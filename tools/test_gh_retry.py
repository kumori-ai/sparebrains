"""gh_retry.sh: reads retried through GitHub's 5xx, dispatches never re-sent. Offline: a scripted command, no gh."""
from pathlib import Path
import re
import subprocess
import os
import tempfile
import time
import unittest

import yaml

ROOT = Path(__file__).resolve().parent.parent
HELPER = ROOT / 'tools' / 'gh_retry.sh'


def run(failures):
    """gh_retry over a command that fails `failures` times then prints ok; sleep stubbed out."""
    with tempfile.TemporaryDirectory() as d:
        count = Path(d) / 'n'
        count.write_text(str(failures))
        flaky = f'n=$(cat {count}); echo $((n-1)) > {count}; [ "$n" -le 0 ] && {{ echo ok; exit 0; }}; echo 500 >&2; exit 1'
        script = f'sleep() {{ :; }}; . {HELPER}; out=$(gh_retry sh -c \'{flaky}\'); echo "got=$out"; echo after'
        r = subprocess.run(['bash', '-e', '-o', 'pipefail', '-c', script], capture_output=True, text=True, timeout=30)
        return r.returncode, r.stdout


class GhRetryTests(unittest.TestCase):
    def test_a_read_recovers_on_the_third_try_with_clean_output(self):
        self.assertEqual(run(2), (0, 'got=ok\nafter\n'))

    def test_a_read_that_keeps_failing_stops_the_step(self):
        code, out = run(3)
        self.assertNotEqual(code, 0)
        self.assertNotIn('after', out)

    def test_dispatches_are_never_retried_and_reads_in_attempt_are(self):
        for wf in (ROOT / '.github' / 'workflows').glob('*.yml'):
            found = re.findall(r'gh_retry\s+gh\s+workflow\s+run.*', wf.read_text())
            self.assertEqual(found, [], f'{wf.name}: a re-sent dispatch can cancel queued work')
        attempt = (ROOT / '.github' / 'workflows' / 'attempt.yml').read_text()
        self.assertEqual(re.findall(r'(?<!gh_retry )gh run list', attempt), [])



def stub_bin(d, gh_body):
    gh = Path(d) / 'gh'
    gh.write_text('#!/bin/bash\n' + gh_body)
    gh.chmod(0o755)
    date = Path(d) / 'date'   # the script uses GNU date -d; a fixed instant keeps the test off the host's date
    date.write_text('#!/bin/sh\nif [ "$1" = +%s ]; then exec /bin/date +%s; fi\necho 2026-11-04T00:00:00Z\n')
    date.chmod(0o755)
    return {**os.environ, 'PATH': f'{d}:{os.environ["PATH"]}', 'GITHUB_REPOSITORY': 'o/r', 'GITHUB_RUN_ID': '1'}


def lane_step(fail_on, queued=0):
    """tools/start_dropped_lanes.sh as attempt.yml runs it (no bash -e from outside), gh stubbed: reads for
    fail_on always fail; sleep is a no-op so retries are instant."""
    with tempfile.TemporaryDirectory() as d:
        (Path(d) / 'sleep').write_text('#!/bin/sh\n'); (Path(d) / 'sleep').chmod(0o755)
        env = stub_bin(d, f'''if [ "$1 $2" = "workflow run" ]; then echo "DISPATCH $3"; exit 0; fi
[ "$4" = "{fail_on}" ] && {{ echo "HTTP 500" >&2; exit 1; }}
case "$*" in *createdAt*) echo "";; *) echo {queued};; esac
''')
        r = subprocess.run([str(ROOT / 'tools' / 'start_dropped_lanes.sh')], cwd=ROOT, env=env,
                           capture_output=True, text=True, timeout=60)
        return r.returncode, r.stdout


def heartbeat(open_jobs, tick_body, poll_s=1, tick_s=0, max_unreadable=3, timeout=30):
    """tools/lanes_heartbeat.sh with gh answering the job count from a file the test controls."""
    with tempfile.TemporaryDirectory() as d:
        state = Path(d) / 'open'
        state.write_text(open_jobs)
        env = stub_bin(d, f'v=$(cat {state}); [ "$v" = x ] && exit 1; echo "$v"\n')
        tick = Path(d) / 'tick.sh'
        tick.write_text(tick_body.replace('STATE', str(state)).replace('DIR', d))
        env.update(TICK_CMD=str(tick), POLL_S=str(poll_s), TICK_S=str(tick_s), MAX_UNREADABLE=str(max_unreadable))
        t0 = time.monotonic()
        r = subprocess.run([str(ROOT / 'tools' / 'lanes_heartbeat.sh')], env=env, capture_output=True,
                           text=True, timeout=timeout)
        ticks = len(list(Path(d).glob('ticked*')))
        return r.returncode, r.stdout, time.monotonic() - t0, ticks


class LaneStepTests(unittest.TestCase):
    def test_an_unreadable_queue_in_the_leanstral_group_stops_every_dispatch(self):
        for g in ('leanstral.yml', 'decompose.yml', 'headtohead.yml'):
            code, out = lane_step(g)
            self.assertNotEqual(code, 0, g)
            self.assertNotIn('DISPATCH', out, g)

    def test_readable_empty_queues_start_both_lanes(self):
        code, out = lane_step('none')
        self.assertEqual(code, 0)
        self.assertIn('DISPATCH prover.yml', out)
        self.assertIn('DISPATCH leanstral.yml', out)

    def test_a_waiting_run_keeps_leanstral_back(self):
        code, out = lane_step('none', queued=1)
        self.assertEqual(code, 0)
        self.assertNotIn('DISPATCH leanstral.yml', out)


class HeartbeatTests(unittest.TestCase):
    def test_a_slow_tick_never_delays_the_end(self):
        # the tick sleeps 60 s (a gh_retry backoff); the ladder job finishes at once: out within a couple of polls
        # the tick starts, the ladder job finishes during it, and the tick goes on sleeping 60 s (a gh_retry backoff):
        # the heartbeat must still end within a couple of polls and take the tick's whole process group with it
        mark = f'67.{os.getpid()}'   # this run's own sleep: a concurrent run of this test elsewhere never matches
        code, out, took, ticks = heartbeat('1', f'touch DIR/ticked; echo 0 > STATE; sleep {mark}; touch DIR/ticked_late\n')
        self.assertEqual(code, 0)
        self.assertIn('heartbeat ends', out)
        self.assertLess(took, 10)
        self.assertEqual(ticks, 1)
        time.sleep(1)
        found = subprocess.run(["pgrep", "-f", f"sleep {mark}$"], capture_output=True, text=True)
        if found.returncode not in (0, 1):   # pgrep: 0 match, 1 none, else it could not look (Codex f4, sandboxes)
            self.skipTest(f'cannot list processes: {found.stderr.strip()}')
        self.assertEqual(found.returncode, 1, f'orphaned tick: {found.stdout}')

    def test_ticks_repeat_while_the_ladder_runs_and_a_failed_tick_does_not_stop_them(self):
        body = 'n=$(ls DIR | grep -c ticked); touch DIR/ticked$n; [ "$n" -ge 2 ] && echo 0 > STATE; exit 1\n'
        code, out, took, ticks = heartbeat('1', body)
        self.assertEqual(code, 0)
        self.assertGreaterEqual(ticks, 3)
        self.assertIn('lane tick failed', out)

    def test_an_unreadable_status_stops_the_heartbeat_instead_of_holding_the_chain(self):
        code, out, took, _ = heartbeat('x', 'touch DIR/ticked\n', max_unreadable=3)
        self.assertEqual(code, 0)
        self.assertIn('status unreadable', out)
        self.assertLess(took, 10)

    def test_the_relay_step_and_the_ladder_heartbeat_use_the_one_script(self):
        wf = yaml.safe_load((ROOT / '.github' / 'workflows' / 'attempt.yml').read_text())
        steps = wf['jobs']['attempt']['steps']
        relay = next(st for st in steps if st.get('name', '').startswith('start the two-hourly lanes'))
        self.assertEqual(relay['run'], 'tools/start_dropped_lanes.sh')
        lanes = wf['jobs']['lanes']
        self.assertEqual(lanes['permissions'], {'actions': 'write', 'contents': 'read'})
        self.assertIn('tools/lanes_heartbeat.sh', [st.get('run') for st in lanes['steps']])
        for f in ('leanstral.yml', 'headtohead.yml'):
            c = yaml.safe_load((ROOT / '.github' / 'workflows' / f).read_text())['concurrency']
            self.assertEqual((c['group'], c.get('queue')), ('leanstral', 'max'), f)

if __name__ == '__main__':
    unittest.main()
