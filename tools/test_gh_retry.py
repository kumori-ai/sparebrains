"""gh_retry.sh: reads retried through GitHub's 5xx, dispatches never re-sent. Offline: a scripted command, no gh."""
from pathlib import Path
import re
import subprocess
import os
import tempfile
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



def lane_step(fail_on, queued=0):
    """The real 'start the two-hourly lanes' step body, with gh stubbed: reads for fail_on always fail."""
    steps = yaml.safe_load((ROOT / '.github' / 'workflows' / 'attempt.yml').read_text())['jobs']['attempt']['steps']
    body = next(st['run'] for st in steps if st.get('name', '').startswith('start the two-hourly lanes'))
    with tempfile.TemporaryDirectory() as d:
        gh = Path(d) / 'gh'
        gh.write_text(f'''#!/bin/bash
if [ "$1 $2" = "workflow run" ]; then echo "DISPATCH $3"; exit 0; fi
[ "$4" = "{fail_on}" ] && {{ echo "HTTP 500" >&2; exit 1; }}
case "$*" in *createdAt*) echo "";; *) echo {queued};; esac
''')
        gh.chmod(0o755)
        date = Path(d) / 'date'   # the step uses GNU date -d; a fixed instant keeps the test off the host's date
        date.write_text('#!/bin/sh\necho 2026-11-04T00:00:00Z\n')
        date.chmod(0o755)
        env = {**os.environ, 'PATH': f'{d}:{os.environ["PATH"]}', 'GITHUB_REPOSITORY': 'o/r'}
        r = subprocess.run(['bash', '-e', '-c', 'sleep() { :; }; ' + body], cwd=ROOT, env=env,
                           capture_output=True, text=True, timeout=60)
        return r.returncode, r.stdout


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

if __name__ == '__main__':
    unittest.main()
