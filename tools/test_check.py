"""The judge never hands Lean a secret. A fake `lake` (and `sudo`) on PATH prints what it was
given; the real isolation is proved in Actions by tools/judge_isolation_canary.py."""
import os
import stat
import sys
import tempfile
import threading
import time
import unittest
from pathlib import Path
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).parent))
import check

FAKE = f"#!{sys.executable}\n" + """import os, sys
print("ARGV", " ".join(sys.argv[1:]))
print("ENV", " ".join(f"{k}={v}" for k, v in sorted(os.environ.items())))
"""


class JudgeEnvTests(unittest.TestCase):
    def setUp(self):
        self.bin = tempfile.mkdtemp()
        for name in ("lake", "sudo"):
            p = Path(self.bin) / name
            p.write_text(FAKE)
            p.chmod(p.stat().st_mode | stat.S_IXUSR)
        self.lean = Path(self.bin) / "demo.lean"
        self.lean.write_text("theorem demo : True := trivial\n")
        self.env = {"PATH": f"{self.bin}:{os.environ['PATH']}", "HOME": os.environ.get("HOME", "/tmp"),
                    "KUMORI_API_KEY": "sbcanary-key-1234", "SB_CANARY": "sbcanary-env-5678"}

    def run_judge(self, extra=None):
        with patch.dict(os.environ, {**self.env, **(extra or {})}, clear=True):
            return check.judge(str(self.lean), 30)[3]

    def test_secrets_never_reach_lean(self):
        out = self.run_judge()
        self.assertIn("ARGV env lean", out)              # the fake really ran
        self.assertNotIn("sbcanary", out)

    def test_judge_user_runs_lean_through_sudo_with_an_empty_env(self):
        out = self.run_judge({"SB_JUDGE_USER": "sbjudge"})
        self.assertIn("ARGV -n -u sbjudge env -i", out)
        self.assertNotIn("sbcanary", out)

    def test_candidate_is_readable_by_the_judge_user(self):
        seen = {}
        real = check.run_lean
        def spy(cmd, *a, **kw):
            seen["mode"] = stat.S_IMODE(os.stat(cmd[-1]).st_mode)
            return real(cmd, *a, **kw)
        with patch.object(check, "run_lean", spy):
            self.run_judge({"SB_JUDGE_USER": "sbjudge"})
        self.assertTrue(seen["mode"] & stat.S_IROTH)


GRANDCHILD = ("import subprocess, sys, time\n"
              "p = subprocess.Popen([sys.executable, '-c', 'import time; time.sleep(120)'])\n"
              "print(p.pid, flush=True)\np.wait()\n")


def alive(pid):
    try:
        os.kill(pid, 0)
    except ProcessLookupError:
        return False
    return True


class RunLeanTests(unittest.TestCase):
    """Run 43142012823 (2026-11-12): five checks timed out and the runner was shut down. `lake env lean` is a parent
    of Lean (and of sudo's in Actions), so killing the process we started left Lean running: locally, 2.96 GB held 6 s
    after judge() returned its timeout, 3.27 GB 20 s later."""

    def test_a_timeout_stops_the_whole_tree_not_only_the_process_we_started(self):
        rc, out, err, peak = check.run_lean([sys.executable, "-c", GRANDCHILD], dict(os.environ), 2)
        self.assertIsNone(rc, "None is a timeout")
        pid = int(out.split()[0])
        self.addCleanup(lambda: alive(pid) and os.kill(pid, 9))
        for _ in range(40):                                    # a killed process takes a moment to go
            if not alive(pid):
                break
            time.sleep(0.05)
        self.assertFalse(alive(pid), "the grandchild outlived the timeout")

    def test_a_finished_check_returns_its_output_and_its_peak_memory(self):
        code = "import sys; b = bytearray(200 * 1024 * 1024); print('out'); print('err', file=sys.stderr); sys.exit(3)"
        rc, out, err, peak = check.run_lean([sys.executable, "-c", code], dict(os.environ), 30)
        self.assertEqual((rc, out, err), (3, "out\n", "err\n"))
        self.assertTrue(200 <= peak < 2000, f"peak {peak} MB for a 200 MB allocation")

    def test_judge_says_timeout_and_how_much_memory_the_last_check_took(self):
        lake = Path(tempfile.mkdtemp()) / "lake"
        lake.write_text(f"#!{sys.executable}\nimport time\ntime.sleep(120)\n")
        lake.chmod(0o755)
        lean = lake.parent / "demo.lean"
        lean.write_text("theorem demo : True := trivial\n")
        with patch.dict(os.environ, {"PATH": f"{lake.parent}:{os.environ['PATH']}"}):
            os.environ.pop("SB_JUDGE_USER", None)
            verdict, reason, secs, _ = check.judge(str(lean), 1)
        self.assertEqual((verdict, reason), ("reject", "timeout after 1s"))
        self.assertIsNone(check.last_peak_mb(), "a killed check has no peak to report")


class RunLeanOutput(unittest.TestCase):
    def test_output_reads_as_subprocess_text_mode_did(self):          # Codex 20261112T200455784944Z q1
        code = "import sys; sys.stdout.buffer.write(b'first\\r\\nsecond\\rthird\\n')"
        self.assertEqual(check.run_lean([sys.executable, "-c", code], dict(os.environ), 30)[1], "first\nsecond\nthird\n")

    def test_a_process_table_that_cannot_be_read_still_stops_the_process_we_started(self):   # f3
        with patch.object(check.subprocess, "run", side_effect=OSError("no ps")):
            rc = check.run_lean([sys.executable, "-c", "import time; time.sleep(120)"], dict(os.environ), 1)[0]
        self.assertIsNone(rc)


class TimeoutCanary(unittest.TestCase):
    """tools/judge_timeout_canary.py is the runner's evidence, so it must not pass blind (Codex f1, f2)."""

    def setUp(self):
        import judge_timeout_canary
        self.canary = judge_timeout_canary

    def table(self, text, code=0):
        return patch.object(self.canary.subprocess, "run",
                            return_value=type("R", (), {"stdout": text, "stderr": "ps failed", "returncode": code})())

    def test_only_lean_itself_counts_never_the_launchers_around_it(self):
        rows = ("11 900 sudo -n -u sbjudge env -i PATH=/x lake env lean -DautoImplicit=false /tmp/p.lean\n"
                "12 800 lake env lean -DautoImplicit=false /tmp/p.lean\n"
                "13 3145728 /home/runner/.elan/toolchains/v4/bin/lean -DautoImplicit=false /tmp/p.lean\n"
                "14 3145728 lean -DautoImplicit=false /tmp/other.lean\n")
        with self.table(rows):
            self.assertEqual(self.canary.leans("/tmp/p.lean"), {13: 3072})
        with self.table(rows.splitlines()[0] + "\n" + rows.splitlines()[1] + "\n"):
            self.assertEqual(self.canary.leans("/tmp/p.lean"), {}, "a launcher stalled before Lean is not Lean")

    def test_an_arm_that_stops_early_still_kills_its_probe(self):                 # Codex 20261112T201242695422Z f4
        killed = []
        def run(cmd, **kw):
            if cmd[0] == "ps":
                return type("R", (), {"stdout": f"77 2048 lean {cmd_file[0]}\n", "stderr": "", "returncode": 0})()
            killed.append(cmd)
        cmd_file = [None]
        def stop(cmd, env, watch):
            cmd_file[0] = cmd[-1]
            raise SystemExit("stopped before the timeout")
        with patch.object(self.canary.subprocess, "run", run), patch.dict(os.environ, {"PATH": os.environ["PATH"]}), \
                patch.object(self.canary, "USER", None), self.assertRaises(SystemExit):
            self.canary.arm("old", stop)
        self.assertEqual(killed, [["kill", "-KILL", "77"]])

    def test_a_process_table_that_cannot_be_read_stops_the_canary(self):
        with self.table("", code=1), self.assertRaises(SystemExit) as e:
            self.canary.leans("/tmp/p.lean")
        self.assertIn("ps failed", str(e.exception))


class MemoryLimit(unittest.TestCase):
    """kumori #683: the limit is measured before it is set (tools/judge_memory_canary.py). Lean's own -M is not it:
    on the runner it printed its message and the runaway ran on (check run 43326406123)."""

    def test_a_named_unit_runs_lean_in_its_own_scope_of_the_judge_slice_as_the_judge_user(self):
        with patch.dict(os.environ, {"SB_JUDGE_USER": "sbjudge", "KUMORI_API_KEY": "sbcanary-key-1234"}):
            plain = check.lean_cmd("x.lean")[0]
            cmd = check.lean_cmd("x.lean", unit="sbjudge-7-1")[0]
        self.assertEqual(plain[:4], ["sudo", "-n", "-u", "sbjudge"], "the judge itself is unchanged")
        head = cmd[:cmd.index("env")]
        self.assertEqual(head[:4], ["sudo", "-n", "systemd-run", "--scope"])
        for want in ("--unit=sbjudge-7-1", "--slice=sbjudge.slice", "--uid=sbjudge", "OOMPolicy=kill"):
            self.assertIn(want, head)
        self.assertEqual(cmd[cmd.index("env"):][:2], ["env", "-i"], "the scope still starts from an empty environment")
        self.assertNotIn("sbcanary", " ".join(cmd))
        self.assertEqual(cmd[-1], "x.lean")
        with patch.dict(os.environ, {}, clear=False):
            os.environ.pop("SB_JUDGE_USER", None)
            self.assertEqual(check.lean_cmd("x.lean", unit="u")[0][0], "lake", "no judge user, no scope")

    def test_the_sample_is_one_proof_per_problem_spread_evenly_and_the_same_every_run(self):
        import judge_memory_canary as canary
        files = [f"verified/s/p{i:03}/{lane}.lean" for i in range(100) for lane in ("b", "a")]
        got = canary.spread(files, 10)
        self.assertEqual(got, [f"verified/s/p{i:03}/a.lean" for i in range(0, 100, 10)])
        self.assertEqual(canary.spread(list(reversed(files)), 10), got)
        self.assertEqual(len(canary.spread(files[:6], 10)), 3)

    def test_free_memory_is_read_from_the_kernel_or_is_none(self):
        import judge_memory_canary as canary
        with tempfile.NamedTemporaryFile("w") as f:
            f.write("MemTotal:       16373692 kB\nMemAvailable:    9541234 kB\n")
            f.flush()
            self.assertEqual(canary.free_mb(f.name), 9317)
        self.assertIsNone(canary.free_mb("/nonexistent/meminfo"))

    LOG = ("[ 10.1] Memory cgroup out of memory: Killed process 4242 (lean) total-vm:9000kB\n"
           "[ 10.1] Tasks in /sbjudge.slice/sbjudge-7-1.scope are going to be killed due to memory.oom.group set\n")

    def test_a_kill_is_the_limits_only_when_the_kernel_log_names_that_checks_scope(self):
        import judge_memory_canary as canary
        self.assertTrue(canary.limit_killed(self.LOG, "sbjudge-7-1"))
        self.assertFalse(canary.limit_killed(self.LOG, "sbjudge-7-2"))
        self.assertFalse(canary.limit_killed(self.LOG, "sbjudge-7-11"), "a longer unit name is another check")
        self.assertEqual(canary.host_kills(self.LOG), 0)
        self.assertEqual(canary.host_kills(self.LOG + "[ 11.0] Out of memory: Killed process 77 (python3)\n"), 1)

    def test_a_proof_met_the_limit_only_if_it_was_running_when_a_runaway_was_killed(self):
        import judge_memory_canary as canary
        runs = [("a", 0, 0.0, 5.0), ("b", 0, 6.0, 9.0), ("c", None, 3.0, 20.0)]
        self.assertEqual([r[0] for r in canary.overlapping(runs, [4.0, 10.0])], ["a", "c"])
        self.assertEqual(canary.overlapping(runs, []), [])

    def run_canary(self, proof=lambda n: (0, "", 6200, 0.0, 1e12), probe_rc=-9, log=True, limits=(8000,)):
        """The canary's whole run on fakes: the slice sets, every runaway ends as probe_rc, proofs as proof(n)."""
        import contextlib, io
        import judge_memory_canary as canary
        n, dmesg = [0], []
        def lean(path, unit, timeout):
            if path == canary.PROBE:
                if log:
                    dmesg.append(f"Tasks in /sbjudge.slice/{unit}.scope are going to be killed due to memory.oom.group set")
                return probe_rc, "", 9000, 1.0, 2.0
            n[0] += 1
            return proof(n[0])
        out, code = io.StringIO(), 0
        with patch.multiple(canary, lean=lean, JOBS=1, LIMITS=limits, MIXED_RUNAWAYS=2, MIN_MET=1, set_limit=lambda mb: None,
                            guard=lambda mb: 6600, settle=lambda: None, kernel_log=lambda: "\n".join(dmesg),
                            charged=lambda: "current 0 MB"), contextlib.redirect_stdout(out):
            try:
                canary.main([f"verified/s/p{i:02}/a.lean" for i in range(12)])
            except SystemExit as e:
                code = e.code
        return code, out.getvalue()

    def test_a_limit_is_named_when_runaways_die_by_it_and_every_proof_passes_beside_them(self):
        code, out = self.run_canary()
        self.assertFalse(code, out)
        self.assertIn("limits that held every arm: [8000]", out)

    def test_proofs_that_time_out_name_no_limit(self):                      # Codex 20261112T230227845584Z f1
        code, out = self.run_canary(lambda n: (None, "", 6200, 0.0, 1e12))
        self.assertTrue(code)
        self.assertNotIn("limits that held", out)

    def test_a_runaway_that_ended_without_the_kernel_log_naming_its_scope_names_no_limit(self):
        code, out = self.run_canary(log=False)                              # Codex 20261112T233227563378Z f2
        self.assertTrue(code)
        self.assertNotIn("limits that held", out)
        code, out = self.run_canary(probe_rc=None)
        self.assertTrue(code, "a runaway still alive at the timeout was not contained")
        self.assertNotIn("limits that held", out)

    def test_proofs_that_never_ran_beside_a_kill_name_no_limit(self):       # Codex 20261112T233227563378Z f3
        code, out = self.run_canary(lambda n: (0, "", 6200, 5.0, 6.0))
        self.assertTrue(code)
        self.assertIn("met the limit", out)
        self.assertNotIn("limits that held", out)

    def test_a_proof_run_that_raised_beside_a_runaway_names_no_limit(self):   # Codex 20261112T233926341418Z f4
        def proof(n):
            if n > 5 and "proofs" in threading.current_thread().name:     # the mixed arm's workers only
                raise OSError("no reading")
            return 0, "", 6200, 0.0, 1e12
        with patch("threading.excepthook", lambda a: None):
            code, out = self.run_canary(proof)
        self.assertTrue(code)
        self.assertIn("OSError", str(code))
        self.assertNotIn("limits that held", out)

    def test_every_limit_is_tried_and_each_that_held_is_listed(self):
        code, out = self.run_canary(limits=(8000, 9000))
        self.assertFalse(code, out)
        self.assertIn("limits that held every arm: [8000, 9000]", out)


if __name__ == "__main__":
    unittest.main()
