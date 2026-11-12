"""The judge never hands Lean a secret. A fake `lake` (and `sudo`) on PATH prints what it was
given; the real isolation is proved in Actions by tools/judge_isolation_canary.py."""
import os
import stat
import sys
import tempfile
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


class MemoryCap(unittest.TestCase):
    """kumori #683: the cap is measured before it is set (tools/judge_memory_canary.py)."""

    def test_the_lean_command_carries_a_cap_only_when_asked(self):
        with patch.dict(os.environ, {}, clear=False):
            os.environ.pop("SB_JUDGE_USER", None)
            self.assertNotIn("-M", check.lean_cmd("x.lean")[0])
            cmd = check.lean_cmd("x.lean", 4500)[0]
        self.assertEqual(cmd[cmd.index("-M") + 1], "4500")
        self.assertEqual(cmd[-1], "x.lean")

    def test_a_cap_abort_is_told_from_an_ordinary_error(self):
        self.assertTrue(check.capped("libc++abi: terminating due to uncaught exception of type lean::memory_exception: "
                                     "excessive memory consumption detected at 'interpreter'"))
        self.assertFalse(check.capped("x.lean:3:2: error: unsolved goals"))

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

    def test_the_floor_is_the_lowest_cap_a_plain_accept_passes_and_none_when_no_cap_does(self):
        import judge_memory_canary as canary
        tried = []
        def plain(cap):
            tried.append(cap)
            return (0, "", 6100) if cap >= 6500 else (134, "excessive memory consumption", 6072)
        self.assertEqual(canary.floor((5000, 6000, 6500, 7000), plain), (6500, 6100))
        self.assertEqual(tried, [5000, 6000, 6500], "it stops at the first cap that passes")
        self.assertEqual(canary.floor((5000, 6000), plain), (None, None))

    def test_a_plain_accept_that_fails_for_another_reason_is_not_a_floor_reading(self):
        import judge_memory_canary as canary
        with self.assertRaises(SystemExit):
            canary.floor((5000, 6000), lambda cap: (1, "x.lean:3:2: error: unsolved goals", 6000))

    def test_a_runaway_whose_peak_is_no_higher_than_a_plain_accept_was_not_seen_taking_memory(self):
        import judge_memory_canary as canary
        self.assertFalse(canary.blind([7010, 7004, 7100], 6600))
        self.assertTrue(canary.blind([7010, 6650, 7100], 6600), "one runaway stopped before it took anything")
        self.assertTrue(canary.blind([7010, None, 7100], 6600), "a peak that was not read proves nothing")
        self.assertTrue(canary.blind([7010], None))

    def run_canary(self, proof):
        """The canary's whole run on fake Lean: floor 6500, runaways stopped at their cap and seen, proofs as proof(cap, n)."""
        import contextlib, io
        import judge_memory_canary as canary
        n = [0]
        def lean(path, cap, timeout):
            if path == canary.PLAIN:
                return (0, "", 6100) if cap >= 6500 else (134, "excessive memory consumption", 6072)
            if path == canary.PROBE:
                return 134, "excessive memory consumption", cap + 20
            n[0] += 1
            return proof(cap, n[0])
        out, code = io.StringIO(), 0
        with patch.object(canary, "lean", lean), patch.object(canary, "JOBS", 1), contextlib.redirect_stdout(out):
            try:
                canary.main([f"verified/s/p{i:02}/a.lean" for i in range(12)])
            except SystemExit as e:
                code = e.code
        return code, out.getvalue()

    def test_proofs_that_time_out_are_not_proofs_the_cap_kept(self):
        code, out = self.run_canary(lambda cap, n: (None, "", 6200))       # Codex 20261112T230227845584Z f1
        self.assertTrue(code, "it must not exit clean")
        self.assertNotIn("lowest cap that keeps", out)

    def test_a_timeout_is_a_failed_reading_even_when_it_printed_the_cap_message(self):
        import judge_memory_canary as canary                               # Codex 20261112T230620127550Z f1
        late = lambda cap, n: (None, "excessive memory consumption", None) if cap == 7000 else (0, "", 6200)
        code, out = self.run_canary(late)
        self.assertTrue(code)
        self.assertNotIn("lowest cap that keeps", out)
        with self.assertRaises(SystemExit):
            canary.floor((5000, 6000), lambda cap: (None, "excessive memory consumption", None))

    def test_a_cap_is_named_only_after_the_whole_sample_passes_under_it(self):
        code, out = self.run_canary(lambda cap, n: (0, "", 6200))
        self.assertFalse(code)
        self.assertIn("lowest cap that keeps every sampled proof: 7000 (floor 6500 + 500)", out)
        cut_once = lambda cap, n: (134, "excessive memory consumption", 7000) if cap == 7000 and n == 3 else (0, "", 6200)
        code, out = self.run_canary(cut_once)
        self.assertFalse(code)
        self.assertIn("cap 7500: 1 verified proofs, 1 pass", out)
        self.assertIn("cap 7500: 12 verified proofs, 12 pass", out, "the cap is rechecked on the whole sample")
        self.assertIn("lowest cap that keeps every sampled proof: 7500", out)


if __name__ == "__main__":
    unittest.main()
