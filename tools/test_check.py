"""The judge never hands Lean a secret. A fake `lake` (and `sudo`) on PATH prints what it was
given; the real isolation is proved in Actions by tools/judge_isolation_canary.py."""
import os
import stat
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).parent))
import check

FAKE = """#!/usr/bin/env python3
import os, sys
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
        real = check.subprocess.run
        def spy(cmd, **kw):
            seen["mode"] = stat.S_IMODE(os.stat(cmd[-1]).st_mode)
            return real(cmd, **kw)
        with patch.object(check.subprocess, "run", spy):
            self.run_judge({"SB_JUDGE_USER": "sbjudge"})
        self.assertTrue(seen["mode"] & stat.S_IROTH)


if __name__ == "__main__":
    unittest.main()
