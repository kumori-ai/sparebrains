"""Every workflow that builds Lean shares one Mathlib-packages cache: restored before lean-action, saved right after it,
before the judge sandbox or any untrusted Lean, under the build's own condition. lean-action's per-commit cache
(2.4 GB per commit) filled the repo's 10 GB on 2026-11-05 and evicted every other cache, openproblems' data included."""
import unittest
from pathlib import Path

import yaml

WORKFLOWS = Path(__file__).resolve().parent.parent / ".github" / "workflows"


def lean_jobs():
    for f in sorted(WORKFLOWS.glob("*.yml")):
        for name, job in (yaml.safe_load(f.read_text()).get("jobs") or {}).items():
            steps = job.get("steps") or []
            at = [i for i, st in enumerate(steps) if "lean-action" in str(st.get("uses", ""))]
            if at:
                yield f.name, name, steps, at[0]


class LeanCache(unittest.TestCase):
    def test_every_lean_build_is_restore_build_save_with_the_builds_condition(self):
        seen = 0
        for wf, job, steps, i in lean_jobs():
            seen += 1
            where = f"{wf}:{job}"
            restore, lean, save = steps[i - 1], steps[i], steps[i + 1]
            self.assertIn("actions/cache/restore", restore.get("uses", ""), where)
            self.assertIn("actions/cache/save", save.get("uses", ""), where)
            self.assertEqual(lean["with"].get("use-github-cache"), False, f"{where}: lean-action's per-commit cache is off")
            self.assertEqual(restore["with"]["path"], ".lake/packages", where)
            self.assertEqual(save["with"]["path"], ".lake/packages", where)
            self.assertNotIn("github.sha", restore["with"]["key"], f"{where}: one key per Mathlib version, not per commit")
            cond = lean.get("if")
            if cond:                                     # Codex 20261105 f2: a skipped build does no cache work either
                self.assertEqual(restore.get("if"), cond, where)
                self.assertIn(f"({cond})", save.get("if", ""), where)
            before = [st.get("name", "") for st in steps[:i - 1]]
            self.assertFalse(any("sandbox" in n for n in before), f"{where}: the save comes before the judge sandbox")
        self.assertGreaterEqual(seen, 12, "the walk found the Lean workflows (a 0 here would make this test pass on nothing)")


if __name__ == "__main__":
    unittest.main()
