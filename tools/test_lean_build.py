"""lean-build (.github/actions/lean-build): the network steps (elan + toolchain, the Mathlib cache) are retried with
backoff, `lake build` runs once (2026-11-08: a GitHub releases 504 failed attempt 42466336624 and tactics 42470456174;
WarpBuild's retry guidance read 2026-11-08: retry what talks to a machine you do not control, never a compile error).
Codex 20261108T160100530734Z: no timeout-minutes in composite steps, lean by its absolute path, keep the manifest guard."""
import os, subprocess, tempfile, unittest
from pathlib import Path

import yaml

ACTION = Path(__file__).resolve().parent.parent / ".github" / "actions" / "lean-build"
RETRY = ACTION / "retry.sh"


def retry(script, waits="0 0 0", limit="30"):
    """Run retry.sh on a bash snippet that counts its own attempts in a file; (exit code, attempts, output)."""
    d = tempfile.mkdtemp()
    count = Path(d) / "n"
    count.write_text("0")
    cmd = f'n=$(( $(cat {count}) + 1 )); echo $n > {count}; {script}'
    p = subprocess.run(["bash", str(RETRY), limit, "bash", "-c", cmd], capture_output=True, text=True,
                       env={**os.environ, "RETRY_WAITS": waits})
    return p.returncode, int(count.read_text()), p.stdout + p.stderr


class Retry(unittest.TestCase):
    def test_a_transient_failure_recovers_on_a_later_attempt(self):
        rc, n, out = retry('[ "$n" -ge 3 ]')
        self.assertEqual((rc, n), (0, 3), out)
        self.assertIn("attempt 2 of 4 failed", out)

    def test_a_permanent_failure_stops_after_four_attempts_and_fails(self):
        rc, n, out = retry("exit 7")
        self.assertEqual((rc, n), (7, 4), out)
        self.assertIn("::error::", out)

    def test_success_first_time_is_one_attempt(self):
        rc, n, _ = retry("true")
        self.assertEqual((rc, n), (0, 1))

    def test_the_default_waits_are_15_30_60(self):
        self.assertIn('RETRY_WAITS:-15 30 60', RETRY.read_text())


class Action(unittest.TestCase):
    def setUp(self):
        self.steps = yaml.safe_load((ACTION / "action.yml").read_text())["runs"]["steps"]

    def test_lake_build_runs_once_unretried_and_last(self):
        runs = [s.get("run", "") for s in self.steps]
        builds = [r for r in runs if "lake\" build" in r or "lake build" in r]
        self.assertEqual(len(builds), 1, runs)
        self.assertNotIn("retry.sh", builds[0])
        self.assertIs(runs[-1], builds[0])

    def test_the_network_steps_are_retried(self):
        runs = " ".join(s.get("run", "") for s in self.steps)
        self.assertIn('retry.sh" 900 bash "$GITHUB_ACTION_PATH/install_elan.sh"', runs)
        self.assertIn('retry.sh" 1800 "$HOME/.elan/bin/lake" exe cache get', runs)

    def test_no_composite_step_uses_timeout_minutes_or_lean_action(self):
        for s in self.steps:
            self.assertNotIn("timeout-minutes", s, s)          # not in the runner's composite schema (2.338.2)
            self.assertNotIn("lean-action", str(s.get("uses", "")), s)

    def test_lean_is_called_by_its_absolute_path_in_the_install(self):
        text = (ACTION / "install_elan.sh").read_text()
        self.assertIn('"$HOME/.elan/bin/lean" --version', text)
        self.assertNotIn("\nlean --version", text)

    def test_a_missing_manifest_is_refused_before_any_build(self):
        guard = next(s["run"] for s in self.steps if "lake-manifest.json" in s.get("run", ""))
        d = tempfile.mkdtemp()
        self.assertNotEqual(subprocess.run(["bash", "-c", guard], cwd=d, capture_output=True).returncode, 0)
        Path(d, "lake-manifest.json").write_text("{}")
        self.assertEqual(subprocess.run(["bash", "-c", guard], cwd=d, capture_output=True).returncode, 0)


if __name__ == "__main__":
    unittest.main()
