"""Issue threads, rendered offline from a fixture dossier: what the bot posts and what it never posts."""
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
import problem_issues as pi

D = dict(target_set="mil", target="mil_c05_s01_ex03", rung="mil", rung_label="textbook basics", solved=False,
         answered=114, lanes_tried=40, source="https://github.com/kumori-ai/sparebrains/blob/main/targets/mil/mil_c05_s01_ex03.lean",
         statement=None, failures=[dict(kind="unsolved_goals", n=10, lanes=6)], unknown_names=[["Nat.fake", 2], ["h", 5], ["x.val", 3]],
         near_misses=[dict(id=47348, backend="groq-gptoss", try_mode="relay", failure_kind="unsolved_goals",
                           proof="  intro h", lean_output="/home/runner/w/.lake/attempts/x.lean:4:107: error: unsolved goals")],
         thread=[])


class RenderTests(unittest.TestCase):
    def test_body_opens_with_the_marker_and_carries_the_pack(self):
        title, body = pi.render(D, order=1)
        self.assertTrue(body.startswith("<!-- sparebrains:problem mil/mil_c05_s01_ex03 -->"))
        self.assertIn("number 1 in the", body)
        self.assertIn("Prompt pack", body)
        self.assertIn("theorem mil_c05_s01_ex03", body)          # the statement, read from targets/
        self.assertIn("`Nat.fake`", body)
        self.assertNotIn("`h`", body)                            # a local name is not an invented library name
        self.assertNotIn("x.val", body)
        self.assertNotIn("/home/runner", body)
        self.assertIn("mil_c05_s01_ex03", title)

    def test_reference_proof_never_appears(self):
        ref = (pi.ROOT / "targets/mil/reference/mil_c05_s01_ex03.lean").read_text()
        _, body = pi.render(D)
        proof = ref.split(":= by", 1)[1].strip()
        self.assertNotIn(proof[:60], body)

    def test_a_solved_problem_is_never_rendered(self):
        with self.assertRaises(ValueError):
            pi.render(dict(D, solved=True))


class DigestTests(unittest.TestCase):
    def test_one_comment_per_problem_and_relay_rows_only(self):
        rows = [dict(run_id="9", target_set="mil", target="a", backend="x", attempt_no=1, try_mode="relay", verdict="reject", reason="unsolved goals"),
                dict(run_id="9", target_set="mil", target="a", backend="y", attempt_no=1, try_mode="relay", verdict="accept", reason="ok"),
                dict(run_id="9", target_set="mil", target="b", backend="x", attempt_no=1, try_mode="cold", verdict="reject", reason="cold row"),
                dict(run_id="8", target_set="mil", target="a", backend="z", attempt_no=1, try_mode="relay", verdict="reject", reason="old run")]
        out = dict(pi.digest("9", rows))
        self.assertEqual(list(out), ["mil/a"])
        self.assertIn("2 calls, 2 answers, 1 accepted", out["mil/a"])
        self.assertIn("**Solved.**", out["mil/a"])
        self.assertNotIn("old run", out["mil/a"])


if __name__ == "__main__":
    unittest.main()
