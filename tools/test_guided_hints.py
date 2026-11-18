"""Paired lemma-name hints: treatment separation and missing data, without GPU or Lean."""
import copy
import unittest

import guided_hints as hints


def work():
    return [{"target_set": "test", "target": "demo", "n": 2,
             "statement": "import Mathlib\ntheorem sb_goal : True := by\n  sorry\n",
             "guided": {"manifest": "pilot", "path": [1, 3], "hole": hole, "n": 2}}
            for hole in (2, 3)]


NAMES = {"test/demo:1.3.2": ["Nat.prime_def"], "test/demo:1.3.3": ["Nat.Prime.divisors"]}


class Pairing(unittest.TestCase):
    def test_manifest_requires_frozen_inputs_and_explicit_budget(self):
        man = {"problems": ["test/demo"], "blueprint": {"path": "bp.json", "sha256": "a" * 64},
               "target_sha256": {"test/demo": "b" * 64}, "samples_per_hole": 2,
               "generation": {"model": "fixture", "revision": "c" * 40}}
        hints.validate_manifest(man, 2)
        for field in ("blueprint", "target_sha256", "samples_per_hole", "generation"):
            bad = copy.deepcopy(man)
            del bad[field]
            with self.subTest(field=field), self.assertRaises(ValueError):
                hints.validate_manifest(bad, 2)
        with self.assertRaises(ValueError):
            hints.validate_manifest(man, 3)
        del man["blueprint"]["sha256"]
        with self.assertRaises(ValueError):
            hints.validate_manifest(man, 2)

    def test_uniform_wrong_snapshot_is_refused_before_judging(self):
        paired = hints.paired_work(work(), NAMES)
        for p in paired:
            p["guided"]["generation"] = {"model": "fixture", "revision": "a" * 40}
        answers = self.answers(paired)
        with self.assertRaisesRegex(ValueError, "frozen model revision"):
            hints.judge(paired, answers, lambda t: self.fail("must not judge drifted snapshot"), lambda t: t)
        for answer in answers:
            answer["config"]["revision"] = "a" * 40
        rows, _ = hints.judge(paired, answers, lambda t: {"verdict": "reject"}, lambda t: "  fail\n")
        self.assertTrue(all(row["complete"] for row in rows))

    def test_pair_order_balances_and_only_hint_comment_changes_statement(self):
        original = work()
        paired = hints.paired_work(original, NAMES)
        self.assertEqual([p["guided"]["hint_arm"] for p in paired], ["unhinted", "hinted", "hinted", "unhinted"])
        for left, right in zip(paired[::2], paired[1::2]):
            self.assertEqual(left["guided"]["statement_sha"], right["guided"]["statement_sha"])
            self.assertEqual(left["guided"]["hint_sha"], right["guided"]["hint_sha"])
            plain = next(p for p in (left, right) if p["guided"]["hint_arm"] == "unhinted")
            hinted = next(p for p in (left, right) if p["guided"]["hint_arm"] == "hinted")
            self.assertEqual(hinted["statement"].split("\n", 1)[1], plain["statement"])
        self.assertEqual(original, work(), "source statements must stay untouched")

    def test_missing_extra_and_code_shaped_hints_are_refused(self):
        for names in ({}, {**NAMES, "other:1": ["Nat.prime_def"]},
                      {**NAMES, "test/demo:1.3.2": ["Nat.prime_def\nby exact True.intro"]}):
            with self.assertRaises(ValueError):
                hints.paired_work(work(), names)

    def answers(self, paired):
        return [{"target_set": p["target_set"], "target": p["target"], "sample": k,
                 "guided": copy.deepcopy(p["guided"]), "text": p["guided"]["hint_arm"],
                 "config": {"model": "fixture", "revision": "frozen"}}
                for p in paired for k in range(p["n"])]

    def test_only_hinted_arm_closes_and_no_proof_text_reaches_public_rows(self):
        paired = hints.paired_work(work(), NAMES)
        seen = []
        def judge(text):
            seen.append(text)
            return {"verdict": "accept" if "exact True.intro" in text else "reject", "reason": ""}
        rows, held = hints.judge(paired, self.answers(paired), judge,
                                lambda text: "  exact True.intro\n" if text == "hinted" else "  fail\n")
        self.assertEqual(len(seen), 8, "judge all samples, even after the first accept")
        self.assertEqual([r["complete"] for r in rows], [True, True])
        self.assertTrue(all(r["arms"]["hinted"]["pass_at_n"] for r in rows))
        self.assertFalse(any(r["arms"]["unhinted"]["pass_at_n"] for r in rows))
        self.assertNotIn("exact True.intro", str(rows))
        self.assertEqual(len(held), 4)

    def test_missing_arm_is_incomplete_even_if_the_other_arm_passed(self):
        paired = hints.paired_work(work(), NAMES)
        answers = [a for a in self.answers(paired) if a["guided"]["hint_arm"] == "hinted"]
        rows, _ = hints.judge(paired, answers, lambda t: {"verdict": "accept"}, lambda t: "  trivial\n")
        self.assertFalse(any(r["complete"] for r in rows))
        self.assertTrue(all(r["arms"]["unhinted"]["pass_at_n"] is None for r in rows))

    def test_duplicates_wrong_provenance_and_model_drift_refuse_all_judging(self):
        paired = hints.paired_work(work(), NAMES)
        for defect in ("duplicate", "metadata", "config", "sample"):
            answers = self.answers(paired)
            if defect == "duplicate":
                answers.append(answers[0])
            elif defect == "metadata":
                answers[0]["guided"]["hint_sha"] = "changed"
            elif defect == "config":
                answers[0]["config"]["revision"] = "changed"
            else:
                answers[0]["sample"] = 99
            with self.subTest(defect=defect), self.assertRaises(ValueError):
                hints.judge(paired, answers, lambda t: self.fail("must validate before judging"), lambda t: t)

    def test_unfinished_judge_is_not_a_failed_comparison(self):
        paired = hints.paired_work(work(), NAMES)
        rows, _ = hints.judge(paired, self.answers(paired),
                              lambda t: {"verdict": "reject", "reason": "timeout after 300s"},
                              lambda t: "  trivial\n")
        self.assertFalse(any(r["complete"] for r in rows))
        self.assertTrue(all(r["arms"]["hinted"]["pass_at_n"] is None for r in rows))


if __name__ == "__main__":
    unittest.main()
