"""The Kaggle head-to-head (tools/kaggle_h2h.py): the skeleton pilot generated on Kaggle's GPUs from the open
Ministral 3 3B checkpoint, judged here, raw. Codex 20261108T161803773335Z f1-f4 and 20261108T162104656262Z f5-f6: every
sample has an identity, a target is paired only when all its samples are present and judged, a trimmed batch is
incomplete, nothing is repaired, the lane is the checkpoint's own."""
import json, sys, unittest
from pathlib import Path
from unittest import mock

sys.path[:0] = [str(Path(__file__).resolve().parent)]
import headtohead as h, kaggle_h2h as k

ROOT = Path(__file__).resolve().parent.parent
TARGET = "import Mathlib\n\nopen Real\n\ntheorem t1 (x : ℝ) (h : 0 < x) : 0 < x ^ 2 := by\n  sorry\n"


def answer(body, name="t1"):
    return f"```lean4\ntheorem {name} (x : ℝ) (h : 0 < x) : 0 < x ^ 2 := by\n{body}```"


MAN = {"id": "m", "kind": "exploratory pilot", "lane": k.LANE, "transport": "kaggle", "arms": ["alone", "skeleton"],
       "calls": 16, "max_tokens": 1024, "temperature": 0.6, "top_p": 0.95, "cohort": "c",
       "schedule": [[a, b] for a, b in h.schedule()], "claim": "none",
       "checkpoint": "mistralai/Ministral-3-3B-Instruct-2512-BF16", "revision": "b6d637bef2393152b3da2b2fde72eecdee30557e"}
COHORT = [{"target_set": "s", "target": "t1", "rung": "aime", "status": "solved"},
          {"target_set": "s", "target": "t2", "rung": "aime", "status": "solved"}]
read = lambda s, t: TARGET.replace("t1", t)


def full(ex, text=lambda e: answer("  nlinarith\n", e["target"])):
    return [{"id": e["id"], "prompt_sha": e["prompt_sha"], "text": text(e), "tokens": 9, "finish": "stop", "seconds": 1.0}
            for e in ex]


class Identity(unittest.TestCase):
    def test_every_sample_has_its_own_id_and_the_set_is_cohort_by_arm_by_index(self):
        ex = k.expected(MAN, COHORT, read)
        self.assertEqual(len(ex), 2 * 2 * 16)
        self.assertEqual(len({e["id"] for e in ex}), len(ex))
        self.assertEqual(ex[0]["id"], "m/s/t1/alone/0")
        sk = [e for e in ex if e["arm"] == "skeleton" and e["target"] == "t1"]
        self.assertIn("```lean4\nsimp\n```", sk[1]["prompt"])               # index i carries schedule entry i
        self.assertIn("Hint: Start by simplifying", sk[15]["prompt"])
        al = [e for e in ex if e["arm"] == "alone" and e["target"] == "t1"]
        self.assertTrue(all("must begin" not in e["prompt"] for e in al))

    def test_the_smoke_is_two_targets_two_arms_two_samples(self):
        self.assertEqual(len(k.expected(MAN, COHORT * 3, read, smoke=True)), 8)

    def test_the_manifest_is_refused_without_the_papers_schedule_or_a_pinned_revision(self):
        self.assertEqual(k.check(MAN)["lane"], k.LANE)
        with self.assertRaises(AssertionError):
            k.check({**MAN, "schedule": MAN["schedule"][::-1]})
        with self.assertRaises(AssertionError):
            k.check({**MAN, "revision": "main"})
        with self.assertRaises(AssertionError):
            k.check({**MAN, "lane": "mistral-ministral-3b-2512"})      # never the router lane's series

    def test_the_kernel_is_filled_with_the_items_and_the_pinned_model(self):
        import tempfile
        ex = k.expected(MAN, COHORT, read, smoke=True)
        d = Path(tempfile.mkdtemp())
        k.build(d, MAN, ex, "b1", budget_s=3600, sec_per_sample=2.0)
        src = (d / "kaggle_h2h_kernel.py").read_text()
        self.assertIn('"m/s/t1/alone/0"', src)
        self.assertIn(MAN["revision"], src)
        self.assertIn("You are an expert in Lean 4", src)                 # attempt.SYSTEM, the ladder's
        meta = json.loads((d / "kernel-metadata.json").read_text())
        self.assertEqual((meta["id"], meta["code_file"]), (k.KERNEL_ID, "kaggle_h2h_kernel.py"))
        compile(src, "kernel", "exec")


class Ingest(unittest.TestCase):
    def setUp(self):
        self.ex = k.expected(MAN, COHORT, read)

    def test_a_complete_batch_has_no_voids(self):
        valid, void = k.ingest(full(self.ex), self.ex)
        self.assertEqual((len(valid), void), (64, []))

    def test_duplicate_unknown_and_mismatched_samples_are_void_and_named(self):
        ans = full(self.ex)
        ans.append(dict(ans[0]))                                            # duplicate
        ans.append({**ans[1], "id": "m/s/t9/alone/0"})                       # unknown
        ans[2] = {**ans[2], "prompt_sha": "0" * 64}                          # mismatch
        valid, void = k.ingest(ans, self.ex)
        why = {v["id"]: v["void"] for v in void}
        self.assertEqual(why[ans[0]["id"]], "duplicate")
        self.assertEqual(why["m/s/t9/alone/0"], "unknown")
        self.assertEqual(why[ans[2]["id"]], "prompt_sha")
        self.assertNotIn(ans[0]["id"], valid)
        self.assertNotIn(ans[2]["id"], valid)

    def test_an_alone_sample_never_fills_a_skeleton_id(self):
        ans = [a for a in full(self.ex) if not a["id"].endswith("/skeleton/3")]
        stray = next(a for a in ans if a["id"] == "m/s/t1/alone/3")
        ans.append({**stray, "id": "m/s/t1/skeleton/3"})                    # the alone prompt's sha under a skeleton id
        valid, void = k.ingest(ans, self.ex)
        self.assertNotIn("m/s/t1/skeleton/3", valid)
        self.assertIn("m/s/t1/skeleton/3", {v["id"] for v in void})


class Judge(unittest.TestCase):
    def setUp(self):
        self.ex = k.expected(MAN, COHORT, read)

    def judge(self, answers):
        valid, void = k.ingest(answers, self.ex)
        samples = k.judge(valid, self.ex, read, lambda t: {"verdict": "accept" if "positivity" in t else "reject"})
        return k.targets(samples, self.ex, void)

    def test_every_sample_is_judged_and_the_first_accept_index_is_recorded(self):
        text = lambda e: answer("  simp\n  positivity\n" if e["arm"] == "skeleton" and e["index"] >= 4 else "  nlinarith\n", e["target"])
        rows = self.judge(full(self.ex, text))
        by = {(r["target"], r["arm"]): r for r in rows}
        sk = by[("t1", "skeleton")]
        self.assertEqual((sk["outcome"], sk["first_accept_index"], sk["generated"], sk["judged"]), ("solved", 4, 16, 16))
        self.assertEqual(sk["accepts"], 12)
        self.assertEqual(by[("t1", "alone")]["outcome"], "failed")
        self.assertIn("skeleton_followed", sk)
        s = k.report(rows, MAN, self.ex, [])
        self.assertEqual((s["only_skeleton"], s["complete"], s["samples_expected"], s["samples_present"]),
                         (["t1", "t2"], True, 64, 64))

    def test_a_truncated_batch_is_incomplete_and_the_short_target_is_void_in_both_arms(self):
        ans = [a for a in full(self.ex) if a["id"] != "m/s/t2/alone/15"]   # the kernel's budget trimmed one sample
        rows = self.judge(ans)
        voided = {(r["target"], r["arm"]) for r in rows if r.get("void")}
        self.assertEqual(voided, {("t2", "alone"), ("t2", "skeleton")})
        s = k.report(rows, MAN, self.ex, [])
        self.assertEqual((s["complete"], s["problems_paired"], s["samples_present"]), (False, 1, 63))

    def test_a_rejected_proof_is_never_repaired(self):
        import fixer
        with mock.patch.object(fixer, "fix", side_effect=AssertionError("repair ran")):
            self.judge(full(self.ex))                                       # every sample rejected, none repaired

    def test_rows_are_filed_under_the_checkpoints_lane(self):
        rows = self.judge(full(self.ex))
        self.assertTrue(all(r["writer"] == k.LANE for r in rows))
        self.assertEqual(k.LANE, "kaggle-ministral-3-3b-instruct-2512")


if __name__ == "__main__":
    unittest.main()
