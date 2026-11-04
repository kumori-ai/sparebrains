"""tools/prover_pilot.py: the frozen set, every answer judged, resume by answer id, and the frozen read (#480)."""
import json
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
import prover_pilot as pp

NAME = "mathd_algebra_478"


def answer(sample, batch="b1", text=None, target=NAME):
    proof = f"```lean4\ntheorem {target} : True := by\n  trivial\n```"
    return {"batch": batch, "target_set": "minif2f/test", "target": target, "sample": sample, "tokens": 100,
            "seconds": 9.0, "text": text if text is not None else proof, "config": {"model": pp.MODEL}}


class Pilot(unittest.TestCase):
    def setUp(self):
        self.tmp = Path(tempfile.mkdtemp())
        self.man = pp.manifest(out=self.tmp / "manifest.json")
        self.rows = self.tmp / "judged.jsonl"

    def test_the_set_is_six_per_stratum_from_the_named_population_and_frozen(self):
        self.assertEqual(sum(self.man["population"].values()), 160, "math-L3..L5, amc12, aime+imo of miniF2F-test")
        by = {}
        for p in self.man["problems"]:
            by.setdefault(p["stratum"], []).append(p)
        self.assertEqual({s: len(v) for s, v in by.items()}, {s: 6 for s in pp.STRATA})
        self.assertTrue(all(p["rung"] in pp.STRATA[p["stratum"]] for p in self.man["problems"]))
        self.assertEqual(pp.manifest(out=self.tmp / "again.json")["problems"], self.man["problems"], "a fixed seed")
        with self.assertRaises(SystemExit):
            pp.manifest(out=self.tmp / "manifest.json")

    def man_with(self, name=NAME):
        import hashlib
        text = (pp.ROOT / "targets" / "minif2f" / "test" / f"{name}.lean").read_text()
        return {"problems": [{"target_set": "minif2f/test", "target": name, "stratum": "math-L3",
                              "statement_sha": hashlib.sha256(text.encode()).hexdigest()}]}

    def test_every_answer_is_judged_even_after_sample_zero_succeeds(self):
        """Codex f9 on #480: prover.judge_answers stops a problem at its first accept; the pilot must not."""
        calls = []
        judge = lambda text: calls.append(text) or {"verdict": "accept" if len(calls) == 1 else "reject", "output": "err"}
        chain = lambda proof, prefix, said: {"c_verdict": "accept", "final": prefix + proof}
        w = pp.judge([answer(k) for k in range(8)], self.man_with(), [], judge, chain, out=self.rows)
        self.assertEqual(len(w), 8)
        self.assertEqual(len(calls), 8, "all 8 raw verdicts")
        self.assertEqual([r["raw"] for r in w], ["accept"] + ["reject"] * 7)
        self.assertEqual([r["chain"] for r in w], ["accept"] * 8, "the chain runs on raw rejects, raw accepts kept")

    def test_a_rerun_resumes_by_answer_id_and_owes_only_the_missing_slots(self):
        judge = lambda text: {"verdict": "reject", "output": "err"}
        chain = lambda proof, prefix, said: {"c_verdict": "reject"}
        man = self.man_with()
        pp.judge([answer(k) for k in range(5)], man, [], judge, chain, out=self.rows)   # a batch cut by the budget
        done = pp.rows(self.rows)
        self.assertEqual(pp.missing(man, done), {("minif2f/test", NAME): 3})
        again = pp.judge([answer(k) for k in range(5)] + [answer(k, batch="b2") for k in range(3)], man, done, judge, chain,
                         out=self.rows)
        self.assertEqual(len(again), 3, "the 5 already judged are skipped")
        self.assertEqual(pp.missing(man, pp.rows(self.rows)), {})

    def test_a_changed_statement_stops_the_judge(self):
        man = self.man_with()
        man["problems"][0]["statement_sha"] = "0" * 64
        with self.assertRaises(SystemExit):
            pp.judge([answer(0)], man, [], lambda t: {"verdict": "reject"}, lambda *a: {"c_verdict": "reject"}, out=self.rows)

    def test_the_read_is_inconclusive_until_complete_and_claims_at_five_rescues(self):
        probs = [{"target_set": "minif2f/test", "target": f"t{i}", "stratum": "amc12"} for i in range(30)]
        man = {"problems": probs}
        row = lambda t, k, raw, chain: {"batch": "b", "target_set": "minif2f/test", "target": t, "sample": k,
                                        "raw": raw, "chain": chain}
        full = [row(f"t{i}", k, "reject", "accept" if (i < 5 and k == 3) else "reject") for i in range(30) for k in range(8)]
        r = pp.read(man, full)
        self.assertEqual((r["complete"], r["R"], r["absolute_lift"], r["solved_raw"]), (True, 5, round(5 / 30, 4), 0))
        self.assertIn("lifts the 4B", r["read"])
        four = [x for x in full if not (x["target"] == "t4" and x["chain"] == "accept")] + [row("t4", 3, "reject", "reject")]
        self.assertIn("no claim", pp.read(man, four)["read"])
        self.assertIn("inconclusive", pp.read(man, full[:-1])["read"], "one answer short")
        raw_too = [row(x["target"], x["sample"], "accept", "accept") if x["target"] == "t0" else x for x in full]
        self.assertEqual(pp.read(man, raw_too)["R"], 4, "a problem solved raw is no rescue")

    def test_a_deadline_stops_new_judging_and_a_rerun_makes_progress(self):
        """Codex f1: rows land as they are judged; past the deadline nothing new starts; the next run goes on."""
        import time as _t
        man, tick = self.man_with(), [0]

        def clock():                      # a rising clock: every call is a second later
            tick[0] += 1
            return tick[0]
        judge = lambda text: {"verdict": "reject", "output": "err"}
        chain = lambda proof, prefix, said: {"c_verdict": "reject"}
        from unittest import mock
        with mock.patch.object(pp.time, "monotonic", clock):
            w = pp.judge([answer(k) for k in range(8)], man, [], judge, chain, out=self.rows, deadline=12)
        self.assertLess(len(w), 8)
        self.assertEqual(len(pp.rows(self.rows)), len(w), "every judged row is already on disk")
        more = pp.judge([answer(k) for k in range(8)], man, pp.rows(self.rows), judge, chain, out=self.rows)
        self.assertEqual(len(w) + len(more), 8)

    def test_the_ledger_record_of_pushes_decides_what_may_be_replaced(self):
        """Codex 2026-11-04, three rounds on #480: Kaggle's reply cannot tell a missing kernel from a denied one, so
        the accounting reads only the ledger's record of pushes."""
        import gzip
        store = lambda b: self.tmp / f"answers-{b}.jsonl.gz"
        pushes = self.tmp / "pushes.jsonl"
        self.assertIsNone(pp.accounted([], [], store), "nothing pushed yet: a first push")
        pp.record_push("pilot4b-x", path=pushes)
        self.assertIn("not in the ledger", pp.accounted(pp.rows(pushes), [], store), "pushed, never judged: blocked")
        with gzip.open(store("pilot4b-x"), "wt") as f:
            f.writelines(json.dumps(answer(k, batch="pilot4b-x")) + "\n" for k in range(3))
        self.assertIn("3 answers not judged", pp.accounted(pp.rows(pushes), [], store))
        done = [{"batch": "pilot4b-x", "target": NAME, "sample": k} for k in range(3)]
        self.assertIsNone(pp.accounted(pp.rows(pushes), done, store))
        pp.record_push("pilot4b-y", path=pushes)
        self.assertIn("pilot4b-y", pp.accounted(pp.rows(pushes), done, store))
        pp.record_push("pilot4b-y", void="kaggle kernels push exit 1", path=pushes)
        self.assertIsNone(pp.accounted(pp.rows(pushes), done, store), "a void push owes nothing")
        with self.assertRaises(SystemExit):
            pp.record_push("pilot4b-y", path=pushes)              # Codex f1: an id is pushed once, never reused
        with self.assertRaises(SystemExit):
            pp.record_push("pilot4b-y", void="again", path=pushes)
        with self.assertRaises(SystemExit):
            pp.record_push("pilot4b-z", void="never pushed", path=pushes)

    def test_duplicate_records_of_one_answer_count_once_and_a_conflict_is_inconclusive(self):
        """Codex f3: five distinct answers and their copies are not eight."""
        man = {"problems": [{"target_set": "minif2f/test", "target": "t0", "stratum": "amc12"}]}
        row = lambda k, raw="reject", secs=1: {"batch": "b", "target_set": "minif2f/test", "target": "t0", "sample": k,
                                               "raw": raw, "chain": raw, "gen_seconds": secs}
        five = [row(k) for k in range(5)] + [row(k, secs=2) for k in range(3)]
        self.assertEqual((pp.read(man, five)["complete"], pp.read(man, five)["answers"]), (False, 5))
        self.assertEqual(pp.read(man, five)["gen_seconds"], 5.0, "Codex f4: costs count each answer once")
        clash = [row(k) for k in range(8)] + [row(0, raw="accept")]
        self.assertIn("conflicting", pp.read(man, clash)["read"])

    def test_the_kernel_runs_the_4b_under_its_own_kaggle_id_for_the_owed_slots(self):
        man = self.man_with()
        d = self.tmp / "k"
        n, samples = pp.build(d, man, [], "pilot4b-test", 5.0)
        meta = json.loads((d / "kernel-metadata.json").read_text())
        src = (d / "prover_kernel.py").read_text()
        self.assertEqual((n, samples, meta["id"]), (1, 8, pp.KERNEL_ID))
        self.assertIn(f'MODEL = "{pp.MODEL}"', src)
        self.assertIn('"n": 8', src)


if __name__ == "__main__":
    unittest.main()
