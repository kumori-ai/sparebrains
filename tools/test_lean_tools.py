"""tools/lean_tools.py, with mathlib and Lean faked: name lookup ranking, and auto stopping at the
first closer the judge accepts (a Try-this proof is made concrete and judged again).

    python3 tools/test_lean_tools.py
"""
import sys
import unittest
from pathlib import Path
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parent))
import lean_tools as lt

INDEX = {"Nat.Prime.dvd_of_dvd_pow", "dvd_pow", "Int.Prime.dvd_pow", "Nat.Prime.dvd_mul", "Finset.card_le_card"}
TARGET = "import Mathlib\n\ntheorem t (n : ℕ) : n + 0 = n := by\n  sorry\n"


class Names(unittest.TestCase):
    def setUp(self):
        lt._INDEX.clear()
        lt._INDEX.update(names=INDEX, by_last=lt.fixer._by_last(INDEX))

    def test_a_real_name_is_itself(self):
        self.assertEqual(lt.names("dvd_pow"), ["dvd_pow"])

    def test_same_last_part_first_then_close_spellings(self):
        got = lt.names("Nat.Prime.dvd_pow")
        self.assertEqual(got[:2], ["dvd_pow", "Int.Prime.dvd_pow"])
        self.assertIn("Nat.Prime.dvd_of_dvd_pow", got)


class TryThis(unittest.TestCase):
    def test_reads_lean_4_33s_format_and_the_old_one(self):
        self.assertEqual(lt.TRY_THIS.findall("x.lean:4:8: error\nTry this:\n  [apply] exact Nat.lt_of_succ_le h\n"),
                         ["exact Nat.lt_of_succ_le h"])
        self.assertEqual(lt.TRY_THIS.findall("Try this: exact h"), ["exact h"])


class Auto(unittest.TestCase):
    def test_stops_at_the_first_accept_and_makes_try_this_concrete(self):
        seen = []

        def judge(text, timeout=300):
            seen.append(text.rsplit("\n", 2)[-2].strip())
            if seen[-1] == "exact?":
                return {"verdict": "accept", "reason": "", "seconds": 1, "output": "Try this: exact Nat.add_zero n\n"}
            return {"verdict": "accept" if seen[-1].startswith("exact Nat") else "reject", "reason": "", "seconds": 1, "output": ""}
        with mock.patch.object(lt, "judge_text", judge):
            r = lt.auto(TARGET)
        self.assertEqual((r["solved"], r["by"]), (True, "exact Nat.add_zero n"))
        self.assertEqual(seen, ["exact?", "exact Nat.add_zero n"])

    def test_reports_every_closer_when_none_works(self):
        with mock.patch.object(lt, "judge_text", lambda t, timeout=300: {"verdict": "reject", "reason": "", "seconds": 1, "output": ""}):
            r = lt.auto(TARGET)
        self.assertFalse(r["solved"])
        self.assertEqual([x["tactic"] for x in r["tried"]], lt.CLOSERS)


if __name__ == "__main__":
    unittest.main(verbosity=1)
