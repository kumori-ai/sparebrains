"""tools/daily_brief.py: the top of the daily report says what changed, against the prior week of reports: wins,
losses, what to fix, ideas, each with its numbers, plus a headline and preheader for kumori's mail. No network.
Fixture numbers are 2026-11-05's report and the seven before it."""
import copy
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
import daily_brief

LANE = lambda n, a, ans: {"lane": n, "accepts": a, "answered": ans}
TODAY = {"day": "2026-11-05", "first_solves": [],
         "totals": {"accepted": 213, "answered": 774, "judged": 1102, "solved_ever": 338, "open": 40,
                    "errors": {"upstream timeout (504)": 200, "router 5xx": 127, "other error": 1},
                    "recovered": {"attempted": 318, "answers": 1, "accepted": 0, "failed": 317}},
         "grades": [{"grade": "kindergarten", "open": 0, "lanes": [LANE("flint", 22, 24), LANE("qwen", 13, 14)]},
                    {"grade": "high school", "open": 40, "lanes": [LANE("flint", 27, 43), LANE("leanstral", 15, 39)]}],
         "speed": [{"lane": "ministral-8b", "size_b": 8, "week": "2026-11-02", "targets": 18, "accepted": 1, "refused": 90,
                    "prev_week": "2026-10-26", "prev_targets": 44, "prev_accepted": 15},
                   {"lane": "agnes", "size_b": None, "week": "2026-11-02", "targets": 17, "accepted": 11, "refused": 70,
                    "prev_week": "2026-10-26", "prev_targets": 26, "prev_accepted": 12}],
         "kaggle": {"finished": [{"batch": "b1", "answers": 56}], "failed": []},
         "rungs": [{"rung": "competition math (ladder)", "idle_days": 0.1}, {"rung": "goal-closer", "idle_days": 14.9},
                   {"rung": "formal-conjectures", "idle_days": 3.1, "accepts_ever": 0},
                   {"rung": "openproblems.bio", "idle_days": 0.3, "scored": 144, "crashed": 138}]}
# (day, accepted, answered, judged, lost) for 10-29..11-04: rates 21 24 23 22 19 29 15, median 22%; lost 23..34%
PRIOR = [("2026-10-29", 153, 745, 965, 220), ("2026-10-30", 230, 955, 1282, 327), ("2026-10-31", 201, 876, 1196, 320),
         ("2026-11-01", 148, 677, 993, 316), ("2026-11-02", 124, 644, 903, 259), ("2026-11-03", 104, 364, 549, 185),
         ("2026-11-04", 72, 483, 654, 171)]
HISTORY = [{"day": d, "totals": {"accepted": a, "answered": n, "judged": j, "solved_ever": 338, "errors": {"x": e}},
            "speed": [{"lane": "ministral-8b", "week": "2026-11-02"}]} for d, a, n, j, e in PRIOR]


def brief(today=None, history=HISTORY):
    return daily_brief.brief(today or TODAY, history)


class Brief(unittest.TestCase):
    def test_accept_rate_is_read_against_the_weeks_median(self):
        b = brief()
        self.assertTrue(any("28%" in w and "22%" in w for w in b["wins"]), b["wins"])

    def test_a_low_rate_day_is_a_loss_not_a_win(self):
        t = copy.deepcopy(TODAY)
        t["totals"]["accepted"] = 100                         # 13% against a 22% median
        b = brief(t)
        self.assertFalse(any("accept rate" in w for w in b["wins"]))
        self.assertTrue(any("accept rate" in l and "13%" in l for l in b["losses"]), b["losses"])

    def test_a_rate_inside_the_band_is_neither(self):
        t = copy.deepcopy(TODAY)
        t["totals"]["accepted"] = 178                         # 23%, one point off the median
        b = brief(t)
        self.assertFalse(any("accept rate" in x for x in b["wins"] + b["losses"]))

    def test_chronic_loss_before_the_kernel_is_a_fix_with_its_streak(self):
        b = brief()
        fix = [f for f in b["fixes"] if "before the kernel" in f]
        self.assertEqual(len(fix), 1, b["fixes"])
        self.assertIn("328 of 1102 (30%)", fix[0])
        self.assertIn("at least 8 days running", fix[0])      # today plus all seven loaded, every one >= 20%

    def test_a_clean_day_has_no_loss_fix(self):
        t = copy.deepcopy(TODAY)
        t["totals"]["errors"] = {"router 5xx": 3}
        self.assertFalse(any("before the kernel" in f for f in brief(t)["fixes"]))

    def test_a_rescue_that_saves_almost_nothing_is_a_fix(self):
        self.assertTrue(any("1 of 318 (0.3%)" in f for f in brief()["fixes"]), brief()["fixes"])

    def test_idle_and_crashing_rungs_are_fixes(self):
        fixes = " | ".join(brief()["fixes"])
        self.assertIn("goal-closer", fixes)
        self.assertIn("14.9", fixes)
        self.assertIn("138 crashed beside 144 scored (49% of rounds)", fixes)   # disjoint sets in rungs(): errors vs rmse rows
        self.assertNotIn("competition math", fixes)           # 0.1 days idle is running

    def test_lift_regression_is_a_loss_and_refusals_become_an_idea(self):
        b = brief()
        self.assertTrue(any("ministral-8b" in l and "34%" in l and "6%" in l for l in b["losses"]), b["losses"])
        self.assertTrue(any("ministral-8b (90 refusals, 18 targets)" in i for i in b["ideas"]), b["ideas"])

    def test_refusing_lanes_share_one_idea_line(self):
        t = copy.deepcopy(TODAY)
        t["speed"].append(dict(t["speed"][0], lane="ministral-14b"))
        ideas = [i for i in brief(t)["ideas"] if "Refusals" in i]
        self.assertEqual(len(ideas), 1, ideas)
        self.assertIn("ministral-14b", ideas[0])

    def test_most_accepts_is_summed_across_grades_and_beats_a_small_perfect_lane(self):
        self.assertTrue(any("flint" in w and "49/67" in w for w in brief()["wins"]), brief()["wins"])

    def test_first_solves_lead_the_headline(self):
        t = copy.deepcopy(TODAY)
        t["first_solves"] = [{"key": "imo_1960_p2", "lane": "flint"}]
        b = brief(t)
        self.assertTrue(b["headline"].startswith("1 first-time solve"), b["headline"])
        self.assertTrue(any("imo_1960_p2" in w for w in b["wins"]))

    def test_headline_carries_the_rate_and_the_worst_problem_and_stays_short(self):
        h = brief()["headline"]
        self.assertTrue(h.startswith("0 new solves"), h)
        self.assertIn("28%", h)
        self.assertIn("30% lost", h)
        self.assertLessEqual(len(h), 70, h)

    def test_a_failed_kaggle_batch_outranks_the_loss_line(self):
        t = copy.deepcopy(TODAY)
        t["kaggle"]["failed"] = [{"batch": "b2"}]
        b = brief(t)
        self.assertIn("Kaggle", b["headline"])
        self.assertTrue(any("b2" in f for f in b["fixes"]))

    def test_preheader_carries_the_steady_numbers(self):
        p = brief()["preheader"]
        for s in ("213/774", "338 solved ever", "40 open"):
            self.assertIn(s, p)

    def test_no_history_says_so_instead_of_inventing_a_baseline(self):
        b = brief(history=[])
        self.assertFalse(any("median" in x for x in b["wins"] + b["losses"]))
        self.assertIn("no earlier reports", b["preheader"])

    def test_headline_stays_inside_the_bound_on_every_combination(self):   # Codex f1: 72 chars got through
        import itertools
        for n_first, rate, kaggle, ladder in itertools.product((0, 2, 12), (100, 178, 213), (False, True), (0.1, 3.4)):
            t = copy.deepcopy(TODAY)
            t["first_solves"] = [{"key": f"k{i}", "lane": "flint"} for i in range(n_first)]
            t["totals"]["accepted"] = rate
            t["kaggle"]["failed"] = [{"batch": "b2"}] if kaggle else []
            t["rungs"][0]["idle_days"] = ladder
            h = brief(t)["headline"]
            self.assertLessEqual(len(h), daily_brief.HEADLINE_MAX, h)
            self.assertTrue(h.startswith(f"{n_first} first-time" if n_first else "0 new solves"), h)

    def test_a_lane_newly_regressed_midweek_reaches_the_headline(self):   # Codex f2: the week-id gate hid it
        hist = copy.deepcopy(HISTORY)
        hist[-1]["speed"] = [dict(TODAY["speed"][0], targets=6, accepted=1)]   # same week, too small to compare yesterday
        t = copy.deepcopy(TODAY)
        t["totals"]["errors"] = {"router 5xx": 3}                # the loss line outranks lift; take it away
        self.assertIn("lift down", brief(t, hist)["headline"])

    def test_a_regression_already_reported_stays_out_of_the_headline(self):
        hist = copy.deepcopy(HISTORY)
        hist[-1]["speed"] = [TODAY["speed"][0]]
        t = copy.deepcopy(TODAY)
        t["totals"]["errors"] = {"router 5xx": 3}
        self.assertNotIn("lift down", brief(t, hist)["headline"])
        self.assertTrue(any("ministral-8b" in l for l in brief(history=hist)["losses"]))

    def test_streak_is_calendar_days_and_says_at_least_when_history_runs_out(self):   # Codex f3
        t = dict(copy.deepcopy(TODAY), day="2026-11-05")
        self.assertIn("at least 8 days running", " ".join(brief(t)["fixes"]))
        short = " ".join(brief(history=HISTORY[-2:])["fixes"])                   # Codex r2 f3: short history is a lower bound too
        self.assertIn("at least 3 days running", short)
        gap = [h for h in HISTORY if h["day"] != "2026-11-02"]                   # a missing report ends the streak
        fix = [f for f in brief(history=gap)["fixes"] if "before the kernel" in f][0]
        self.assertIn("3 days running", fix)                  # 11-03, 11-04, 11-05
        self.assertNotIn("at least", fix)

    def test_markdown_puts_the_brief_first(self):
        md = daily_brief.render(brief())
        self.assertTrue(md.index("**Wins**") < md.index("**Fix**") < md.index("**Ideas**"))


if __name__ == "__main__":
    unittest.main()
