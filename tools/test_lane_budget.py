"""tools/lane_budget.py: a batch is checked against the router's daily cap and backoff before its first call."""
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
import lane_budget as lb

# The router as read 2026-11-03 22:09 UTC (llm_usage, llm_backoff_state), cut to four lanes
USAGE = {"backends": {
    "meganova-mistral-small-3-2-24b-instruct-2506": {"cap": 50, "enabled": True, "remaining": 1, "used": 49},
    "groq-qwen3-8-27b": {"cap": 900, "enabled": True, "remaining": 837, "used": 63},
    "llm7-mistral-small-3-2": {"cap": 300, "enabled": True, "remaining": 299, "used": 1},
    "mistral-mistral-small-2506": {"cap": 150, "enabled": False, "remaining": 149, "used": 1}}}
BACKOFF = {"meganova-mistral-small-3-2-24b-instruct-2506": {"backed_off": True, "reason": "rate_limit", "remaining_sec": 6663},
           "groq-qwen3-8-27b": {"backed_off": False}}


class LaneBudget(unittest.TestCase):
    def setUp(self):
        self.room = lb.headroom(USAGE, BACKOFF)

    def test_run_41725608251_would_have_been_refused(self):
        why = lb.why_not("meganova-mistral-small-3-2-24b-instruct-2506", 240, self.room)
        self.assertIn("backoff", why)
        self.room["meganova-mistral-small-3-2-24b-instruct-2506"]["backed_off"] = False
        self.assertIn("1 of 50 calls left today; 240 needed", lb.why_not("meganova-mistral-small-3-2-24b-instruct-2506", 240, self.room))

    def test_a_batch_takes_at_most_its_share_of_what_is_left(self):
        self.assertIsNone(lb.why_not("groq-qwen3-8-27b", 240, self.room))
        self.assertIsNone(lb.why_not("groq-qwen3-8-27b", 418, self.room))
        self.assertIn("at most 418 (50%)", lb.why_not("groq-qwen3-8-27b", 419, self.room))

    def test_disabled_unknown_and_uncapped_lanes_are_refused_with_the_reason(self):
        self.assertIn("disabled", lb.why_not("mistral-mistral-small-2506", 1, self.room))
        self.assertIn("not in the router's usage table", lb.why_not("nope", 1, self.room))
        room = lb.headroom({"backends": {"x": {"cap": None, "enabled": True, "remaining": None}}}, {})
        self.assertIn("no daily cap", lb.why_not("x", 1, room))

    def test_roomy_lists_the_lanes_that_fit_most_room_first(self):
        self.assertEqual(lb.roomy(100, self.room), ["groq-qwen3-8-27b", "llm7-mistral-small-3-2"])
        self.assertEqual(lb.roomy(200, self.room), ["groq-qwen3-8-27b"])

    def test_preflight_stops_before_any_call_and_names_the_alternatives(self):
        with self.assertRaises(SystemExit) as e:
            lb.preflight("meganova-mistral-small-3-2-24b-instruct-2506", 240, lambda: USAGE, lambda: BACKOFF)
        self.assertIn("Lanes with room for 240 today: groq-qwen3-8-27b", str(e.exception))
        lb.preflight("groq-qwen3-8-27b", 240, lambda: USAGE, lambda: BACKOFF)      # fits: no exit

    def test_alternatives_are_chat_lanes_only(self):
        self.assertEqual(lb.roomy(100, self.room, among={"llm7-mistral-small-3-2"}), ["llm7-mistral-small-3-2"])
        with self.assertRaises(SystemExit) as e:
            lb.preflight("meganova-mistral-small-3-2-24b-instruct-2506", 100, lambda: USAGE, lambda: BACKOFF,
                         catalog_fn=lambda: [{"name": "llm7-mistral-small-3-2"}])
        self.assertIn("today: llm7-mistral-small-3-2", str(e.exception))


if __name__ == "__main__":
    unittest.main()
