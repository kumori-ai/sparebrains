"""The Leanstral lane (tools/leanstral.py): which problems are owed a try, the proof read out of Leanstral's parts,
and a 429 stopping the round instead of hammering. No network: the API call is faked."""
import sys
import unittest
from pathlib import Path
from unittest import mock

sys.path.insert(0, str(Path(__file__).parent))
import leanstral as ls

OPEN = [dict(target_set="minif2f/test", target="imo_x", rung="imo", order=2),
        dict(target_set="minif2f/test", target="amc_y", rung="amc12", order=1),     # the prover's 50: never here
        dict(target_set="minif2f/test", target="custom_z", rung="custom", order=3)]


def row(target, verdict="reject", sample=0, mode="leanstral"):
    return dict(target_set="minif2f/test", target=target, verdict=verdict, try_mode=mode, sample_no=sample, batch="b")


class Owed(unittest.TestCase):
    def test_outside_the_bar_unsolved_and_with_tries_left(self):
        self.assertEqual([(t["target"], n) for t, n in ls.owed(OPEN, [])], [("imo_x", 0), ("custom_z", 0)])
        rows = [row("imo_x", sample=i) for i in range(ls.TRIES)] + [row("custom_z", sample=0)]
        self.assertEqual([(t["target"], n) for t, n in ls.owed(OPEN, rows)], [("custom_z", 1)])
        self.assertEqual(ls.owed(OPEN, [row("custom_z", "accept"), *[row("imo_x", sample=i) for i in range(8)]]), [])


class Answers(unittest.TestCase):
    def test_the_proof_is_in_the_text_parts_not_the_thinking(self):
        parts = [{"type": "thinking", "thinking": [{"type": "text", "text": "let me think"}]},
                 {"type": "text", "text": "```lean4\ntheorem t : True := trivial\n```"}]
        self.assertEqual(ls.text_of(parts), "```lean4\ntheorem t : True := trivial\n```")
        self.assertEqual(ls.text_of("plain"), "plain")

    def test_a_429_stops_the_round(self):
        import urllib.error, io
        err = urllib.error.HTTPError(ls.API, 429, "slow down", {}, io.BytesIO(b"rate limited"))
        pacer = ls.Pacer(0)
        with mock.patch.object(ls.urllib.request, "urlopen", side_effect=err) as calls:
            with self.assertRaises(RuntimeError):
                ls.call("k", "theorem t : True := by\n  sorry", pacer)
            with self.assertRaises(RuntimeError):
                ls.call("k", "theorem t : True := by\n  sorry", pacer)
        self.assertEqual(pacer.stop, "HTTP 429")
        self.assertEqual(calls.call_count, 1)                 # the second call never reached Mistral

    def test_a_dropped_connection_is_retried_once(self):
        import http.client, io, json
        ok = lambda: io.BytesIO(json.dumps({"choices": [{"message": {"content": "proof"}, "finish_reason": "stop"}],
                                            "usage": {"completion_tokens": 7}}).encode())
        drop = http.client.RemoteDisconnected("Remote end closed connection without response")
        with mock.patch.object(ls.urllib.request, "urlopen", side_effect=[drop, ok()]) as calls:
            r = ls.call("k", "theorem t : True := by\n  sorry", ls.Pacer(0))
        self.assertEqual((r["text"], r["retried"], calls.call_count), ("proof", True, 2))
        with mock.patch.object(ls.urllib.request, "urlopen", side_effect=[drop, drop, ok()]) as calls:
            with self.assertRaises(http.client.RemoteDisconnected):
                ls.call("k", "theorem t : True := by\n  sorry", ls.Pacer(0))
        self.assertEqual(calls.call_count, 2)                 # once, never a loop

    def test_an_empty_reply_says_why(self):
        self.assertEqual(ls.reply({"text": "proof", "finish": "stop", "tokens": 9}), "proof")
        self.assertEqual(ls.reply({"text": "  ", "finish": "length", "tokens": 40000}),
                         {"error": "empty reply (finish=length, 40000 tokens)"})


if __name__ == "__main__":
    unittest.main()
