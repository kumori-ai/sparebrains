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

    def test_an_answer_cut_off_at_the_token_cap_is_not_a_try(self):
        capped = lambda i: {**row("imo_x", sample=i), "inference": {"finish": "length"}}
        rows = [capped(i) for i in range(6)] + [row("imo_x", sample=i) for i in range(6, 8)]
        self.assertEqual([(t["target"], n) for t, n in ls.owed(OPEN[:1], rows)], [("imo_x", 8)], "2 real tries, next sample 8")
        rows = [capped(i) for i in range(ls.MAX_CALLS)]
        self.assertEqual(ls.owed(OPEN[:1], rows), [], "a problem that always runs out stops at MAX_CALLS")


def sse(events):
    """A streamed reply as Mistral sends it: one `data:` line per event, then [DONE]."""
    import io, json
    return io.BytesIO(("".join(f"data: {json.dumps(e)}\n\n" for e in events) + "data: [DONE]\n\n").encode())


class BarAndReach(unittest.TestCase):
    def test_the_bar_joins_only_when_allowed_and_reachable_problems_go_first(self):
        self.assertEqual([t["target"] for t, _ in ls.owed(OPEN, [], bar=True)], ["amc_y", "imo_x", "custom_z"])
        reach = {("minif2f/test", "custom_z")}
        self.assertEqual([t["target"] for t, _ in ls.owed(OPEN, [], reachable=reach)], ["custom_z", "imo_x"])
        self.assertEqual([t["target"] for t, _ in ls.owed(OPEN, [], bar=True, reachable=reach)],
                         ["custom_z", "amc_y", "imo_x"])


class Effort(unittest.TestCase):
    def test_a_problem_that_ran_out_twice_is_asked_without_long_reasoning(self):
        capped = lambda t, i: {**row(t, sample=i), "inference": {"finish": "length"},
                               "request_config": {"max_tokens": ls.MAX_TOKENS}}
        rows = [capped("imo_x", 0), capped("imo_x", 1), capped("custom_z", 0), row("custom_z", sample=1)]
        self.assertEqual(ls.effort_for(rows, ("minif2f/test", "imo_x")), "none")
        self.assertIsNone(ls.effort_for(rows, ("minif2f/test", "custom_z")), "one cap is not enough")
        old = [{**capped("imo_x", i), "request_config": {"max_tokens": 40000}} for i in range(3)]
        self.assertIsNone(ls.effort_for(old, ("minif2f/test", "imo_x")), "cut off under an older, smaller cap")

    def test_the_effort_is_sent_only_when_set_and_kept_in_the_row(self):
        import json
        sent = []

        def fake_urlopen(req, timeout=None):
            sent.append(json.loads(req.data))
            return sse([{"choices": [{"delta": {"content": "x"}, "finish_reason": "stop"}], "usage": {"completion_tokens": 1}}])
        with mock.patch.object(ls.urllib.request, "urlopen", side_effect=fake_urlopen):
            ls.call_prompt("k", "p", ls.Pacer(0))
            ls.call_prompt("k", "p", ls.Pacer(0), effort="none")
        self.assertNotIn("reasoning_effort", sent[0])
        self.assertEqual(sent[1]["reasoning_effort"], "none")


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

    def test_the_stream_keeps_the_text_and_drops_the_thinking(self):
        events = [{"choices": [{"delta": {"content": [{"type": "thinking", "thinking": [{"type": "text", "text": "hmm"}]}]}}]},
                  {"choices": [{"delta": {"content": [{"type": "thinking", "thinking": []}, {"type": "text", "text": "pro"}]}}]},
                  {"choices": [{"delta": {"content": "of"}, "finish_reason": "stop"}], "usage": {"completion_tokens": 7}}]
        with mock.patch.object(ls.urllib.request, "urlopen", return_value=sse(events)):
            r = ls.call("k", "theorem t : True := by\n  sorry", ls.Pacer(0))
        self.assertEqual((r["text"], r["finish"], r["tokens"], r["retried"]), ("proof", "stop", 7, False))

    def test_a_whole_json_reply_still_reads(self):
        import io, json
        body = io.BytesIO(json.dumps({"choices": [{"message": {"content": "proof"}, "finish_reason": "stop"}],
                                      "usage": {"completion_tokens": 7}}, indent=1).encode())
        with mock.patch.object(ls.urllib.request, "urlopen", return_value=body):
            r = ls.call("k", "theorem t : True := by\n  sorry", ls.Pacer(0))
        self.assertEqual((r["text"], r["finish"], r["tokens"]), ("proof", "stop", 7))

    def test_a_dropped_connection_is_retried_once(self):
        import http.client
        ok = lambda: sse([{"choices": [{"delta": {"content": "proof"}, "finish_reason": "stop"}],
                           "usage": {"completion_tokens": 7}}])
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
