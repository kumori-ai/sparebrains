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

    def test_a_stream_past_its_deadline_stops_with_what_it_has(self):
        """#642: decompose run 42531165741 waited 3,600 s on each of 7 Leanstral streams that never finished (thinking
        chunks kept the 1,200 s socket timeout from firing); the slowest answer on record took 2,399 s."""
        events = [{"choices": [{"delta": {"content": "pro"}}]}, {"choices": [{"delta": {"content": "of"}, "finish_reason": "stop"}]}]
        with mock.patch.object(ls.time, "monotonic", side_effect=iter([0] + [ls.CALL_DEADLINE_S + 1] * 50)):
            r = ls.read_stream(sse(events), deadline=ls.CALL_DEADLINE_S)
        self.assertEqual((r["text"], r["finish"]), ("pro", "deadline"))
        self.assertGreaterEqual(ls.CALL_DEADLINE_S, 2400)

    def test_a_blocked_read_is_ended_at_the_deadline_and_not_retried(self):
        """Codex f1 (20261109T023458450389Z): a deadline checked only between lines cannot end a read that blocks."""
        import threading
        gate = threading.Event()

        class Blocked:
            def __init__(self): self.n = 0
            def __enter__(self): return self
            def __exit__(self, *a): return False
            def __iter__(self): return self
            def __next__(self):
                self.n += 1
                if self.n == 1:
                    return b'data: {"choices": [{"delta": {"content": "pro"}}]}'
                gate.wait(5)                                   # blocks until close() releases it
                raise ValueError("I/O operation on closed file")
            def close(self): gate.set()
        calls = mock.Mock(side_effect=lambda req, timeout=None: Blocked())
        with mock.patch.object(ls, "CALL_DEADLINE_S", 0.2), mock.patch.object(ls.urllib.request, "urlopen", calls):
            t = ls.time.monotonic()
            r = ls.call_prompt("k", "p", ls.Pacer(0))
        self.assertLess(ls.time.monotonic() - t, 2)
        self.assertEqual((r["text"], r["finish"], calls.call_count), ("pro", "deadline", 1))

    def test_a_real_socket_held_open_returns_at_the_deadline(self):
        """Codex f1 round 2 (20261109T024528060534Z): a peer that sends one line and holds the connection open."""
        import http.server, threading
        hold = threading.Event()

        class H(http.server.BaseHTTPRequestHandler):
            def do_POST(self):
                self.rfile.read(int(self.headers["Content-Length"]))
                self.send_response(200)
                self.send_header("Content-Type", "text/event-stream")
                self.end_headers()
                self.wfile.write(b'data: {"choices": [{"delta": {"content": "pro"}}]}\n\n')
                self.wfile.flush()
                hold.wait(10)                                  # keep the socket open, send nothing
            def log_message(self, *a): pass
        srv = http.server.ThreadingHTTPServer(("127.0.0.1", 0), H)
        threading.Thread(target=srv.serve_forever, daemon=True).start()
        try:
            real = ls.urllib.request.urlopen                  # the socket's own timeout held at 10 s, as 1,200 s is live
            with mock.patch.object(ls, "CALL_DEADLINE_S", 0.5), \
                 mock.patch.object(ls.urllib.request, "urlopen", lambda req, timeout=None: real(req, timeout=10)), \
                 mock.patch.object(ls, "API", f"http://127.0.0.1:{srv.server_address[1]}/v1/chat/completions"):
                t = ls.time.monotonic()
                r = ls.call_prompt("k", "p", ls.Pacer(0))
                took = ls.time.monotonic() - t
        finally:
            hold.set()
            srv.shutdown()
        self.assertLess(took, 2, f"returned after {took:.2f} s")
        self.assertEqual((r["text"], r["finish"]), ("pro", "deadline"))
        self.assertIn("finish=deadline", ls.reply(r)["error"], "a cut reply is not an answer")

    def test_no_retry_after_the_deadline(self):
        def urlopen(req, timeout=None):
            raise TimeoutError("read timed out")
        calls = mock.Mock(side_effect=urlopen)
        with mock.patch.object(ls, "CALL_DEADLINE_S", 0), mock.patch.object(ls.urllib.request, "urlopen", calls):
            with self.assertRaises(TimeoutError):
                ls.call_prompt("k", "p", ls.Pacer(0))
        self.assertEqual(calls.call_count, 1, "a dropped connection past the deadline is not asked again")

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
