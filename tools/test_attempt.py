"""Small parser contract tests. Lean remains the end-to-end verifier in Actions."""
import sys
import unittest
from unittest.mock import Mock, patch
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
from attempt import extract_proof
import attempt


class ExtractProofTests(unittest.TestCase):
    def test_recovers_bare_by_block(self):
        self.assertEqual(extract_proof("by\n  norm_num\n", "demo"), "  norm_num\n")
        # fenced, its own `by` dropped: the target already ends in `:= by` (74 double-by rejects to 2026-10-08)
        self.assertEqual(extract_proof("```lean\nby\n  norm_num\n```", "demo"), "  norm_num\n")
        self.assertEqual(extract_proof("```lean\n  norm_num\n```", "demo"), "  norm_num\n")

    def test_does_not_mine_by_from_prose(self):
        self.assertIsNone(extract_proof("Here is a proof: by\n  norm_num\n", "demo"))

    def test_keeps_fenced_full_file_behavior(self):
        reply = "```lean\nimport Mathlib\n\ntheorem demo : 2 + 2 = 4 := by\n  norm_num\n```"
        self.assertEqual(extract_proof(reply, "demo"), "  norm_num\n")


class LaneMetadataTests(unittest.TestCase):
    def test_runtime_flag_and_provenance_survive_roster(self):
        row = dict(name='groq-test', provider='groq', model='gpt-oss-test',
                   quality_tier='high', is_reasoning_model=True,
                   reasoning_sources=['endpoint.is_reasoning'], lifecycle_status='revived')
        with patch.object(attempt, 'llm_backends', return_value=[row]):
            known, unknown = attempt.lanes('')
        self.assertFalse(unknown)
        self.assertEqual(known[0]['capability']['reasoning_sources'], ['endpoint.is_reasoning'])
        self.assertTrue(known[0]['capability']['is_reasoning_model'])

    def test_explicit_lane_cannot_bypass_missing_canonical_state(self):
        with patch.object(attempt, 'llm_backends', return_value=[]):
            with self.assertRaisesRegex(ValueError, 'absent'):
                attempt.lanes('unknown-nvidia')

    def test_a_lane_sparebrains_paused_is_never_asked_even_by_name(self):
        """The pause list is a mechanism, not a lane: groq-qwen3-8-27b sat in it 2026-10-23..28 (kumori-45, then
        reopened on kumori #316); the mechanism is tested with a stand-in and the list is empty today."""
        rows = [dict(name='lane-x', provider='p', model='m', quality_tier='high'),
                dict(name='groq-gptoss', provider='groq', model='openai/gpt-oss-120b', quality_tier='high')]
        with patch.object(attempt, 'llm_backends', return_value=rows), \
                patch.dict(attempt.PAUSED_LANES, {'lane-x': 'test'}, clear=True):
            known, unknown = attempt.lanes('')
            self.assertEqual([l['backend'] for l in known + unknown], ['groq-gptoss'])
            known, unknown = attempt.lanes('lane-x')
            self.assertEqual(known + unknown, [])
        self.assertEqual(attempt.PAUSED_LANES, {})
        self.assertTrue(attempt.is_never_fits(attempt.KumoriAPIError('x', status_code=429, payload={'error_code': 'request_too_large'})))
        self.assertFalse(attempt.is_never_fits(attempt.KumoriAPIError('x', status_code=429, payload={'error_code': 'rate_limited'})))

    def test_paused_lane_is_not_tested(self):
        with patch.object(attempt, 'llm_backends', return_value=[
                dict(name='test', model='test', lifecycle_status='paused')]):
            self.assertEqual(attempt.lanes(''), ([], []))


class RetryPacingTests(unittest.TestCase):
    def runner(self):
        import ast, threading
        from collections import defaultdict
        from types import SimpleNamespace
        from unittest.mock import Mock, MagicMock
        tree = ast.parse(Path(attempt.__file__).read_text())
        node = next(n for n in ast.walk(tree) if isinstance(n, ast.FunctionDef) and n.name == 'run_one')
        target_dir = MagicMock()
        target_dir.__truediv__.return_value.read_text.return_value = 'theorem demo : True := by sorry'
        env = dict(vars(attempt), target_set='test', tdir=target_dir, lock=threading.Lock(),
                   provider_lock=defaultdict(threading.Lock), bench={'streak': {}, 'told': {}, 'gone': set()},
                   per_target=defaultdict(lambda: defaultdict(int)), per_lane=defaultdict(lambda: defaultdict(int)),
                   base_row=Mock(return_value={}), record=Mock(), memory={}, solved={}, names=[],
                   planned_per_target=1, previous_id=Mock(return_value=None),
                   benched=Mock(return_value=False), llm_chat=Mock(),
                   args=SimpleNamespace(max_tokens=256, call_timeout=60, max_calls=99, stop_on_accept=False),
                   state={'calls': 0, 'errors': 0, 'accepts': 0, 'waits': 0}, exhausted={}, too_big={}, cut_cells=set(), fit_cap={}, skip=Mock(),
                   order=[{'backend': 'test-lane', 'provider': 'test'}, {'backend': 'test-sibling', 'provider': 'test'},
                          {'backend': 'other-lane', 'provider': 'other'}],
                   extract_proof=Mock(side_effect=RuntimeError('verifier boundary')))
        env['sent_tokens'] = lambda lane: min(attempt.lane_max_tokens(lane, env['args'].max_tokens),
                                              env['fit_cap'].get(lane['backend'], 10 ** 9))
        exec(compile(ast.Module(body=[node], type_ignores=[]), attempt.__file__, 'exec'), env)
        return env, {'backend': 'test-lane', 'provider': 'test', 'tier': 'high'}

    def test_waiting_worker_rechecks_bench_before_request(self):
        env,lane = self.runner(); env['benched'].return_value = True
        self.assertEqual(env['run_one']('demo', lane, 1), 'defer')
        env['llm_chat'].assert_not_called()

    def test_repeated_refusals_extend_wait_and_do_not_count_as_attempts(self):
        env,lane = self.runner()
        env['llm_chat'].side_effect = attempt.KumoriAPIError('test-lane is benched', status_code=503, retry_after=120)
        with patch.object(attempt.time, 'monotonic', return_value=1000):
            for wait in [120,240,480,960,1800,1800]:
                self.assertEqual(env['run_one']('demo', lane, 1), 'defer')
                self.assertEqual(env['bench']['told']['test-lane'], 1000+wait)
        self.assertEqual(env['state']['calls'], 0)

    def test_a_pacing_refusal_parks_the_lane_for_the_routers_window_and_is_no_try(self):
        """2026-11-01: 106 of one day's 353 pre-kernel errors were groq-qwen3-8-27b's "is pacing to the provider limit
        (tokens:batch_day_sp...)", kumori's daily-budget refusal with retry_after_s set, scored here as lost tries
        (kumori-96, kumori #316: re-asking inside the window cannot succeed)."""
        env, lane = self.runner()
        env['llm_chat'].side_effect = attempt.KumoriAPIError(
            'kumori /api/v1/llm/chat HTTP 503 : test-lane is pacing to the provider limit (tokens:batch_day_sp 1,000,000); retry in 5400s',
            status_code=503, retry_after=5400)
        with patch.object(attempt.time, 'monotonic', return_value=1000):
            self.assertEqual(env['run_one']('demo', lane, 1), 'defer')
            self.assertEqual(env['bench']['told']['test-lane'], 1000 + 5400, "parked exactly as long as the router says")
        self.assertEqual((env['state']['calls'], env['bench']['streak'].get('test-lane')), (0, 1), "no try spent, one refusal counted")

    def test_real_response_resets_refusal_streak_before_verification(self):
        env,lane = self.runner();env['bench']['streak']['test-lane'] = 5
        env['llm_chat'].return_value = ('answer','test-lane',{})
        with self.assertRaisesRegex(RuntimeError,'verifier boundary'):
            env['run_one']('demo',lane,1)
        self.assertNotIn('test-lane',env['bench']['streak'])

    def test_server_longer_minimum_is_never_shortened(self):
        self.assertEqual(attempt.bench_delay(7200, 20),7200)
        self.assertEqual(attempt.bench_delay(None, 1),60)


class DeadLaneTests(RetryPacingTests):
    """2026-09-20, run 35481806786: one lane's upstream died, the router demoted it, and the job
    asked it 1,702 more times. The three-error rule then closed 250 cells it was never asked about."""

    def test_router_404_drops_the_lane_for_the_job_and_is_not_held_against_the_cell(self):
        env, lane = self.runner()
        env['llm_chat'].side_effect = attempt.KumoriAPIError(
            'kumori /api/v1/llm/chat HTTP 404 : unknown backend: test-lane', status_code=404)
        self.assertEqual(env['run_one']('demo', lane, 1), 'error_router')
        self.assertIn('test-lane', env['bench']['gone'])

    def test_a_reasoning_cut_returns_error_cut(self):
        env, lane = self.runner()
        env['llm_chat'].side_effect = attempt.KumoriAPIError(
            'kumori /api/v1/llm/chat HTTP 503 [reasoning_truncated] : backend test-lane returned no text', status_code=503)
        self.assertEqual(env['run_one']('demo', lane, 1), 'error_cut')
        calls = env['llm_chat'].call_count
        # Codex 20261109T162517332095Z f1: the cell's later try, queued before the cut (or waiting on the provider
        # lock), makes no call; another cell still does
        self.assertEqual(env['run_one']('demo', lane, 2), 'error_cut')
        self.assertEqual(env['llm_chat'].call_count, calls, "no call for a cut cell")
        env['run_one']('other', lane, 1)
        self.assertEqual(env['llm_chat'].call_count, calls + 1, "an unrelated cell is still asked")

    def test_a_worker_waiting_on_the_provider_lock_sees_the_cut(self):
        """Codex round 2: two workers on one cell; the first is held at record() after its cut, so the provider lock
        is already released. The second must make no call and write no row."""
        import threading
        env, lane = self.runner()
        env['llm_chat'].side_effect = attempt.KumoriAPIError(
            'kumori /api/v1/llm/chat HTTP 503 [reasoning_truncated] : backend test-lane returned no text', status_code=503)
        held, go = threading.Event(), threading.Event()
        def record(*a, **k):
            if not held.is_set():
                held.set()
                go.wait(5)
        env['record'].side_effect = record
        out = {}
        t1 = threading.Thread(target=lambda: out.__setitem__(1, env['run_one']('demo', lane, 1)))
        t1.start()
        held.wait(5)                                       # the first worker is past the lock, inside record()
        out[2] = env['run_one']('demo', lane, 2)
        go.set(); t1.join(5)
        self.assertEqual((out[1], out[2]), ('error_cut', 'error_cut'))
        self.assertEqual((env['llm_chat'].call_count, env['record'].call_count), (1, 1), "one call, one row")

    def test_failures_in_a_row_park_the_lane_with_growing_waits(self):
        env, lane = self.runner()
        env['llm_chat'].side_effect = attempt.KumoriAPIError('kumori /api/v1/llm/chat HTTP 502 : unknown', status_code=502)
        with patch.object(attempt.time, 'monotonic', return_value=1000):
            for n, parked_until in [(1, None), (2, None), (3, 1060), (4, 1120), (5, 1240)]:
                self.assertEqual(env['run_one']('demo', lane, 1), 'error_router')
                self.assertEqual(env['bench']['told'].get('test-lane'), parked_until, f'after failure {n}')

    def share_refusal(self, reason, retry_after):
        return attempt.KumoriAPIError(
            f"kumori /api/v1/llm/chat HTTP 503 : test-lane is gated: the 'sparebrains' share of the test pool "
            f"is spent for now ({reason})", status_code=503, retry_after=retry_after,
            payload={'ok': False, 'reason': reason, 'tenant': 'sparebrains', 'retry_after_s': retry_after})

    def test_share_held_for_others_parks_the_provider_briefly_not_for_the_job(self):
        env, lane = self.runner()
        env['llm_chat'].side_effect = self.share_refusal('held_for_others', 900)
        with patch.object(attempt.time, 'monotonic', return_value=1000):
            self.assertEqual(env['run_one']('demo', lane, 1), 'defer')
        self.assertEqual(env['exhausted'], {})
        self.assertEqual(env['bench']['told'], {'test-lane': 1900, 'test-sibling': 1900})
        self.assertEqual(env['state']['calls'], 0)

    def test_share_borrow_cap_parks_the_provider_for_the_job(self):
        env, lane = self.runner()
        env['llm_chat'].side_effect = self.share_refusal('borrow_cap', 40000)
        self.assertEqual(env['run_one']('demo', lane, 1), 'exhausted')
        self.assertIn('test', env['exhausted'])

    def test_never_fits_halves_max_tokens_for_the_job_and_asks_the_same_cell_again(self):
        """2026-10-22..23: groq-qwen3-8-27b refused every call at 16,000 max_tokens (3,930 skip rows, 0 accepts)
        though it proved problems at that size through 10-21. kumori's refusal says to lower max_tokens."""
        env, lane = self.runner()
        lane['capability'] = {'is_reasoning_model': True}                     # asked relay.MAX_TOKENS
        nf = attempt.KumoriAPIError('kumori /api/v1/llm/chat HTTP 503 : too big', status_code=503, retry_after=60,
                                    payload={'error_code': 'never_fits'})
        env['llm_chat'].side_effect = [nf, nf, ('answer', 'test-lane', {})]
        with self.assertRaisesRegex(RuntimeError, 'verifier boundary'):      # it got an answer, at 4,000
            env['run_one']('demo', lane, 1)
        sent = [c.kwargs['max_tokens'] for c in env['llm_chat'].call_args_list]
        self.assertEqual(sent, [16000, 8000, 4000])
        self.assertEqual(env['fit_cap'], {'test-lane': 4000}, 'the rest of the job starts at the size that fit')
        env['skip'].assert_not_called()
        self.assertEqual((env['too_big'], env['bench']['streak']), ({}, {}), 'a refusal is no lane error')

    def test_a_row_records_the_max_tokens_the_call_was_sent(self):
        env, lane = self.runner()
        lane['capability'] = {'is_reasoning_model': True}
        env['base_row'] = Mock(return_value={'request_config': {'max_tokens': 16000}})
        env['fit_cap']['test-lane'] = 8000
        env['llm_chat'].side_effect = attempt.KumoriAPIError('kumori /api/v1/llm/chat HTTP 504 : timed out', status_code=504)
        env['run_one']('demo', lane, 1)
        self.assertEqual(env['llm_chat'].call_args.kwargs['max_tokens'], 8000)
        self.assertEqual(env['record'].call_args[0][0]['request_config']['max_tokens'], 8000)

    def test_never_fits_at_the_floor_is_still_a_skip(self):
        env, lane = self.runner()
        lane['capability'] = {'is_reasoning_model': True}
        env['fit_cap']['test-lane'] = attempt.MIN_FIT_TOKENS
        env['llm_chat'].side_effect = attempt.KumoriAPIError('x', status_code=503, payload={'error_code': 'never_fits'})
        self.assertEqual(env['run_one']('demo', lane, 1), 'too_big')
        self.assertEqual(env['llm_chat'].call_count, 1)
        env['skip'].assert_called_once()

    def test_a_lemma_ask_halves_on_never_fits_and_a_refusal_is_not_a_call(self):
        import ast
        from unittest.mock import Mock
        env, lane = self.runner()
        lane['capability'] = {'is_reasoning_model': True}
        tree = ast.parse(Path(attempt.__file__).read_text())
        node = next(n for n in ast.walk(tree) if isinstance(n, ast.FunctionDef) and n.name == 'make_ask')
        env['relay'] = Mock(LEMMA_CALL_S=120, PARK_WAIT_S=90)
        exec(compile(ast.Module(body=[node], type_ignores=[]), attempt.__file__, 'exec'), env)
        nf = attempt.KumoriAPIError('x', status_code=503, payload={'error_code': 'never_fits'})
        env['llm_chat'].side_effect = [nf, nf, ('lemma proof', 'test-lane', {})]
        self.assertEqual(env['make_ask'](lane)('prove it'), 'lemma proof')
        self.assertEqual([c.kwargs['max_tokens'] for c in env['llm_chat'].call_args_list], [16000, 8000, 4000])
        self.assertEqual(env['state']['calls'], 1, 'two refusals and one answer: one call')
        env['llm_chat'].side_effect = [nf]                                  # at the floor: no answer, and no call
        self.assertIsNone(env['make_ask'](lane)('prove it'))
        self.assertEqual(env['state']['calls'], 1)

    def test_never_fits_is_a_skip_and_no_bigger_prompt_is_asked_again(self):
        """2026-10-15..22: 1,281 never_fits refusals, groq-qwen3-8-27b asked primer_tutorial_07 105 times."""
        env, lane = self.runner()
        env['llm_chat'].side_effect = attempt.KumoriAPIError(
            'kumori /api/v1/llm/chat HTTP 503 : test-lane is pacing to the provider limit (tokens/minute:never_fits); '
            'retry in 60s', status_code=503, retry_after=60)
        self.assertEqual(env['run_one']('demo', lane, 1), 'too_big')
        self.assertEqual(env['llm_chat'].call_count, 1)
        self.assertEqual(env['run_one']('demo', lane, 2), 'too_big')   # same prompt: not asked again
        self.assertEqual(env['llm_chat'].call_count, 1)
        self.assertEqual(env['skip'].call_count, 2)
        self.assertEqual((env['state']['calls'], env['bench']['streak']), (0, {}))

    def test_never_fits_is_read_from_the_error_code_whatever_the_message_says(self):
        env, lane = self.runner()
        env['llm_chat'].side_effect = attempt.KumoriAPIError(
            'kumori /api/v1/llm/chat HTTP 503 : test-lane cannot take a call this size; retrying will not help',
            status_code=503, retry_after=60, payload={'error_code': 'never_fits'})
        self.assertEqual(env['run_one']('demo', lane, 1), 'too_big')

    def test_a_floor_learned_while_waiting_for_the_provider_stops_the_call(self):
        env, lane = self.runner()
        env['provider_lock']['test'] = Mock(__enter__=Mock(side_effect=lambda *a: env['too_big'].update({'test-lane': 1})),
                                            __exit__=Mock(return_value=False))
        self.assertEqual(env['run_one']('demo', lane, 1), 'too_big')
        env['llm_chat'].assert_not_called()

    def test_a_shorter_prompt_than_the_floor_is_still_asked(self):
        env, lane = self.runner()
        env['too_big']['test-lane'] = 10 ** 6
        env['llm_chat'].return_value = ('answer', 'test-lane', {})
        with self.assertRaisesRegex(RuntimeError, 'verifier boundary'):
            env['run_one']('demo', lane, 1)
        env['llm_chat'].assert_called_once()

    def test_a_row_records_the_timeout_the_call_asked_for(self):
        """Every relay row said router_timeout_s 60 while relay calls ask 240 s (2026-10-22). A cold try asks
        LADDER_CALL_S as a long_call since 2026-10-28 (half its calls on the slow lanes died at 60 s)."""
        env, lane = self.runner()
        env['llm_chat'].side_effect = attempt.KumoriAPIError('kumori /api/v1/llm/chat HTTP 504 : timed out', status_code=504)
        env['relay'] = Mock(relay_prompt=Mock(return_value=("prompt", None)), LONG_CALL_S=240)
        env['run_one']('demo', lane, 1, relay_ctx={"dossier": {}, "this_job": []})
        row = env['record'].call_args[0][0]
        self.assertEqual((row['request_config']['router_timeout_s'], row['request_config']['long_call']), (240, True))
        env['run_one']('demo', lane, 1)
        row = env['record'].call_args[0][0]
        self.assertEqual((row['request_config']['router_timeout_s'], row['request_config']['long_call']), (attempt.LADDER_CALL_S, True))
        self.assertEqual(attempt.LADDER_CALL_S, 120)
        self.assertLessEqual(row['upstream_seconds'], row['call_seconds'], "time inside the call alone, apart from lock waits and parks")

    def test_a_failed_rescue_leaves_its_marker_on_the_error_row(self):
        """#597: kumori's client raises a failed edge-cut rescue with payload["recovery"]; the ledger row keeps it, so the
        daily report counts rescues tried, not only the ones that came back."""
        env, lane = self.runner()
        rec = {"attempted": True, "succeeded": False, "original": "http_504_html", "cut_at_s": 121.6, "wait_s": 200}
        env['llm_chat'].side_effect = attempt.KumoriAPIError('kumori /api/v1/llm/chat HTTP 524: cut off by the proxy and no saved answer',
                                                             status_code=524, payload={"recovery": rec})
        env['run_one']('demo', lane, 1)
        row = env['record'].call_args[0][0]
        self.assertEqual((row['verdict'], row['inference']['recovery']), ('error', rec))

    def test_a_cold_try_asks_the_long_bound_only_on_a_lane_running_slow(self):
        """2026-11-01 held every cold try at 120 s because Cloudflare cuts at 125 s; the client has fetched the saved
        answer after the cut since that evening (kumori 364afa74), so a slow lane now asks 240 s (#658, 2026-11-08)."""
        env, lane = self.runner()
        env['llm_chat'].side_effect = attempt.KumoriAPIError('kumori /api/v1/llm/chat HTTP 504 : timed out', status_code=504)
        attempt.RUNNING_SLOW.add('sealion-qwen-sea-lion-v4-5-27b-it')
        try:
            for backend, bound in (('sealion-qwen-sea-lion-v4-5-27b-it', 240), ('test-lane', attempt.LADDER_CALL_S)):
                env['run_one']('demo', dict(lane, backend=backend), 1)
                self.assertEqual(env['llm_chat'].call_args.kwargs['timeout_s'], bound, backend)
                self.assertEqual(env['record'].call_args[0][0]['request_config']['router_timeout_s'], bound)
        finally:
            attempt.RUNNING_SLOW.discard('sealion-qwen-sea-lion-v4-5-27b-it')

    def test_upstream_seconds_sums_the_calls_alone_and_leaves_out_the_retry_sleep(self):
        env, lane = self.runner()
        clock = [0.0]
        def chat(*a, **k):
            clock[0] += 10                                  # each call takes 10 s on the controlled clock
            if env['llm_chat'].call_count == 1:
                raise attempt.KumoriAPIError('kumori /api/v1/llm/chat HTTP 429 : RPM spacing', status_code=429, retry_after=60)
            raise attempt.KumoriAPIError('kumori /api/v1/llm/chat HTTP 504 : timed out', status_code=504)   # the row is written without Lean
        env['llm_chat'].side_effect = chat
        with patch.object(attempt.time, 'monotonic', lambda: clock[0]), \
             patch.object(attempt.time, 'sleep', lambda s: clock.__setitem__(0, clock[0] + s)):
            env['run_one']('demo', lane, 1)
        row = env['record'].call_args[0][0]
        self.assertEqual(env['llm_chat'].call_count, 2)
        self.assertEqual(row['upstream_seconds'], 20.0, "two calls of 10 s; the 60.5 s retry sleep is not upstream time")
        self.assertEqual(row['upstream_answer_s'], None, "no call answered")

    def test_the_answering_calls_own_time_is_recorded_not_a_slow_failed_try(self):
        """#597 (Codex f1, round 2): a slow failed try then a short direct answer is not a rescue; the tell is the
        answering call's clock alone."""
        env, lane = self.runner()
        clock = [0.0]
        def chat(*a, **k):
            if env['llm_chat'].call_count == 1:
                clock[0] += 130                              # a slow 429 (the only retried failure)
                raise attempt.KumoriAPIError('kumori /api/v1/llm/chat HTTP 429 : RPM spacing', status_code=429, retry_after=1)
            clock[0] += 10
            raise attempt.KumoriAPIError('kumori /api/v1/llm/chat HTTP 504 : timed out', status_code=504)
        env['llm_chat'].side_effect = chat
        with patch.object(attempt.time, 'monotonic', lambda: clock[0]), patch.object(attempt.time, 'sleep', lambda s: None):
            env['run_one']('demo', lane, 1)
        row = env['record'].call_args[0][0]
        self.assertEqual((row['upstream_seconds'], row['upstream_answer_s']), (140.0, None))
        self.assertGreaterEqual(row['call_seconds'], 80.0, "call_seconds still holds the whole interval")

    def test_a_timeout_on_this_target_is_the_lanes_own_error(self):
        env, lane = self.runner()
        env['llm_chat'].side_effect = attempt.KumoriAPIError(
            'kumori /api/v1/llm/chat HTTP 504 : backend did not respond in time', status_code=504)
        self.assertEqual(env['run_one']('demo', lane, 1), 'error')

    def test_real_ledger_reasons_are_scoped_by_who_failed(self):
        from ladder import error_scope, lane_is_gone
        router = ['KumoriAPIError: kumori /api/v1/llm/chat HTTP 404 : unknown backend: openrouter-deepseek-v4-flash-0731',
                  'KumoriAPIError: kumori /api/v1/llm/chat HTTP 502 : unknown',
                  'KumoriAPIError: kumori /api/v1/llm/chat HTTP 503 : groq-gptoss is benched: rate limited by the provider',
                  "KumoriAPIError: Network error reaching kumori: HTTPSConnectionPool(host='kumori.ai', port=443)",
                  'KumoriAPIError: kumori /api/v1/llm/chat HTTP 520 : unknown', 'something nobody has seen before']
        lane = ['KumoriAPIError: kumori /api/v1/llm/chat HTTP 504 : backend did not respond in time',
                'KumoriAPIError: kumori /api/v1/llm/chat HTTP 502 : backend vercel-laguna-s-2-1-free returned no text']
        self.assertEqual([error_scope(r) for r in router], ['router'] * len(router))
        self.assertEqual([error_scope(r) for r in lane], ['lane'] * len(lane))
        self.assertTrue(lane_is_gone(router[0]))
        self.assertFalse(lane_is_gone(router[1]))


class SubgoalLoopTests(RetryPacingTests):
    """A rejected relay try goes through tools/subgoals.py, and an accept from it is the try's verdict."""
    def relay_env(self, rep):
        import tempfile
        from unittest.mock import Mock
        env, lane = self.runner()
        from collections import defaultdict
        env.update(extract_proof=attempt.extract_proof, tmpdir=Path(tempfile.mkdtemp()),
                   per_target=defaultdict(lambda: {"done": 0, "accepts": 0, "errors": 0, "lanes": []}),
                   judge=Mock(return_value=("reject", "lean exit 1: x.lean:2:2: error: nope", 1.0, "x.lean:2:2: error: nope")),
                   subgoal_repair=Mock(return_value=rep), look_up_names=Mock(),
                   relay=Mock(relay_prompt=Mock(return_value=("prompt", {"try_mode": "relay", "prev_id": None,
                                                                          "comment_ids": [], "dossier_sha": "s"})),
                              LONG_CALL_S=240),
                   args=type(env['args'])(**{**vars(env['args']), "lean_timeout": 30}))
        env['llm_chat'].return_value = ("```lean\n  exact foo\n```", "test-lane", {})
        return env, lane, {"dossier": {}, "this_job": [], "real_names": {}}

    def test_the_loop_turns_a_reject_into_an_accept(self):
        whole = "theorem demo : True := by\n  trivial\n"
        env, lane, ctx = self.relay_env({"accepted": whole, "closed_by_lean": 1, "lemmas_proved": 0, "holes": 1})
        with patch.object(attempt.Path, "mkdir"), patch.object(attempt.Path, "write_text"):
            self.assertEqual(env['run_one']('demo', lane, 1, relay_ctx=ctx), 'accept')
        row = env['record'].call_args[0][0]
        self.assertIn("1 step(s) closed by Lean", row["reason"])
        self.assertEqual(row["tools"]["subgoals"]["closed_by_lean"], 1)
        self.assertNotIn("accepted", row["tools"]["subgoals"])

    def test_a_partial_loop_hands_its_sketch_to_the_next_lane(self):
        env, lane, ctx = self.relay_env({"stopped": "1 of 1 open steps unproved", "closed_by_lean": 2,
                                         "sketch": "theorem demo : True := by\n  · sorry"})
        self.assertEqual(env['run_one']('demo', lane, 1, relay_ctx=ctx), 'reject')
        said = ctx["this_job"][0][3]
        self.assertIn("Lean's automation closed 2 failing step(s)", said)
        self.assertIn("· sorry", said)
        self.assertNotIn("sketch", env['record'].call_args[0][0]["tools"])


class OwedHistoryTests(unittest.TestCase):
    def ledger(self, rows):
        import json, tempfile
        root = Path(tempfile.mkdtemp())
        (root / 'demo').mkdir()
        (root / 'demo' / 'run.jsonl').write_text('\n'.join(json.dumps(
            dict(target_set='demo', target=t, backend=b, verdict=v, reason=r, ts=ts)) for t, b, v, r, ts in rows))
        return attempt.owed_history(root)

    def owed(self, hist, target, backend):
        lane = {'backend': backend, 'provider': 'p', 'tier': 'high', 'rank': 3}
        with patch.object(attempt, 'rung_of', return_value=('r', 0)), patch.object(attempt, 'sort_key', return_value=0):
            work = attempt.build_ladder_queue([('demo', Path('.'), [target])], [lane], 1, hist)
        return len(work)

    GONE = 'KumoriAPIError: kumori /api/v1/llm/chat HTTP 404 : unknown backend: dead'
    DOWN = 'KumoriAPIError: kumori /api/v1/llm/chat HTTP 502 : unknown'
    SLOW = 'KumoriAPIError: kumori /api/v1/llm/chat HTTP 504 : backend did not respond in time'

    def test_router_errors_never_close_a_cell(self):
        hist = self.ledger([('t1', 'dead', 'error', r, f'2026-09-20T05:0{i}:00+00:00')
                            for i, r in enumerate([self.GONE] * 4 + [self.DOWN] * 4)])
        self.assertEqual(hist[('demo', 't1', 'dead')], {'answered': 0, 'errors': 0, 'router_errors': 8, 'cuts': 0, 'cut_budgets': set()})
        self.assertEqual(self.owed(hist, 't1', 'dead'), 1)

    CUT = 'KumoriAPIError: kumori /api/v1/llm/result/0abf HTTP 503 [reasoning_truncated] : backend flint returned no text'

    def test_one_reasoning_cut_closes_the_cell(self):
        """#658 follow-up (2026-11-09): after a cut, the same cell's next try was accepted 0 of 53 times since 11-01
        (43 cut again), low effort included (0 of 21); a cut cell is not asked again the same way."""
        hist = self.ledger([('t1', 'flint', 'error', self.CUT, '2026-11-09T05:00:00+00:00')])
        self.assertEqual(hist[('demo', 't1', 'flint')]['cuts'], 1)
        self.assertEqual(self.owed(hist, 't1', 'flint'), 0)
        hist = self.ledger([('t1', 'flint', 'error', self.SLOW, '2026-11-09T05:00:00+00:00')])
        self.assertEqual(self.owed(hist, 't1', 'flint'), 1, "a timeout is not a cut")
        h = {'answered': 0, 'errors': 0, 'cuts': 1, 'cut_budgets': {16000}}
        self.assertTrue(attempt.cut_closed(h, 16000))
        self.assertFalse(attempt.cut_closed(h, 32000), "a deliberately different budget reopens it (Codex f2)")
        self.assertTrue(attempt.cut_closed({**h, 'cut_budgets': {None}}, 32000), "unknown budget: closed for any")

    def test_lane_errors_from_a_dead_lane_do_not_close_a_cell(self):
        hist = self.ledger([('t1', 'dead', 'error', self.SLOW, f'2026-09-20T05:0{i}:00+00:00') for i in range(3)])
        self.assertEqual(hist[('demo', 't1', 'dead')]['errors'], 0)
        self.assertEqual(self.owed(hist, 't1', 'dead'), 1)

    def test_three_timeouts_while_the_lane_answers_others_do_close_it(self):
        rows = [('t1', 'alive', 'error', self.SLOW, f'2026-09-20T05:0{i}:00+00:00') for i in range(3)]
        rows.append(('t2', 'alive', 'reject', 'unsolved goals', '2026-09-20T05:10:00+00:00'))
        hist = self.ledger(rows)
        self.assertEqual(hist[('demo', 't1', 'alive')]['errors'], 3)
        self.assertEqual(self.owed(hist, 't1', 'alive'), 0)

    def test_an_answer_hours_away_does_not_vouch_for_the_lane(self):
        rows = [('t1', 'alive', 'error', self.SLOW, f'2026-09-20T05:0{i}:00+00:00') for i in range(3)]
        rows.append(('t2', 'alive', 'reject', 'unsolved goals', '2026-09-20T09:00:00+00:00'))
        self.assertEqual(self.ledger(rows)[('demo', 't1', 'alive')]['errors'], 0)

class BaselineSetAsideTests(unittest.TestCase):
    def test_cells_on_baseline_targets_are_set_aside_and_said(self):
        from collections import deque
        lane = {"backend": "x"}
        work = deque([("s", "d", "easy", "r", 0, lane, 1), ("s", "d", "hard", "r", 0, lane, 1)])
        b = {"set": {("s", "easy")}, "version": {"run_id": "v2"}}
        with patch("replay.no_model_set", return_value=b):
            kept, note = attempt.set_aside_baseline(work, "ledger")
        self.assertEqual([i[2] for i in kept], ["hard"])
        self.assertIn("1 cells set aside on 1 targets", note)
        self.assertIn("v2", note)

    def test_no_baseline_sets_nothing_aside(self):
        from collections import deque
        work = deque([("s", "d", "easy", "r", 0, {"backend": "x"}, 1)])
        with patch("replay.no_model_set", side_effect=ValueError("no tools_alone rows")):
            kept, note = attempt.set_aside_baseline(work, "ledger")
        self.assertEqual((len(kept), "nothing set aside" in note), (1, True))


if __name__ == "__main__":
    unittest.main()


class RetroCohortTests(unittest.TestCase):
    """`--retro --cohort FILE` (#574): the free chain on a frozen file of stored rejects (the repair tries the nightly
    retro's cold-only queue never reaches), solves of open problems recorded as retro records them, no ablation row."""
    def cohort(self, rows):
        import gzip, json, tempfile
        d = Path(tempfile.mkdtemp())
        with gzip.open(d / "c.jsonl.gz", "wt") as fh:
            fh.writelines(json.dumps(r) + "\n" for r in rows)
        return d / "c.jsonl.gz"

    def test_pages_come_from_the_file_in_slice_and_id_order_and_never_from_kumori(self):
        path = self.cohort([{"id": i} for i in (9, 3, 6, 4, 12, 7)])
        todo = Mock(side_effect=AssertionError("asked kumori"))
        pages = list(attempt.retro_pages("0/3", todo, path, limit=2))
        self.assertEqual([[r["id"] for r in p] for p in pages], [[3, 6], [9, 12]])
        todo.assert_not_called()

    def test_without_a_cohort_pages_come_from_the_todo_queue(self):
        todo = Mock(side_effect=[[{"id": 5}], []])
        self.assertEqual([[r["id"] for r in p] for p in attempt.retro_pages("1/6", todo, None)], [[5]])
        self.assertEqual(todo.call_args_list[0].args, ("1/6", 0, 100))
        self.assertEqual(todo.call_args_list[1].args, ("1/6", 5, 100))

    def runner(self, chain):
        import ast, hashlib, tempfile, threading, time
        tree = ast.parse(Path(attempt.__file__).read_text())
        node = next(n for n in ast.walk(tree) if isinstance(n, ast.FunctionDef) and n.name == 'retro_one')
        root = Path(tempfile.mkdtemp())
        (root / "targets" / "s").mkdir(parents=True)
        (root / "targets" / "s" / "demo.lean").write_text("theorem demo : True := by\n  sorry\n")
        env = dict(vars(attempt), ROOT=root, hashlib=hashlib, time=time, lock=threading.Lock(), solved={}, run_id="r",
                   state={"calls": 0, "accepts": 0}, record=Mock(), base_row=Mock(return_value={"target": "demo"}),
                   toolscore=Mock(run_chain=Mock(side_effect=chain)), lean_tools=Mock())
        exec(compile(ast.Module(body=[node], type_ignores=[]), attempt.__file__, 'exec'), env)
        return env

    A = {"id": 41, "target_set": "s", "target": "demo", "backend": "tiny-lane", "quality_tier": "tiny", "rung": "r1",
         "proof": "  bogus", "lean_output": ""}
    WIN = {"fixes": [], "b_verdict": "reject", "c_verdict": "accept", "rep": {"closed_by_lean": 1},
           "final": "theorem demo : True := by\n  trivial"}

    def test_an_open_solve_is_recorded_for_the_lane_that_wrote_it_and_no_ablation_row_is_sent(self):
        env = self.runner(lambda *a: self.WIN)
        self.assertEqual(env["retro_one"](self.A, {("s", "demo")}, None, None), ("accept", "reject"))
        row = env["record"].call_args[0][0]
        self.assertEqual((row["try_mode"], row["prev_id"], row["verdict"]), ("fixer+loop", 41, "accept"))
        self.assertEqual(env["base_row"].call_args[0][1]["backend"], "tiny-lane")
        self.assertEqual(env["solved"]["demo"]["backend"], "tiny-lane")
        self.assertTrue((env["ROOT"] / "verified" / "s" / "demo" / "tiny-lane.lean").exists())

    def test_the_nightly_retro_still_sends_its_ablation_row(self):
        env, sent = self.runner(lambda *a: self.WIN), Mock()
        env["retro_one"](self.A, {("s", "demo")}, None, sent)
        self.assertEqual(sent.call_args[0][0]["attempt_id"], 41)
        self.assertTrue(sent.call_args[0][0]["solved_open"])

    def test_the_nightly_retro_measures_a_target_not_open_and_records_no_solve(self):
        env, sent = self.runner(lambda *a: self.WIN), Mock()
        self.assertEqual(env["retro_one"](self.A, set(), None, sent), ("accept", "reject"))
        env["record"].assert_not_called()
        self.assertFalse(sent.call_args[0][0]["solved_open"])

    def test_a_cohort_row_on_a_target_not_open_or_already_solved_is_not_re_run(self):
        env = self.runner(lambda *a: self.WIN)
        self.assertIsNone(env["retro_one"](self.A, set(), None, None))
        env["solved"]["demo"] = {"backend": "x"}
        self.assertIsNone(env["retro_one"](self.A, {("s", "demo")}, None, None))
        env["toolscore"].run_chain.assert_not_called()


class PilotTests(unittest.TestCase):
    """`--pilot MANIFEST`: arms B and C of a guided blueprint on one problem, rows in ledger/stall, an accepted text in
    SB_GUIDED_OUT (the run's artifact) and nowhere public (the manifest's credit line)."""
    def runner(self, fills):
        import ast, json, tempfile, threading
        module = ast.parse(Path(attempt.__file__).read_text())
        node = next(n for n in ast.walk(module) if isinstance(n, ast.FunctionDef) and n.name == 'pilot_one')
        root = Path(tempfile.mkdtemp())
        (root / "targets" / "s").mkdir(parents=True)
        (root / "targets" / "s" / "demo.lean").write_text("import Mathlib\ntheorem demo : True := by\n  sorry\n")
        (root / "ledger" / "stall" / "blueprints").mkdir(parents=True)
        (root / "ledger" / "stall" / "blueprints" / "demo-1.json").write_text(json.dumps({"ok": False, "statements": ["x"]}))
        (root / "ledger" / "stall" / "blueprints" / "demo-2.json").write_text(json.dumps({"ok": True, "statements": ["True", "True ∧ True"]}))
        import os
        os.environ["SB_GUIDED_OUT"] = str(root / "held")
        self.addCleanup(os.environ.pop, "SB_GUIDED_OUT", None)
        env = dict(vars(attempt), ROOT=root, json=json, lock=threading.Lock(), record=Mock(), run_id="r1",
                   blueprint=Mock(fill=Mock(side_effect=fills)), lean_tools=Mock())
        exec(compile(ast.Module(body=[node], type_ignores=[]), attempt.__file__, 'exec'), env)
        return env, root

    def rows(self, root):
        import json
        return [json.loads(l) for f in (root / "ledger" / "stall").glob("pilot-*.jsonl") for l in f.read_text().splitlines()]

    def test_arms_b_and_c_run_on_the_latest_gated_blueprint_and_write_their_rows(self):
        b = {"holes": 2, "closed_by": {}, "failed": [1, 2], "unattempted": [], "asked": 0, "tries": []}
        c = {"holes": 2, "closed_by": {1: "lean", 2: 0}, "failed": [], "unattempted": [], "asked": 3, "final": "accept",
             "accepted": "import Mathlib\ntheorem demo : True := by\n  have bp_1 : True := by\n    trivial\n  trivial\n",
             "tries": [{"hole": 2, "by": 0, "verdict": "accept", "reason": ""}]}
        c.update(answered=3, unanswered=0)
        b.update(answered=0, unanswered=0)
        env, root = self.runner([b, c])
        man = {"id": "m", "lanes": ["lane-off", "lane-a"], "asks_per_problem": 5}      # lane-off is not live today
        got = env["pilot_one"]("s/demo", man, lambda names: [("lane-a", Mock())], root / "ledger" / "stall" / "pilot-m-r1.jsonl")
        self.assertEqual(got, {"B": None, "C": "accept"})
        rows = self.rows(root)
        self.assertEqual([r["arm"] for r in rows], ["B", "C"])
        self.assertEqual(rows[1]["blueprint"], "ledger/stall/blueprints/demo-2.json", "the latest gated one, not the rejected one")
        self.assertEqual((rows[1]["closed_by"], rows[1]["asked"], rows[1]["final"]), ({"1": "lean", "2": "lane-a"}, 3, "accept"),
                         "Codex f1: credit follows the lanes asked, not the manifest's order")
        self.assertEqual(rows[1]["tries"][0]["by"], "lane-a")
        self.assertEqual((rows[1]["lanes_live"], rows[1]["lanes_missing"]), (["lane-a"], ["lane-off"]))
        self.assertEqual(rows[1]["manifest"], "m")
        calls = env["blueprint"].fill.call_args_list
        self.assertEqual(calls[0].kwargs["asks"], [], "arm B asks nobody")
        self.assertEqual((len(calls[1].kwargs["asks"]), calls[1].kwargs["max_asks"]), (1, 5))
        self.assertIs(calls[1].kwargs["run_lean"], env["lean_tools"].run_lean, "the Lean tier runs the recipes apart")
        held = Path(env["os"].environ["SB_GUIDED_OUT"])
        self.assertEqual((held / "demo-r1.lean").read_text(), c["accepted"])
        self.assertEqual(rows[1]["accepted_sha"], __import__("hashlib").sha256(c["accepted"].encode()).hexdigest())
        self.assertNotIn("accepted", rows[1], "the proof text is not in the row")
        self.assertFalse((root / "verified").exists(), "a guided solve is not a verified/ file")
        self.assertEqual([p.name for p in (root / "ledger").rglob("*.lean")], [],
                         "Codex f2: publish.py commits everything under ledger/ and verified/; the text stays out of both")
        env["record"].assert_not_called()

    def test_a_problem_without_a_gated_blueprint_is_noted_and_skipped(self):
        env, root = self.runner([])
        (root / "ledger" / "stall" / "blueprints" / "demo-2.json").unlink()
        got = env["pilot_one"]("s/demo", {"id": "m", "lanes": [], "asks_per_problem": 1}, lambda names: [], root / "ledger" / "stall" / "pilot-m-r1.jsonl")
        self.assertIsNone(got)
        self.assertEqual([r["arm"] for r in self.rows(root)], ["none"])
        env["blueprint"].fill.assert_not_called()


class PatientAskTests(unittest.TestCase):
    """attempt.patient: a guided pilot's ask waits out the router's bench instead of spending budget on a refusal."""
    def test_a_benched_lane_is_waited_for_then_asked_once_more(self):
        state = {"benched": [True, True, False, False, False]}
        ask = Mock(side_effect=[None, "reply"])
        slept = []
        p = attempt.patient(ask, lambda: state["benched"].pop(0) if state["benched"] else False, wait_s=60, sleep=slept.append)
        self.assertEqual(p("q"), "reply")
        self.assertEqual(ask.call_count, 2)
        self.assertEqual(slept, [5, 5])

    def test_a_lane_still_benched_after_the_wait_is_not_asked_again(self):
        ask = Mock(return_value=None)
        slept = []
        p = attempt.patient(ask, lambda: True, wait_s=20, sleep=slept.append)
        self.assertIsNone(p("q"))
        self.assertEqual(ask.call_count, 1)
        self.assertEqual(sum(slept), 40, "two bounded waits of wait_s, before and after the refused ask")

    def test_an_unbenched_lane_is_asked_at_once(self):
        ask = Mock(return_value="reply")
        p = attempt.patient(ask, lambda: False, wait_s=60, sleep=Mock(side_effect=AssertionError("slept")))
        self.assertEqual(p("q"), "reply")


class LemmaRowTests(unittest.TestCase):
    def test_a_lemma_row_carries_the_full_statements_hash_beside_its_600_char_text(self):
        """Codex 20261109T204946451069Z f8: `lemma` keeps 600 chars, so two long statements can read as one; the hash
        of the whole statement tells them apart (tools/stall.py)."""
        import ast, hashlib
        module = ast.parse(Path(attempt.__file__).read_text())
        node = next(n for n in ast.walk(module) if isinstance(n, ast.FunctionDef) and n.name == 'make_on_lemma')
        env = dict(vars(attempt), hashlib=hashlib, base_row=Mock(return_value={}), record=Mock(),
                   relay=Mock(LEMMA_CALL_S=1), subgoals=Mock(lemma_file=Mock(return_value="")))
        exec(compile(ast.Module(body=[node], type_ignores=[]), attempt.__file__, 'exec'), env)
        statement = "x" * 700
        env['make_on_lemma']("demo", [{"backend": "l"}], 1, "sha", "s", "prefix", "relay-subgoal")(
            statement, {"verdict": "accept", "proof": "p", "prompt": "q", "reason": ""})
        row = env['record'].call_args[0][0]
        self.assertEqual(len(row["lemma"]), 600)
        self.assertEqual(row["lemma_sha"], hashlib.sha256(statement.encode()).hexdigest())
