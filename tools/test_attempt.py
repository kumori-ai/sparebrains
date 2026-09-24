"""Small parser contract tests. Lean remains the end-to-end verifier in Actions."""
import sys
import unittest
from unittest.mock import patch
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
from attempt import extract_proof
import attempt


class ExtractProofTests(unittest.TestCase):
    def test_recovers_bare_by_block(self):
        self.assertEqual(extract_proof("by\n  norm_num\n", "demo"), "  norm_num\n")

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
                   state={'calls': 0, 'errors': 0, 'accepts': 0}, exhausted={},
                   order=[{'backend': 'test-lane', 'provider': 'test'}, {'backend': 'test-sibling', 'provider': 'test'},
                          {'backend': 'other-lane', 'provider': 'other'}],
                   extract_proof=Mock(side_effect=RuntimeError('verifier boundary')))
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
        self.assertEqual(hist[('demo', 't1', 'dead')], {'answered': 0, 'errors': 0, 'router_errors': 8})
        self.assertEqual(self.owed(hist, 't1', 'dead'), 1)

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


if __name__ == "__main__":
    unittest.main()
