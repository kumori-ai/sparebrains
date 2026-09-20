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
                   provider_lock=defaultdict(threading.Lock), bench={'streak': {}, 'told': {}},
                   benched=Mock(return_value=False), llm_chat=Mock(),
                   args=SimpleNamespace(max_tokens=256, call_timeout=60), state={'calls': 0},
                   extract_proof=Mock(side_effect=RuntimeError('verifier boundary')))
        exec(compile(ast.Module(body=[node], type_ignores=[]), attempt.__file__, 'exec'), env)
        return env, {'backend': 'test-lane', 'provider': 'test'}

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


if __name__ == "__main__":
    unittest.main()
