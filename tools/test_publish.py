"""Offline git fixtures. No provider calls, deployments, or Lean execution."""
import json
from pathlib import Path
import tempfile
import unittest

import publish as publish_module
from publish import git, publish, preserve_outputs, snapshot_outputs


class PublishTests(unittest.TestCase):
    def setUp(self):
        self.root = Path(tempfile.mkdtemp(prefix='sparebrains-publish-test-'))
        self.remote = self.root / 'remote.git'
        self.writer = self.root / 'writer'
        self.job = self.root / 'job'
        git(self.root, 'init', '--bare', str(self.remote))
        git(self.root, 'clone', str(self.remote), str(self.writer))
        git(self.writer, 'checkout', '-b', 'main')
        for repo in [self.writer]:
            self.identity(repo)
        self.proof = 'verified/primer/demo/lane.lean'
        self.write(self.writer, self.proof, b'original verified proof\n')
        self.write(self.writer, 'ledger/primer/base.jsonl', b'{"id":0}\n')
        self.commit(self.writer, 'seed')
        git(self.remote, 'symbolic-ref', 'HEAD', 'refs/heads/main')
        git(self.root, 'clone', str(self.remote), str(self.job))
        self.identity(self.job)

    def identity(self, repo):
        git(repo, 'config', 'user.email', 'fixture@example.invalid')
        git(repo, 'config', 'user.name', 'Offline fixture')

    def write(self, repo, name, data):
        path = repo / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)

    def commit(self, repo, message):
        git(repo, 'add', '.')
        git(repo, 'commit', '-m', message)
        git(repo, 'push', 'origin', 'HEAD:main')

    def test_recovery_snapshot_contains_only_this_runs_changes(self):
        self.write(self.job, 'ledger/primer/job.jsonl', b'{"id":2}\n')
        self.write(self.job, self.proof, b'this accepted proof\n')
        destination = self.root / 'recovery'
        files = snapshot_outputs(self.job, destination)
        self.assertEqual(set(files), {'ledger/primer/job.jsonl', self.proof})
        self.assertFalse((destination / 'ledger/primer/base.jsonl').exists())
        self.assertEqual((destination / self.proof).read_bytes(), b'this accepted proof\n')

    def test_stale_job_keeps_both_proofs_and_ledgers(self):
        before = git(self.job, 'rev-parse', 'HEAD').stdout
        self.write(self.writer, self.proof, b'other accepted proof\n')
        self.write(self.writer, 'ledger/primer/other.jsonl', b'{"id":1}\n')
        self.commit(self.writer, 'other completed job')
        self.write(self.job, self.proof, b'this accepted proof\n')
        self.write(self.job, 'ledger/primer/job.jsonl', b'{"id":2}\n')
        publish(self.job, 'publish test')
        git(self.writer, 'pull', '--ff-only', 'origin', 'main')
        self.assertEqual((self.writer / self.proof).read_bytes(), b'other accepted proof\n')
        siblings = list((self.writer / self.proof).parent.glob('lane.*.lean'))
        self.assertEqual(len(siblings), 1)
        self.assertEqual(siblings[0].read_bytes(), b'this accepted proof\n')
        self.assertTrue((self.writer / 'ledger/primer/other.jsonl').exists())
        self.assertTrue((self.writer / 'ledger/primer/job.jsonl').exists())
        self.assertEqual(git(self.job, 'rev-parse', 'HEAD').stdout, before)
        self.assertEqual((self.job / self.proof).read_bytes(), b'this accepted proof\n')
        # Re-publishing is idempotent: no duplicate rows/proofs or new commit.
        head = git(self.remote, 'rev-parse', 'main').stdout
        publish(self.job, 'repeat test')
        self.assertEqual(git(self.remote, 'rev-parse', 'main').stdout, head)

    def test_competing_push_is_retried_without_losing_either_side(self):
        self.write(self.job, 'ledger/primer/job.jsonl', b'{"id":2}\n')
        def race(attempt):
            if attempt == 1:
                self.write(self.writer, 'ledger/primer/other.jsonl', b'{"id":3}\n')
                self.commit(self.writer, 'concurrent writer')
        publish(self.job, 'retry test', before_push=race)
        git(self.writer, 'pull', '--ff-only', 'origin', 'main')
        self.assertTrue((self.writer / 'ledger/primer/job.jsonl').exists())
        self.assertTrue((self.writer / 'ledger/primer/other.jsonl').exists())

    def test_retry_bound_preserves_original_outputs(self):
        self.write(self.job, 'ledger/primer/job.jsonl', b'{"id":2}\n')
        def race(attempt):
            self.write(self.writer, f'ledger/primer/race{attempt}.jsonl', b'{"id":3}\n')
            self.commit(self.writer, f'race {attempt}')
        with self.assertRaisesRegex(RuntimeError, 'after 2 attempts'):
            publish(self.job, 'bounded test', attempts=2, before_push=race)
        self.assertEqual((self.job / 'ledger/primer/job.jsonl').read_bytes(), b'{"id":2}\n')

    def reject_pushes(self, times):
        """A pre-receive hook that refuses the next `times` pushes, as GitHub's 500s did (run 41777596480)."""
        count = self.root / 'rejections'
        count.write_text(str(times))
        hook = self.remote / 'hooks' / 'pre-receive'
        hook.write_text(f'#!/bin/sh\nn=$(cat {count}); [ "$n" -gt 0 ] || exit 0\n'
                        f'echo $((n-1)) > {count}; echo "Internal Server Error" >&2; exit 1\n')
        hook.chmod(0o755)

    def test_server_error_without_a_competing_commit_is_retried(self):
        publish_module.BACKOFF_S = 0
        self.reject_pushes(1)
        self.write(self.job, 'ledger/primer/job.jsonl', b'{"id":2}\n')
        publish(self.job, 'transient test')
        git(self.writer, 'pull', '--ff-only', 'origin', 'main')
        self.assertTrue((self.writer / 'ledger/primer/job.jsonl').exists())

    def test_a_server_that_keeps_failing_stops_at_the_bound(self):
        publish_module.BACKOFF_S = 0
        self.reject_pushes(5)
        self.write(self.job, 'ledger/primer/job.jsonl', b'{"id":2}\n')
        with self.assertRaisesRegex(RuntimeError, 'Internal Server Error'):
            publish(self.job, 'bounded transient', attempts=2)
        self.assertEqual((self.root / 'rejections').read_text().strip(), '3')
        self.assertEqual((self.job / 'ledger/primer/job.jsonl').read_bytes(), b'{"id":2}\n')

    def test_same_run_ledger_union_does_not_duplicate_shared_prefix(self):
        path = 'ledger/primer/base.jsonl'
        preserve_outputs(self.job, {path: b'{"id":0}\n{"id":4}\n'})
        preserve_outputs(self.job, {path: b'{"id":0}\n{"id":5}\n'})
        rows = [json.loads(line) for line in (self.job / path).read_text().splitlines()]
        self.assertEqual(rows, [{'id': 0}, {'id': 4}, {'id': 5}])


if __name__ == '__main__':
    unittest.main()
