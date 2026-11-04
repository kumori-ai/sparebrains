"""Publish only generated ledger/proofs onto fresh main, preserving both sides.

The attempt checkout stays untouched. Each bounded push retry gets a fresh
worktree; a divergent proof gets a content-addressed sibling, not ours/theirs.
Recovery artifacts are uploaded by the workflow BEFORE this script is called.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile
import time

BACKOFF_S = 20   # between pushes refused by the server with no competing commit (a GitHub 500, run 41777596480)


def git(repo, *args, check=True):
    result = subprocess.run(['git', '-C', str(repo), *args], capture_output=True,
                            text=True, timeout=120)
    if check and result.returncode:
        raise RuntimeError(f'git {args[0]} failed: {result.stderr[-1500:]}')
    return result


def changed_outputs(repo):
    deleted = git(repo, 'diff', '--name-only', '--diff-filter=D', 'HEAD', '--', 'ledger', 'verified').stdout
    if deleted:
        raise RuntimeError('Publishing refuses deleted outputs: ' + deleted)
    changed = git(repo, 'diff', '--name-only', '-z', 'HEAD', '--', 'ledger', 'verified').stdout
    untracked = git(repo, 'ls-files', '--others', '--exclude-standard', '-z', '--', 'ledger', 'verified').stdout
    files = {}
    for name in set((changed + untracked).split('\0')) - {''}:
        path = Path(name)
        if path.is_absolute() or '..' in path.parts or path.parts[0] not in ('ledger', 'verified'):
            raise ValueError(f'Unsafe output path: {name}')
        if (repo / path).is_symlink():
            raise ValueError(f'Symlink output refused: {name}')
        files[name] = (repo / path).read_bytes()
    return files


def snapshot_outputs(repo, destination):
    """Archive this run's changed outputs; do not re-upload the entire history."""
    files = changed_outputs(Path(repo).resolve())
    destination = Path(destination)
    for name, content in files.items():
        path = destination / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(content)
    print(f'recovery snapshot: {len(files)} changed output files', flush=True)
    return files


def preserve_outputs(worktree, files):
    for name, content in sorted(files.items()):
        path = worktree / name
        if path.exists():
            old = path.read_bytes()
            if old == content:
                continue
            if name.startswith('ledger/') and path.suffix == '.jsonl':
                # Reruns may extend the same run ledger. Preserve its exact old
                # bytes and append only genuinely new rows (not duplicated prefixes).
                seen = {json.dumps(json.loads(line), sort_keys=True) for line in old.splitlines() if line.strip()}
                extra = []
                for line in content.splitlines():
                    if not line.strip():
                        continue
                    key = json.dumps(json.loads(line), sort_keys=True)
                    if key not in seen:
                        extra.append(line)
                        seen.add(key)
                content = old + (b'\n' if old and not old.endswith(b'\n') else b'')
                content += b''.join(line + b'\n' for line in extra)
            elif name.startswith('verified/') and path.suffix == '.lean':
                sha = hashlib.sha256(content).hexdigest()
                path = path.with_name(f'{path.stem}.{sha}.lean')
                if path.exists() and path.read_bytes() != content:
                    raise RuntimeError(f'Content-address collision: {path}')
                print(f'preserved both accepted proofs: {name} + {path.name}', flush=True)
            else:
                raise RuntimeError(f'Unexpected output collision: {name}; recover from artifact')
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(content)


def publish(repo, message, attempts=3, before_push=None):
    repo = Path(repo).resolve()
    files = changed_outputs(repo)
    if not files:
        print('nothing to publish', flush=True)
        return None
    # Retained until runner teardown, including failed worktrees; never reset or
    # delete the original attempt checkout or its output files.
    staging = Path(tempfile.mkdtemp(prefix='sparebrains-publish-'))
    for attempt in range(1, attempts + 1):
        print(f'publication {attempt}/{attempts}: fetch latest main; {len(files)} output files', flush=True)
        git(repo, 'fetch', 'origin', 'main')
        base = git(repo, 'rev-parse', 'FETCH_HEAD').stdout.strip()
        worktree = staging / str(attempt)
        git(repo, 'worktree', 'add', '--detach', str(worktree), base)
        preserve_outputs(worktree, files)
        git(worktree, 'add', '--', 'ledger', 'verified')
        if git(worktree, 'diff', '--cached', '--quiet', check=False).returncode == 0:
            print('all outputs already published', flush=True)
            return base
        git(worktree, 'commit', '-m', message)
        if before_push:
            before_push(attempt)  # test seam: move local fixture remote after fetch
        result = git(worktree, 'push', 'origin', 'HEAD:main', check=False)
        if result.returncode == 0:
            sha = git(worktree, 'rev-parse', 'HEAD').stdout.strip()
            print(f'published {sha}; source outputs preserved', flush=True)
            return sha
        git(repo, 'fetch', 'origin', 'main')
        if git(repo, 'rev-parse', 'FETCH_HEAD').stdout.strip() == base:
            # Nothing raced us, so the server refused: GitHub's 5xx pass, and a push of the same commit is idempotent.
            if attempt == attempts:
                raise RuntimeError(f'Push failed without a competing commit after {attempts} attempts; outputs retained '
                                   f'at {staging} and in the workflow artifact: {result.stderr[-1500:]}')
            print(f'push refused with no competing commit; retrying in {BACKOFF_S * attempt}s: {result.stderr[-300:]}', flush=True)
            time.sleep(BACKOFF_S * attempt)
            continue
        print('main advanced during publish; retrying on the new head', flush=True)
    raise RuntimeError(f'Publication still competing after {attempts} attempts; outputs retained at {staging} and in the workflow artifact')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--message')
    mode.add_argument('--snapshot', type=Path)
    args = parser.parse_args()
    repo = Path(__file__).resolve().parent.parent
    if args.snapshot:
        snapshot_outputs(repo, args.snapshot)
    else:
        publish(repo, args.message)
