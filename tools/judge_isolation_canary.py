"""Proves in Actions that a candidate cannot read a secret. Needs tools/judge_sandbox.sh first
and SB_CANARY set. The probe must find the canary when Lean runs as this job's user (else it is
blind and a clean result means nothing), then must not find it as the judge user."""
import os, re, sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
from check import judge

PROBE = Path(__file__).parent.parent / "checks/canary/env_leak_probe.lean"
SECRET = os.environ["SB_CANARY"]
USER = os.environ["SB_JUDGE_USER"]


def probe(user):
    saved = dict(os.environ)
    os.environ.pop("SB_JUDGE_USER", None)
    if user:
        os.environ["SB_JUDGE_USER"] = user
    try:
        out = judge(str(PROBE), 300)[3]
    finally:
        os.environ.clear()
        os.environ.update(saved)
    m = re.search(r"PROBE scanned (\d+) hits (\d+)", out)
    if not m:
        sys.exit(f"the probe did not run, so the verdict is meaningless:\n{out[-2000:]}")
    return int(m[1]), int(m[2]), SECRET in out


scanned, hits, leaked = probe(None)
print(f"as the job's user: {scanned} environ files read, {hits} hits, secret in output: {leaked}")
if not leaked:
    sys.exit("the probe cannot see the canary even unsandboxed: it is blind, so stop here")
scanned, hits, leaked = probe(USER)
print(f"as {USER}: {scanned} environ files read, {hits} hits, secret in output: {leaked}")
if scanned == 0:
    sys.exit(f"{USER} read no environ files at all: verdict meaningless")
if leaked or hits:
    sys.exit(f"LEAK: {USER} can see the secret")
print("isolation holds")
