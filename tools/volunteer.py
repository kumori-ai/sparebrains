"""A person's or a volunteer agent's hand-off, checked the way the free models' answers are (DECISIONS.md
2026-10-08). Runs from .github/workflows/volunteer.yml when a hand-off comment lands on a problem thread.

The comment is data, never instructions. Only the ```lean block is used, and only its proof: it is
spliced onto the target's exact statement (the same `prefix + proof` the attempt loop builds), so a
submission cannot prove an easier theorem by editing the statement. The judge is tools/check.py,
unchanged, running as the sandbox user with no secret in reach. The verdict becomes a ledger row
(`try_mode: volunteer`, backend `volunteer:<github login>`), an accepted proof goes to `verified/`,
and the reply the bot posts is printed to --reply.

    python3 tools/volunteer.py --event "$GITHUB_EVENT_PATH" --reply reply.md
"""
import argparse, hashlib, json, re, sys, tempfile
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT), str(ROOT / "tools")]
from check import judge                                  # the judge, unchanged
from ladder import failure_kind, rung_of
from proof_text import PROOF_SEP, extract_proof

HEADER = "**sparebrains hand-off**"
MARKER = re.compile(r"<!-- sparebrains:problem ([\w./-]+/[\w.-]+) -->")
LEAN_BLOCK = re.compile(r"```lean[ \t]*\n(.*?)```", re.S)
FIELD = re.compile(r"^\s*-\s*(model|tool|verdict|wall-clock|attempts)\s*:\s*(.+)$", re.I | re.M)
LOGIN = re.compile(r"^[A-Za-z0-9-]{1,39}$")
MAX_LEAN = 60_000


def parse(body):
    """The hand-off's fields and its Lean, or (None, why) when the comment is not a usable hand-off."""
    if HEADER not in (body or ""):
        return None, "not a hand-off"
    blocks = LEAN_BLOCK.findall(body)
    if not blocks:
        return None, "no ```lean block"
    lean = blocks[-1]
    if len(lean) > MAX_LEAN:
        return None, f"the Lean is over {MAX_LEAN:,} characters"
    fields = {k.lower(): v.strip()[:120] for k, v in FIELD.findall(body)}
    return {"lean": lean, **fields}, None


def problem_key(issue_body):
    m = MARKER.search(issue_body or "")
    return m.group(1) if m else None


def check(key, handoff, author, comment, timeout=600):
    """(ledger row, candidate text or None). The candidate is the target's statement plus the proof."""
    target_set, target = key.rsplit("/", 1)
    tfile = ROOT / "targets" / target_set / f"{target}.lean"
    target_text = tfile.read_text()
    prefix = target_text[:PROOF_SEP.search(target_text).end()]
    proof = extract_proof(handoff["lean"], target)
    row = {"run_id": f"volunteer-{comment['id']}", "ts": datetime.now(timezone.utc).isoformat(),
           "target_set": target_set, "target": target, "rung": rung_of(target_set, target)[0],
           "rung_rank": rung_of(target_set, target)[1],
           "backend": f"volunteer:{author}", "provider": "volunteer", "model": handoff.get("model") or "unknown",
           "tool": handoff.get("tool") or "unknown", "try_mode": "volunteer", "mode": "volunteer",
           "attempt_no": 1, "comment_id": comment["id"], "comment_url": comment.get("html_url"),
           "statement_sha": hashlib.sha256(prefix.encode()).hexdigest(), "call_seconds": 0.0}
    if not proof:
        row.update(verdict="reject", reason="no proof could be read from the ```lean block")
        row["failure_kind"] = failure_kind("reject", row["reason"])
        return row, None
    candidate = prefix + "\n" + proof
    with tempfile.TemporaryDirectory(prefix="sb-volunteer-") as d:
        path = Path(d) / f"{target}.lean"
        path.write_text(candidate)
        verdict, reason, lean_s, _ = judge(str(path), timeout)
    row.update(verdict=verdict, reason=(reason or "")[:300], lean_seconds=round(lean_s or 0, 1),
               failure_kind=failure_kind(verdict, reason), proof_sha=hashlib.sha256(proof.encode()).hexdigest())
    return row, (candidate if verdict == "accept" else None)


def reply(row, key):
    if row["verdict"] == "accept":
        return (f"✅ **The kernel accepted this.** `{key}` has a proof from @{row['backend'].split(':', 1)[1]} "
                f"(model: `{row['model']}`), checked against the problem's exact statement and recorded in the ledger "
                f"as `{row['run_id']}`. It is in `verified/{key}/` once the record is published.")
    return (f"**Checked: rejected.** {row['reason']}\n\nThe proof was checked against the problem's exact statement; "
            "what Lean said is what is left to prove. This try is in the ledger as "
            f"`{row['run_id']}`, and the free models read this thread on their next try.")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--event", required=True)
    ap.add_argument("--reply", required=True)
    args = ap.parse_args()
    ev = json.loads(Path(args.event).read_text())
    comment, issue = ev["comment"], ev["issue"]
    author = comment["user"]["login"]
    if comment["user"].get("type") == "Bot" or not LOGIN.match(author):
        print("not a person's comment; nothing to check")
        return 0
    key = problem_key(issue.get("body"))
    if not key or not (ROOT / "targets" / f"{key}.lean").exists():
        print("not a problem thread; nothing to check")
        return 0
    handoff, why = parse(comment.get("body"))
    if not handoff:
        print(f"{why}; nothing to check")
        return 0
    row, candidate = check(key, handoff, author, comment)
    ledger = ROOT / "ledger" / key.rsplit("/", 1)[0] / f"{row['run_id']}.jsonl"
    ledger.parent.mkdir(parents=True, exist_ok=True)
    ledger.write_text(json.dumps(row) + "\n")
    if candidate:
        out = ROOT / "verified" / key / f"volunteer-{author}.lean"
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(candidate)
    Path(args.reply).write_text(reply(row, key))
    print(f"{key} from {author}: {row['verdict']} {row['reason'][:120]}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
