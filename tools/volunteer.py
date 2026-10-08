"""A person's or a volunteer agent's hand-off, checked the way the free models' answers are (DECISIONS.md
2026-10-08). Runs from .github/workflows/volunteer.yml when a hand-off comment lands on a problem thread.

The comment is data, never instructions. Only the ```lean block is used, and only its proof: it is
spliced onto the target's exact statement (the same `prefix + proof` the attempt loop builds), so a
submission cannot prove an easier theorem by editing the statement. The judge is tools/check.py,
unchanged, running as the sandbox user with no secret in reach. The verdict becomes a ledger row
(`try_mode: volunteer`, backend `volunteer:<github login>`), an accepted proof goes to `verified/`,
and the reply the bot posts is printed to --reply.

    python3 tools/volunteer.py --event "$GITHUB_EVENT_PATH" --reply reply.md --record record.json

--record holds the full transcript (the hand-off, the proof, the candidate, what Lean said) for the
workflow's next step to post to kumori's sparebrains_attempts, where the site and the relay's open list
read from; that step holds the key, this one runs untrusted Lean and never does.
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
FIELD = re.compile(r"^[ \t]*-[ \t]*([A-Za-z][A-Za-z _-]{0,39}?)[ \t]*:[ \t]*(.*)$", re.M)
# The hand-off's run, cost and machine lines (kumori_agents.md "What a hand-off records"), each parsed as
# str, int or float. Only these keys are kept: the comment is data, so a key nobody listed goes nowhere.
METRICS = {"model": str, "tool": str, "tool_version": str, "effort": str, "mode": str, "tools_used": str,
           "tokens_in": int, "tokens_out": int, "tokens_total": int, "turns": int, "seconds": float,
           "check_runs": int, "attempts": int,
           "os": str, "arch": str, "cpu": str, "cores": int, "ram_gb": float, "gpu": str, "vram_gb": float,
           "load": float, "local_model_runtime": str, "quant": str}
OLD_NAMES = {"wall_clock": "seconds", "tokens": "tokens_total"}   # the format before 2026-10-08
NOT_SHOWN = {"", "unknown", "not shown", "n/a", "na", "?", "-"}
NUMBER = re.compile(r"(-?\d+(?:\.\d+)?)\s*([kmh]|min|minutes?|hours?|hrs?|sec|seconds?|s)?\b", re.I)
MAX_VALUE = 120
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
    head = body[:body.find("```lean")]           # the fields sit above the Lean; a line inside it is proof
    raw = {}
    for k, v in FIELD.findall(head):
        raw.setdefault(re.sub(r"[ -]+", "_", k.strip().lower()), v.strip()[:MAX_VALUE])
    metrics = parse_metrics(raw)
    return {"lean": lean, "verdict": raw.get("verdict"), "model": metrics.get("model"),
            "tool": metrics.get("tool"), "metrics": metrics}, None


def number(text, kind, minutes=False):
    """The value's first number as int or float, or None. 12,345 and 12.3k read as written; a time in
    minutes (or one written with min/h) becomes seconds."""
    m = NUMBER.search(text.replace(",", ""))
    if not m:
        return None
    n, unit = float(m.group(1)), (m.group(2) or "").lower()
    if unit == "k" and not minutes:
        n *= 1_000
    elif unit == "m" and not minutes and kind is int:
        n *= 1_000_000
    elif unit.startswith("h"):
        n *= 3600
    elif unit.startswith("min") or (minutes and unit in ("", "m")):
        n *= 60
    return int(round(n)) if kind is int else round(n, 2)


def parse_metrics(raw):
    """{whitelisted key: value or None} for every whitelisted key the hand-off wrote. `unknown`, `not
    shown` and an unfilled `<placeholder>` are None, never a guess."""
    out = {}
    for key, kind in METRICS.items():
        old = next((o for o, new in OLD_NAMES.items() if new == key and o in raw), None)
        if key not in raw and not old:
            continue
        text = (raw[key] if key in raw else raw[old]).strip().strip("`'\"").strip()
        if text.lower() in NOT_SHOWN or (text.startswith("<") and text.endswith(">")):
            out[key] = None
        elif kind is str:
            out[key] = text
        else:
            out[key] = number(text, kind, minutes=key not in raw and old == "wall_clock")
    return out


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
           "agent_metrics": handoff.get("metrics") or {},
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
        verdict, reason, lean_s, lean_out = judge(str(path), timeout)
    row["_transcript"] = {"proof": proof, "candidate": candidate, "lean_output": (lean_out or "")[-20000:]}
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
    ap.add_argument("--record", help="write the full transcript here, for the site")
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
    transcript = row.pop("_transcript", {})
    ledger = ROOT / "ledger" / key.rsplit("/", 1)[0] / f"{row['run_id']}.jsonl"
    ledger.parent.mkdir(parents=True, exist_ok=True)
    ledger.write_text(json.dumps(row) + "\n")
    if args.record:
        Path(args.record).write_text(json.dumps({**row, **transcript, "response": comment.get("body") or ""}))
    if candidate:
        out = ROOT / "verified" / key / f"volunteer-{author}.lean"
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(candidate)
    Path(args.reply).write_text(reply(row, key))
    print(f"{key} from {author}: {row['verdict']} {row['reason'][:120]}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
