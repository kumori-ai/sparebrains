"""Stalled problems: open, and nothing kernel-verified on them for DAYS days (DECISIONS.md 2026-11-09, the stall router).

Progress is an accepted solve or a new distinct verified lemma (lemma-accept rows, told apart by lemma_sha, or by
their 600-char text on rows from before the hash). A reject's error position is never progress: the same failing
proof with blank lines added moves its first error (Codex 20261109T204513251417Z f3). A stalled problem is the one
the stall router hands to the next tool (today: the guide's blueprint, tools/blueprint.py) instead of more of the same
tries; the daily report lists them.
"""
from collections import Counter, defaultdict
from datetime import datetime

DAYS = 14
JUDGED = ("accept", "reject", "error")


def _ts(r):
    return r.get("ts") or r.get("created_at") or ""


def progress(rows):
    """{(target_set, target): sorted timestamps of its verified progress events}."""
    seen, out = set(), defaultdict(list)
    for r in sorted(rows, key=_ts):
        key = (r.get("target_set"), r.get("target"))
        if r.get("verdict") == "accept":
            out[key].append(_ts(r))
        elif r.get("verdict") == "lemma-accept":
            ident = (key, r.get("lemma_sha") or r.get("lemma"))
            if ident not in seen:
                seen.add(ident)
                out[key].append(_ts(r))
    return out


def stalled(rows, open_keys, now, days=DAYS):
    """[{target_set, target, rung, idle_days, last_progress, tries, lanes, paths}] for the open problems idle `days`
    or more, most idle first. idle counts from the last progress event, else from the first try; a problem with no
    rows at all is idle forever (idle_days None) and listed first."""
    prog, by = progress(rows), defaultdict(list)
    for r in rows:
        if r.get("verdict") in JUDGED:
            by[(r.get("target_set"), r.get("target"))].append(r)
    out = []
    for key in open_keys:
        tries = by.get(key, [])
        if any(r.get("verdict") == "accept" for r in tries):     # solved is never stalled, whatever the open list says
            continue
        last = max(prog.get(key, []), default=None)
        since = last or min((_ts(r) for r in tries), default=None)
        idle = None if not since else int((now - datetime.fromisoformat(since)).total_seconds() // 86400)
        if idle is not None and idle < days:
            continue
        out.append({"target_set": key[0], "target": key[1], "rung": next((r.get("rung") for r in tries if r.get("rung")), None),
                    "idle_days": idle, "last_progress": last, "tries": len(tries),
                    "lanes": len({r.get("backend") for r in tries}),
                    "paths": dict(Counter(r.get("try_mode") or "cold" for r in tries))})
    return sorted(out, key=lambda s: -(s["idle_days"] if s["idle_days"] is not None else 10 ** 9))
