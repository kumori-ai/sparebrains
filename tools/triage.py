"""The weekly failure triage (2026-10-24; DECISIONS.md): which answered failures, across every lane, are worth a
tool. A class is a lane's failure_kind on answered rejects (non-answers, lane errors and fixer re-judges left out;
no label = unclassified). A candidate is >=LANE_SHARE of some lane's rejects with that lane's n>=LANE_MIN, or among
the TOP cross-lane totals; ranked by its cross-lane total (demand), the last closed week beside it. Frozen replies
(ledger/replay/) refine a class by reply signature in a separate column, with its coverage; they never move a rank.
It ranks; a person or session picks a candidate and builds under the replay rules (tools/replay.py).

    python3 tools/triage.py                     # the last closed week's page, if not there yet
    python3 tools/triage.py --today 2026-10-27
"""
import argparse, gzip, hashlib, json, re, subprocess, sys
from collections import Counter, defaultdict
from datetime import date, datetime, timedelta, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT), str(ROOT / "tools")]
import ledger_files
from proof_text import FENCE, LEAN3_BEGIN, PROOF_SEP, recover_lean3
from retro import last_closed_week, week_of

LANE_SHARE, LANE_MIN, TOP = 0.4, 100, 5
COHORTS = {"groq-allam": "groq-allam-ladder-x3-2026-10-24.jsonl.gz"}   # lane -> frozen replies in ledger/replay/
COVERED_BY = {"lean3_syntax": "fixer lean3 pass", "unknown_name": "fixer names pass",
              "unsolved_goals": "the loop's holes and automation", "no_fence": "proof_text.recover_lean3 (lean3_body)"}


def answered_rejects(rows):
    """[{lane, class, ts}] for every answered reject: lane = backend, else lane (ledger/fc), else unattributed."""
    out = []
    for r in rows:
        if r.get("verdict") != "reject" or str(r.get("try_mode") or "").startswith("fixer"):
            continue
        out.append({"lane": r.get("backend") or r.get("lane") or "unattributed",
                    "class": r.get("failure_kind") or "unclassified", "ts": r.get("ts") or "",
                    "run_id": str(r.get("run_id")), "target_set": r.get("target_set"), "target": r.get("target"),
                    "attempt_no": r.get("attempt_no")})
    return out


def signature(reply, name):
    """One primary signature per reply, by precedence, and truncation as a flag apart."""
    got = recover_lean3(reply or "", name)
    if got:
        return {"primary": "lean3_body", "truncated": "truncated_closed" in got[1]}
    i = (reply or "").find(f"theorem {name}")
    nxt = re.search(r"\n\s*(?:theorem|lemma)\s", reply[i + 1:]) if i >= 0 else None
    end = i + 1 + nxt.start() if nxt else len(reply or "")
    if i >= 0 and LEAN3_BEGIN.search(reply, i, end):       # Lean 3 in this declaration, cut off before a line was kept
        return {"primary": "lean3_body", "truncated": True}
    if any(f"theorem {name}" in b or PROOF_SEP.search(b) for b in FENCE.findall(reply or "")):
        return {"primary": "fenced_lean4", "truncated": False}
    if re.search(rf"theorem {re.escape(name)}\b[\s\S]*?:=\s*by\b", reply or ""):
        return {"primary": "unfenced_lean4", "truncated": False}
    return {"primary": "prose", "truncated": False}


def refine(lane, cls, cohort, rejects, cutoff):
    """A class's frozen replies for one lane, matched to this page's ledger attempts by (run, set, target, attempt,
    class) and by count, so coverage never exceeds the attempts it matches: cohort rows past the cutoff are left out
    (after_cutoff), rows with no ledger attempt left are database-only (Codex 20261024T193402083246Z)."""
    left = Counter((r["run_id"], r["target_set"], r["target"], r["attempt_no"]) for r in rejects
                   if r["lane"] == lane and r["class"] == cls)
    seen, sigs, trunc, db_only, late = set(), Counter(), 0, 0, 0
    for r in sorted(cohort, key=lambda r: r["id"]):
        if r["id"] in seen or r.get("verdict") != "reject" or (r.get("failure_kind") or "unclassified") != cls:
            continue
        seen.add(r["id"])
        if (r.get("created_at") or "")[:10] >= cutoff:
            late += 1
            continue
        key = (str(r.get("run_id")), r.get("target_set"), r["target"], r.get("attempt_no"))
        if left[key] <= 0:
            db_only += 1
            continue
        left[key] -= 1
        s = signature(r.get("response"), r["target"])
        sigs[s["primary"]] += 1
        trunc += s["truncated"]
    return {"lane": lane, "covered": sum(sigs.values()), "db_only": db_only, "after_cutoff": late,
            "signatures": dict(sigs), "truncated": trunc}


def queue(rejects, week, cohorts=None):
    cutoff = date.fromisocalendar(*week, 7) + timedelta(days=1)
    rejects = [r for r in rejects if not r["ts"] or r["ts"][:10] < cutoff.isoformat()]
    lane_n, per, total, wk = Counter(), defaultdict(Counter), Counter(), Counter()
    for r in rejects:
        lane_n[r["lane"]] += 1
        per[r["class"]][r["lane"]] += 1
        total[r["class"]] += 1
        if r["ts"] and week_of(r["ts"]) == tuple(week):
            wk[r["class"]] += 1
    top = {c for c, _ in sorted(total.items(), key=lambda kv: (-kv[1], kv[0]))[:TOP]}
    cands = []
    for cls, by_lane in per.items():
        bar = sorted(l for l, v in by_lane.items() if l != "unattributed" and lane_n[l] >= LANE_MIN
                     and v >= LANE_SHARE * lane_n[l])
        if not bar and cls not in top:
            continue
        c = {"class": cls, "total": total[cls], "week": wk[cls], "lanes": dict(by_lane), "passes_lane_bar": bar,
             "in_top": cls in top, "existing_tool": COVERED_BY.get(cls), "recoverability": "unknown"}
        refs = [refine(l, cls, rows, rejects, cutoff.isoformat()) for l, rows in (cohorts or {}).items()]
        refs = [x for x in refs if x["covered"] or x["db_only"]]
        if refs:
            c["refined"] = {"covered": sum(x["covered"] for x in refs), "of": total[cls], "by_lane": refs}
        cands.append(c)
    cands.sort(key=lambda c: (-c["total"], c["class"]))
    return {"week": list(week), "cutoff": cutoff.isoformat(), "rejects": len(rejects), "lanes": len(lane_n),
            "unclassified": total["unclassified"], "unattributed": lane_n["unattributed"], "candidates": cands}


def render(q):
    lines = [f"# Failure triage {q['week'][0]}-W{q['week'][1]:02d} (answered rejects to {q['cutoff']})", "",
             f"Read from the ledger by tools/triage.py: {q['rejects']:,} answered rejects over {q['lanes']} lanes "
             f"({q['unclassified']:,} unclassified, {q['unattributed']:,} unattributed). Ranked by cross-lane demand; "
             f"a candidate is >={int(LANE_SHARE * 100)}% of some lane's rejects (lane n>={LANE_MIN}) or in the top "
             f"{TOP}. Recoverability is unknown until a replay measures it.", "",
             "| class | all lanes | last week | lanes | past a lane's bar | existing tool | frozen replies, by signature |",
             "|---|---:|---:|---:|---|---|---|"]
    for c in q["candidates"]:
        ref = c.get("refined")
        refs = "; ".join(f"{x['lane']}: {x['covered']} of {c['lanes'].get(x['lane'], 0)} ("
                         + ", ".join(f"{k} {v}" for k, v in sorted(x["signatures"].items()))
                         + f"; {x['truncated']} truncated; {x['db_only']} database-only)" for x in ref["by_lane"]) if ref else "-"
        lines.append(f"| {c['class']} | {c['total']:,} | {c['week']:,} | {len(c['lanes'])} | "
                     f"{', '.join(c['passes_lane_bar']) or '-'} | {c['existing_tool'] or '-'} | {refs} |")
    return "\n".join(lines) + "\n"


def write_page(q, out_dir, rev, classifier):
    """ledger/retro/<year>-W<week>-triage.md and .json, written once with their input boundary."""
    page = Path(out_dir) / f"{q['week'][0]}-W{q['week'][1]:02d}-triage.md"
    if page.exists():
        return None
    page.parent.mkdir(parents=True, exist_ok=True)
    page.write_text(render(q))
    page.with_suffix(".json").write_text(json.dumps({**q, "ledger_rev": rev, "classifier": classifier}, indent=1) + "\n")
    return page


def load_cohorts():
    out = {}
    for lane, f in COHORTS.items():
        p = ROOT / "ledger" / "replay" / f
        if p.exists():
            with gzip.open(p, "rt") as fh:
                out[lane] = [json.loads(l) for l in fh if l.strip()]
    return out


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--today", default=datetime.now(timezone.utc).date().isoformat())
    ap.add_argument("--out", default=str(ROOT / "ledger" / "retro"))
    a = ap.parse_args(argv)
    rows = []
    for f in sorted(ledger_files.try_files(ROOT / "ledger")):
        for line in f.read_text().splitlines():
            try:
                rows.append(json.loads(line))
            except ValueError:
                pass
    q = queue(answered_rejects(rows), last_closed_week(a.today), load_cohorts())
    rev = subprocess.run(["git", "rev-parse", "HEAD"], capture_output=True, text=True, cwd=ROOT).stdout.strip()
    classifier = hashlib.sha256(b"".join((ROOT / "tools" / f).read_bytes() for f in ("triage.py", "proof_text.py"))).hexdigest()[:10]
    page = write_page(q, a.out, rev, classifier)
    print(f"triage {q['week']}: {len(q['candidates'])} candidates from {q['rejects']:,} answered rejects; "
          + (f"wrote {page.name}" if page else "page already there"))
    return 0


if __name__ == "__main__":
    sys.exit(main())
