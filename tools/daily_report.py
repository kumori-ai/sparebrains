"""The daily school report: what every student (lane) did in the last 24 hours, by grade, read from the ledger alone.

Grades are the target sets the ladder climbs: kindergarten (primer), middle school (Mathematics in Lean), high school
(miniF2F, by competition rung) and college (formal-conjectures, openproblems.bio). For each grade: who answered, who
passed a problem first, the top performers; then the tool-lift series (ledger/speed, this week beside last), the
Kaggle prover batches, the relay's backoff and how many days each rung has sat idle. One JSON and one markdown a day
under ledger/daily/; the issues workflow posts the markdown as the daily log comment and kumori's morning mail
renders the JSON. Counts and receipts only, nothing a reader has to trust.

    python3 tools/daily_report.py                        # writes ledger/daily/<today>.{json,md}
    python3 tools/daily_report.py --now 2026-10-28T12:00:00+00:00 --out /tmp/daily
"""
import argparse, json, sys
import ledger_files
from collections import Counter, defaultdict
from datetime import datetime, timedelta, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
GRADES = (("kindergarten", "primer"), ("middle school", "mil"), ("high school", "minif2f/test"), ("college", None))
COLLEGE = ("formal-conjectures", "openproblems.bio")
TOP = 5
MIN_ANSWERED = 3        # a lane with fewer answered tries in the window is listed, never ranked


def grade_of(target_set):
    for g, s in GRADES:
        if s == target_set:
            return g
    return "college"


def _ts(r):
    return r.get("ts") or r.get("at") or ""


def _load_jsonl(path):
    out = []
    for f in sorted(Path(path).glob("*.jsonl")) if Path(path).is_dir() else ([Path(path)] if Path(path).exists() else []):
        for line in f.read_text().splitlines():
            try:
                out.append(json.loads(line))
            except ValueError:
                continue
    return out


def tries(ledger):
    rows = []
    for f in ledger_files.try_files(ledger):
        for line in f.read_text().splitlines():
            try:
                r = json.loads(line)
            except ValueError:
                continue
            if isinstance(r, dict) and all(r.get(k) for k in ("ts", "target", "mode", "verdict")):
                rows.append(r)
    return sorted(rows, key=lambda r: r["ts"])


def grades(rows, since):
    """Per grade: the lanes of the window ranked by accepts then answered, first solves, solved and open counts."""
    first_ever, solved, seen = {}, defaultdict(set), defaultdict(set)
    lanes = defaultdict(lambda: defaultdict(lambda: {"answered": 0, "accepts": 0, "tier": "?"}))
    firsts = []
    for r in rows:
        key, g = f"{r.get('target_set') or ''}/{r['target']}", grade_of(r.get("target_set"))
        seen[g].add(key)
        if r["verdict"] == "accept":
            solved[g].add(key)
            if key not in first_ever:
                first_ever[key] = r["ts"]
                if r["ts"] > since:
                    firsts.append({"grade": g, "key": key, "lane": r.get("backend") or "?", "tier": r.get("quality_tier") or "?",
                                   "mode": r["mode"], "ts": r["ts"]})
        if r["ts"] > since and r["verdict"] in ("accept", "reject"):
            l = lanes[g][r.get("backend") or "?"]
            l["answered"] += 1
            l["accepts"] += r["verdict"] == "accept"
            l["tier"] = r.get("quality_tier") or l["tier"]
    out = []
    for g, _ in GRADES:
        ranked = sorted(lanes[g].items(), key=lambda x: (-x[1]["accepts"], -x[1]["answered"], x[0]))
        out.append({"grade": g, "solved": len(solved[g]), "open": len(seen[g] - solved[g]),
                    "answered": sum(l["answered"] for l in lanes[g].values()), "accepts": sum(l["accepts"] for l in lanes[g].values()),
                    "lanes": [dict(v, lane=k) for k, v in ranked],
                    "first_solves": [f for f in firsts if f["grade"] == g]})
    return out, firsts


def speed(ledger):
    """The size series (task #191): per lane and run week, targets tried, first accepts, refusals; beside the week before."""
    by = defaultdict(lambda: {"targets": set(), "accepted": set(), "refused": 0, "size_b": None})
    for r in _load_jsonl(Path(ledger) / "speed"):
        if "run_week" not in r or "lane" not in r:
            continue
        s = by[(r["lane"], r["run_week"])]
        s["size_b"] = r.get("size_b")
        s["targets"].add(r.get("target"))
        if r.get("verdict") == "accept":
            s["accepted"].add(r.get("target"))
        elif r.get("verdict") == "refused":
            s["refused"] += 1
    if not by:
        return []
    latest = max(w for _, w in by)
    out = []
    for (lane, w), s in sorted(by.items()):
        if w != latest:
            continue
        prev = sorted((pw for (pl, pw) in by if pl == lane and pw < w), reverse=True)
        p = by[(lane, prev[0])] if prev else None
        out.append({"lane": lane, "size_b": s["size_b"], "week": w, "targets": len(s["targets"]), "accepted": len(s["accepted"]),
                    "refused": s["refused"], "prev_week": prev[0] if prev else None,
                    "prev_targets": len(p["targets"]) if p else 0, "prev_accepted": len(p["accepted"]) if p else 0})
    return sorted(out, key=lambda s: (s["size_b"] if s["size_b"] is not None else 1e9, s["lane"]))


def kaggle(ledger, since):
    fin = [b for b in _load_jsonl(Path(ledger) / "prover-batches.jsonl") if (b.get("finished_at") or "") > since]
    failed = [b for b in _load_jsonl(Path(ledger) / "prover-beats" / "failed.jsonl") if (b.get("first_seen_at") or "") > since]
    return {"finished": [{"batch": b["batch"], "answers": b.get("answers"), "finished_at": b["finished_at"]} for b in fin],
            "failed": [{"batch": b["batch"], "status": b.get("status"), "first_seen_at": b["first_seen_at"]} for b in failed]}


def relay_state(ledger):
    jobs = sorted(Path(ledger).glob("relay-jobs/*.json"))
    if not jobs:
        return {"backed_off": None, "last": None}
    j = json.loads(jobs[-1].read_text()) if jobs[-1].read_text().strip() else {}
    j = max((json.loads(f.read_text()) for f in jobs if f.read_text().strip()), key=lambda x: x.get("ts", ""), default=j)
    return {"backed_off": bool(j.get("backed_off")), "last": j.get("ts")}


def _days(now, ts):
    return round((now - datetime.fromisoformat(ts)).total_seconds() / 86400, 1) if ts else None


def rungs(ledger, rows, now, since):
    """How long each rung has been idle, and what the college rungs did."""
    last = {}
    for r in rows:
        last[r["mode"]] = max(last.get(r["mode"], ""), r["ts"])
    out = [{"rung": "competition math (ladder)", "last": last.get("ladder-x3"), "idle_days": _days(now, last.get("ladder-x3"))},
           {"rung": "relay", "last": last.get("relay"), "idle_days": _days(now, last.get("relay"))},
           {"rung": "prover", "last": last.get("prover"), "idle_days": _days(now, last.get("prover"))},
           {"rung": "goal-closer", "last": last.get("goal-closer"), "idle_days": _days(now, last.get("goal-closer"))}]
    fc = _load_jsonl(Path(ledger) / "fc")
    fc_last = max((_ts(r) for r in fc), default=None)
    out.append({"rung": "formal-conjectures", "last": fc_last, "idle_days": _days(now, fc_last),
                "tries_24h": sum(_ts(r) > since for r in fc), "accepts_ever": sum(r.get("verdict") == "accept" for r in fc)})
    ev = [r for r in _load_jsonl(Path(ledger) / "openproblems") if r.get("round") is not None]
    ev_last = max((_ts(r) for r in ev), default=None)
    scored = [r for r in ev if isinstance(r.get("metrics"), dict) and "rmse" in r["metrics"]]
    # The bar is the leave-one-site-out qualify (both directions, rmse and Pearson, every site), never a screen score:
    # the best evolve rmse (0.8916 vs 0.9684, 2026-10-21) came from one split and its candidate failed qualify on Pearson.
    quals = sorted((json.loads(f.read_text()) for f in Path(ledger).glob("openproblems/qualify-*.json")), key=_ts)
    q = quals[-1] if quals else None
    out.append({"rung": "openproblems.bio", "last": ev_last, "idle_days": _days(now, ev_last), "rounds_24h": sum(_ts(r) > since for r in ev),
                "scored": len(scored), "crashed": sum("error" in r for r in ev), "qualify_runs": len(quals),
                "qualify": {"at": q["at"], "passed": bool(q["verdict"].get("passed")), "sites": q["verdict"].get("sites"),
                            "mean_pearson_delta": q["verdict"].get("mean_pearson_delta")} if q and q.get("verdict") else None})
    return out


def build(ledger, now, hours=24):
    ledger = Path(ledger)
    rows = tries(ledger) if ledger.exists() else []
    if not rows:
        sys.exit(f"no ledger rows under {ledger}: a report of nothing would read as a quiet day")
    since = (now - timedelta(hours=hours)).isoformat()
    window = [r for r in rows if r["ts"] > since]
    judged = [r for r in window if r["verdict"] in ("accept", "reject", "error")]
    answered = [r for r in judged if r["verdict"] != "error"]
    g, firsts = grades(rows, since)
    errors = Counter("upstream timeout (504)" if "HTTP 504" in (r.get("reason") or "") else
                     "router 5xx" if "HTTP 5" in (r.get("reason") or "") else "other error"
                     for r in judged if r["verdict"] == "error")
    return {"day": f"{now:%Y-%m-%d}", "to": now.isoformat(), "hours": hours,
            "totals": {"judged": len(judged), "answered": len(answered), "accepted": sum(r["verdict"] == "accept" for r in answered),
                       "errors": dict(errors),
                       "lanes": len({r.get("backend") for r in judged}), "problems": len({(r.get("target_set"), r["target"]) for r in judged}),
                       "solved_ever": sum(x["solved"] for x in g), "open": sum(x["open"] for x in g)},
            "first_solves": sorted(firsts, key=lambda f: f["ts"]), "grades": g, "speed": speed(ledger),
            "kaggle": kaggle(ledger, since), "relay": relay_state(ledger), "rungs": rungs(ledger, rows, now, since)}


def render(d):
    t, out = d["totals"], []
    out += [f"**{d['day']}** (the {d['hours']} hours to {d['to'][11:16]} UTC): **{len(d['first_solves'])} first-time solves**, "
            f"{t['accepted']} accepts from {t['answered']} answered tries by {t['lanes']} lanes on {t['problems']} problems. "
            f"{t['solved_ever']} problems solved ever, {t['open']} open.", ""]
    if t.get("errors"):
        out += ["Lost before the kernel: " + ", ".join(f"{n} {k}" for k, n in sorted(t["errors"].items(), key=lambda x: -x[1])), ""]
    for f in d["first_solves"]:
        out.append(f"- first solve: `{f['key']}` by {f['lane']} ({f['tier']}, {f['mode']})")
    if d["first_solves"]:
        out.append("")
    out += ["| grade | solved / open | answered | accepts | top performers (accepts/answered) |", "|---|---:|---:|---:|---|"]
    for g in d["grades"]:
        ranked = [l for l in g["lanes"] if l["answered"] >= MIN_ANSWERED][:TOP]
        top = ", ".join(f"{l['lane']} {l['accepts']}/{l['answered']}" for l in ranked) or "nobody answered"
        out.append(f"| {g['grade']} | {g['solved']} / {g['open']} | {g['answered']} | {g['accepts']} | {top} |")
    if d["speed"]:
        out += ["", "**Tool lift, same models, this week's tools** (ledger/speed; first accepts on the frozen solved set):", "",
                "| lane | size | this week | week before | refused |", "|---|---:|---:|---:|---:|"]
        for s in d["speed"]:
            prev = f"{s['prev_accepted']}/{s['prev_targets']}" if s["prev_week"] else "none"
            out.append(f"| {s['lane']} | {s['size_b'] or '?'}B | {s['accepted']}/{s['targets']} | {prev} | {s['refused']} |")
    k = d["kaggle"]
    if k["finished"] or k["failed"]:
        out += ["", "**Kaggle prover batches:** " + "; ".join([f"{b['batch']} finished, {b['answers']} answers" for b in k["finished"]] +
                                                        [f"{b['batch']} FAILED" for b in k["failed"]])]
    out += ["", "| rung | last activity | idle days |", "|---|---|---:|"]
    for r in d["rungs"]:
        extra = ""
        if r["rung"] == "openproblems.bio":
            q = r.get("qualify")
            bar = (f"last qualify {'PASSED' if q['passed'] else 'missed'} {q['at'][:10]} (Pearson delta {q['mean_pearson_delta']:+.3f} over {q['sites']} sites)"
                   if q else "no qualify run yet")
            extra = f" ({r['scored']} candidates scored, {r['crashed']} crashed; {bar})"
        if r["rung"] == "formal-conjectures":
            extra = f" ({r['accepts_ever']} accepts ever)"
        out.append(f"| {r['rung']}{extra} | {(r['last'] or 'never')[:16]} | {r['idle_days'] if r['idle_days'] is not None else '-'} |")
    if d["relay"]["backed_off"]:
        out += ["", "Relay is backed off: it asks again only on a wake (a person's comment, a new lane, the daily probe)."]
    return "\n".join(out) + "\n"


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--ledger", default=str(ROOT / "ledger"))
    ap.add_argument("--out", default=str(ROOT / "ledger" / "daily"))
    ap.add_argument("--now", default=datetime.now(timezone.utc).isoformat())
    ap.add_argument("--hours", type=int, default=24)
    a = ap.parse_args(argv)
    d = build(a.ledger, datetime.fromisoformat(a.now), a.hours)
    out = Path(a.out)
    out.mkdir(parents=True, exist_ok=True)
    (out / f"{d['day']}.json").write_text(json.dumps(d, indent=1, sort_keys=True) + "\n")
    (out / f"{d['day']}.md").write_text(render(d))
    print(f"wrote {out / d['day']}.{{json,md}}: {len(d['first_solves'])} first-time solves, {d['totals']['accepted']} accepts")
    return 0


if __name__ == "__main__":
    sys.exit(main())
