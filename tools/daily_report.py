"""The daily school report: what every student (lane) did since the last report, by grade, read from the ledger alone.

Grades are the target sets the ladder climbs: kindergarten (primer), middle school (Mathematics in Lean), high school
(miniF2F, by competition rung) and college (formal-conjectures, openproblems.bio). For each grade: who answered, who
passed a problem first, the top performers; then the tool-lift series (ledger/speed, this week beside last), the
Kaggle prover batches, the relay's backoff and how many days each rung has sat idle. One JSON and one markdown a day
under ledger/daily/; the issues workflow posts the markdown as the daily log comment and kumori's morning mail
renders the JSON. Counts and receipts only, nothing a reader has to trust.

    python3 tools/daily_report.py                        # writes ledger/daily/<today>.{json,md}
    python3 tools/daily_report.py --now 2026-10-28T12:00:00+00:00 --out /tmp/daily
"""
import argparse, json, re, subprocess, sys
import daily_brief, ledger_files, source_probe
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


def git(top, *args):
    r = subprocess.run(["git", "-C", str(top), *args], capture_output=True, text=True)
    return r.stdout if r.returncode == 0 else None


def canon(r):
    return json.dumps(r, sort_keys=True)


def arrivals(ledger, daily, day):
    """The ledger rows that reached main since the last report of an earlier day was built (#597, 2026-11-03).
    A row's ts is when its run asked, not when it landed: an attempt run (up to 350 min) publishes its rows when it
    ends, so a ts window loses every row stamped before a report and committed after it (run 41564483444: rows from
    02:16Z, committed 07:34Z, the 11-03 report built 02:37Z). Each report records the commit it was built from; the
    next one counts the lines added to the ledger from that commit to HEAD, so each committed row is counted once.
    Returns (Counter of the added rows' canonical JSON, window). (None, reason) only when there is no checkpoint to
    lose rows past: not a git checkout, or no earlier report at all; the caller then uses the ts window. An earlier
    report whose checkpoint cannot be read stops the report (Codex f1, 20261103T212818516158Z): a ts fallback there
    would advance the checkpoint over the rows it missed."""
    top = git(ledger, "rev-parse", "--show-toplevel")
    head = git(ledger, "rev-parse", "HEAD")
    if not top or not head:
        return None, "not a git checkout"
    top, head = Path(top.strip()), head.strip()
    prev = sorted(f for f in Path(daily).glob("*.json") if f.stem < day)
    if not prev:
        return None, "no earlier report"
    win, how = {"kind": "arrived", "from_report": prev[-1].stem}, None
    base = (json.loads(prev[-1].read_text()).get("window") or {}).get("built_from")
    if not base:
        # The transition (reports before 2026-11-04): the parent of the commit that wrote that page. Publish commits
        # it onto a fresh fetch of main, so rows that landed between its checkout and its push sit in that parent but
        # were not read: they are lost once, the residual of this one day.
        wrote = (git(top, "log", "-1", "--format=%H", "--", str(prev[-1].resolve().relative_to(top.resolve()))) or "").strip()
        if not wrote:
            sys.exit(f"{prev[-1]} has no built_from and no commit: no checkpoint, and a ts window would skip rows")
        base, how = f"{wrote}^", f"parent of {wrote[:12]}, the commit that wrote {prev[-1].name} (it predates built_from)"
        base = (git(top, "rev-parse", base) or "").strip()
    if not base or git(top, "merge-base", "--is-ancestor", base, head) is None:
        sys.exit(f"{prev[-1].name}'s checkpoint {base[:12] or '?'} is not in this checkout's history (a shallow clone? "
                 "check out with fetch-depth: 0); a ts window would skip rows, so no report")
    diff = git(top, "diff", "--unified=0", "--no-renames", "--no-color", "--no-ext-diff", base, head, "--",
               str(Path(ledger).resolve().relative_to(top.resolve())))
    if diff is None:
        sys.exit(f"git diff {base[:12]}..{head[:12]} failed: no report rather than one that skips rows (Codex f1, round 2)")
    fresh = Counter()
    for line in diff.splitlines():
        if line.startswith("+") and not line.startswith("+++"):
            try:
                r = json.loads(line[1:])
            except ValueError:
                continue
            if isinstance(r, dict):
                fresh[canon(r)] += 1
    return fresh, {**win, "from": base, **({"base": how} if how else {}), "built_from": head}


def arrived(fresh):
    """since() for an arrival window: a row is in it when an added line carries it. By occurrence, not content (Codex
    f3): two identical rows with one of them added count once. Each row object is decided once and kept alive here, so
    every caller that asks about the same row gets the same answer and an id is never reused."""
    left, seen = Counter(fresh), {}
    def since(r, k=None):
        if id(r) not in seen:
            c = canon(r)
            seen[id(r)] = (r, left[c] > 0)
            left[c] -= left[c] > 0
        return seen[id(r)][1]
    return since


def grades(rows, since):
    """Per grade: the lanes of the window ranked by accepts then answered, first solves, solved and open counts."""
    first_ever, solved, seen = {}, defaultdict(set), defaultdict(set)
    lanes = defaultdict(lambda: defaultdict(lambda: {"answered": 0, "accepts": 0, "tier": "?"}))
    firsts = []
    # A first solve is an accept in the window on a key no earlier-counted row accepted, whatever the ts order: an
    # added row identical to an old accept is in the window by count but is no first solve (Codex f3, round 2)
    before = {f"{r.get('target_set') or ''}/{r['target']}" for r in rows if r["verdict"] == "accept" and not since(r)}
    for r in rows:
        key, g = f"{r.get('target_set') or ''}/{r['target']}", grade_of(r.get("target_set"))
        seen[g].add(key)
        if r["verdict"] == "accept":
            solved[g].add(key)
            if key not in first_ever:
                first_ever[key] = r["ts"]
                if since(r) and key not in before:
                    firsts.append({"grade": g, "key": key, "lane": r.get("backend") or "?", "tier": r.get("quality_tier") or "?",
                                   "mode": r["mode"], "ts": r["ts"]})
        if since(r) and r["verdict"] in ("accept", "reject"):
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
    try:                                                 # #574: the same read off the no-model baseline, beside it
        import replay
        b = replay.no_model_set(ledger)
        base = b["set"] | b.get("unknown", set())     # off = its completed rejects only (Codex f3)
    except ValueError:
        base = None
    by = defaultdict(lambda: {"targets": set(), "accepted": set(), "refused": 0, "size_b": None})
    for r in _load_jsonl(Path(ledger) / "speed"):
        if "run_week" not in r or "lane" not in r:
            continue
        s = by[(r["lane"], r["run_week"])]
        s["size_b"] = r.get("size_b")
        s["targets"].add((r.get("target_set"), r.get("target")))
        if r.get("verdict") == "accept":
            s["accepted"].add((r.get("target_set"), r.get("target")))
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
                    "prev_targets": len(p["targets"]) if p else 0, "prev_accepted": len(p["accepted"]) if p else 0,
                    **({"targets_off": len(s["targets"] - base), "accepted_off": len(s["accepted"] - base)} if base is not None else {})})
    return sorted(out, key=lambda s: (s["size_b"] if s["size_b"] is not None else 1e9, s["lane"]))


def kaggle(ledger, since):
    fin = [b for b in _load_jsonl(Path(ledger) / "prover-batches.jsonl") if since(b, "finished_at")]
    failed = [b for b in _load_jsonl(Path(ledger) / "prover-beats" / "failed.jsonl") if since(b, "first_seen_at")]
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


# kumori 4e0f0c98 (live 2026-11-08 17:25:51Z): the pinned chat answers its own failures as 503 + error_code, written by
# the client into the reason as "HTTP 503 [code] : ..." (kumori shared/kumori_api_client/README.md section 8). Rows
# before it read as Cloudflare's HTML 502/504 and keep their old buckets.
ERROR_CODES = {"upstream_timeout": "upstream timeout", "reasoning_truncated": "reasoning cut at max_tokens",
               "empty_answer": "empty answer", "upstream_error": "upstream error", "deadline_exceeded": "deadline exceeded",
               "call_failed": "call failed"}
CODE = re.compile(r"HTTP \d{3} \[([a-z_]+)\]")


def lost_bucket(reason):
    m = CODE.search(reason)
    if m:
        return ERROR_CODES.get(m.group(1), m.group(1).replace("_", " "))
    return "upstream timeout (504)" if "HTTP 504" in reason else "router 5xx" if "HTTP 5" in reason else "other error"


def rungs(ledger, rows, now, since):
    """How long each rung has been idle, and what the college rungs did."""
    last = {}
    for r in rows:
        last[r["mode"]] = max(last.get(r["mode"], ""), r["ts"])
        # two tools write goal-closer tries: decomposition (Leanstral, mode goal-closer, backend *-decompose) and the
        # prover's GPU goal batches (try_mode goal-closer, retired 2026-11-02); one rung each, so one can't hide the other
        if r["mode"] == "goal-closer" and str(r.get("backend", "")).endswith("-decompose"):
            last["decompose"] = max(last.get("decompose", ""), r["ts"])
        if r.get("try_mode") == "goal-closer":
            last["goal batches (GPU)"] = max(last.get("goal batches (GPU)", ""), r["ts"])
    # a decompose run whose goals all failed writes ledger/decompose/ rows and no try row (2026-11-08: the retro said
    # idle 18.1 days with runs on 11-05 and 11-06 there)
    runs = [_ts(r) for r in _load_jsonl(Path(ledger) / "decompose")]
    last["decompose"] = max([last.get("decompose", "")] + runs) or None
    out = [{"rung": "competition math (ladder)", "last": last.get("ladder-x3"), "idle_days": _days(now, last.get("ladder-x3"))},
           {"rung": "relay", "last": last.get("relay"), "idle_days": _days(now, last.get("relay"))},
           {"rung": "prover", "last": last.get("prover"), "idle_days": _days(now, last.get("prover"))},
           {"rung": "decompose", "last": last.get("decompose"), "idle_days": _days(now, last.get("decompose"))},
           {"rung": "goal batches (GPU)", "last": last.get("goal batches (GPU)"), "idle_days": _days(now, last.get("goal batches (GPU)"))}]
    fc = _load_jsonl(Path(ledger) / "fc")
    fc_last = max((_ts(r) for r in fc), default=None)
    out.append({"rung": "formal-conjectures", "last": fc_last, "idle_days": _days(now, fc_last),
                "tries_24h": sum(map(since, fc)), "accepts_ever": sum(r.get("verdict") == "accept" for r in fc)})
    ev = [r for r in _load_jsonl(Path(ledger) / "openproblems") if r.get("round") is not None and not r.get("rescore")]
    ev_last = max((_ts(r) for r in ev), default=None)
    scored = [r for r in ev if isinstance(r.get("metrics"), dict) and "rmse" in r["metrics"]]
    # The bar is the leave-one-site-out qualify (both directions, rmse and Pearson, every site), never a screen score:
    # the best evolve rmse (0.8916 vs 0.9684, 2026-10-21) came from one split and its candidate failed qualify on Pearson.
    quals = sorted((json.loads(f.read_text()) for f in Path(ledger).glob("openproblems/qualify-*.json")), key=_ts)
    q = quals[-1] if quals else None
    drifts = sorted((json.loads(f.read_text()) for f in Path(ledger).glob("openproblems/drift-*.json")), key=_ts)
    dr = drifts[-1] if drifts else None      # upstream main checked against the pin (tools/openproblems.py drift)
    out.append({"rung": "openproblems.bio", "last": ev_last, "idle_days": _days(now, ev_last), "rounds_24h": sum(map(since, ev)),
                "scored": len(scored), "crashed": sum("error" in r for r in ev), "qualify_runs": len(quals),
                "qualify": {"at": q["at"], "passed": bool(q["verdict"].get("passed")), "sites": q["verdict"].get("sites"),
                            "mean_pearson_delta": q["verdict"].get("mean_pearson_delta")} if q and q.get("verdict") else None,
                "drift": {"at": dr["at"], "main": dr["main"][:12], "status": dr["status"]} if dr else None,
                "source": source_probe.state(source_probe.read("openproblems", Path(ledger) / "sources"))})
    return out


def build(ledger, now, hours=24, daily=None):
    """The window is the rows that arrived since the last earlier-day report (arrivals()); outside a git checkout, or
    with no earlier report at all, the last `hours` by row ts, labeled so in window.kind."""
    ledger = Path(ledger)
    rows = tries(ledger) if ledger.exists() else []
    if not rows:
        sys.exit(f"no ledger rows under {ledger}: a report of nothing would read as a quiet day")
    fresh, win = arrivals(ledger, daily or ledger / "daily", f"{now:%Y-%m-%d}")
    if fresh is None:
        cut = (now - timedelta(hours=hours)).isoformat()
        head = git(ledger, "rev-parse", "HEAD")
        win = {"kind": "ts", "reason": win, "since": cut, "built_from": head.strip() if head else None}
        since = lambda r, k=None: ((r.get(k) if k else _ts(r)) or "") > cut
    else:
        since = arrived(fresh)
    window = [r for r in rows if since(r)]
    judged = [r for r in window if r["verdict"] in ("accept", "reject", "error")]
    answered = [r for r in judged if r["verdict"] != "error"]
    g, firsts = grades(rows, since)
    errors = Counter(lost_bucket(r.get("reason") or "") for r in judged if r["verdict"] == "error")
    return {"day": f"{now:%Y-%m-%d}", "to": now.isoformat(), "hours": hours, "window": win,
            "totals": {"judged": len(judged), "answered": len(answered), "accepted": sum(r["verdict"] == "accept" for r in answered),
                       "errors": dict(errors), "recovered": recovered(judged),
                       "lanes": len({r.get("backend") for r in judged}), "problems": len({(r.get("target_set"), r["target"]) for r in judged}),
                       "solved_ever": sum(x["solved"] for x in g), "open": sum(x["open"] for x in g)},
            "first_solves": sorted(firsts, key=lambda f: f["ts"]), "grades": g, "speed": speed(ledger),
            "kaggle": kaggle(ledger, since), "relay": relay_state(ledger), "rungs": rungs(ledger, rows, now, since)}


EDGE_CUT_S = 125       # kumori.ai's Cloudflare zone's proxy_read_timeout as read on 2026-11-01 (one raw 504 at 121.6 s); an estimate's line


def recovery_of(r):
    """How a row's answer got past the edge cut, or None. kumori's marker inference["recovery"] when the client carries
    it; until then (Andy, 2026-11-01, via the kumori session: do not wait on kumori) the row's own clock, an estimate:
    an answering call that ran past EDGE_CUT_S and still ended in a verdict is read as having come back through the
    /result/<id> fetch."""
    m = (r.get("inference") or {}).get("recovery")
    if isinstance(m, dict):                                   # the marker is authoritative either way (Codex f2)
        return m if m.get("attempted") else None
    if (r.get("upstream_answer_s") or 0) > EDGE_CUT_S and r.get("verdict") in ("accept", "reject"):
        # an estimate from the answering call's own clock (a failed earlier try is not it): a verdict that arrived
        # after the cut can only have come through the fetch. Residuals: a rescue after an early network drop ends
        # sooner and is missed; the edge's 125 s is read, not proven for every path (Codex f1 x2, f3)
        return {"attempted": True, "succeeded": True, "original": "clock>125s", "estimate": True}
    return None


def recovered(rows):
    """Answers rescued after an edge cut (#597, 2026-11-01), by recovery_of(). Counted apart, by what Lean said of them
    and how many rescues failed, so the lost-before-the-kernel line can be attributed to the rescue, not the weather.
    {} when no row shows one."""
    rec = [(r, recovery_of(r)) for r in rows]
    rec = [(r, m) for r, m in rec if m]
    if not rec:
        return {}
    ok = [r for r, m in rec if m.get("succeeded") and r["verdict"] in ("accept", "reject")]
    return {"attempted": len(rec), "answers": len(ok), "accepted": sum(r["verdict"] == "accept" for r in ok),
            "failed": sum(not m.get("succeeded") for _, m in rec),
            "estimated": sum(bool(m.get("estimate")) for _, m in rec),
            "by_original": dict(Counter(str(m.get("original")) for _, m in rec))}


def render(d):
    t, out = d["totals"], []
    w = d.get("window") or {}
    span = (f"rows that reached the ledger since the {w['from_report']} report" if w.get("kind") == "arrived" else
            f"the {d['hours']} hours to {d['to'][11:16]} UTC by row time")
    out += [f"**{d['day']}** ({span}): **{len(d['first_solves'])} first-time solves**, "
            f"{t['accepted']} accepts from {t['answered']} answered tries by {t['lanes']} lanes on {t['problems']} problems. "
            f"{t['solved_ever']} problems solved ever, {t['open']} open.", ""]
    if d.get("brief"):                                   # what changed against the prior week (tools/daily_brief.py)
        out += [daily_brief.render(d["brief"]), "**The details**", ""]
    if t.get("errors"):
        out += ["Lost before the kernel: " + ", ".join(f"{n} {k}" for k, n in sorted(t["errors"].items(), key=lambda x: -x[1])), ""]
    if t.get("recovered"):
        rc = t["recovered"]
        out += [f"Recovered after an edge cut: {rc['answers']} answers ({rc['accepted']} accepted) of {rc['attempted']} rescues tried, "
                f"{rc['failed']} failed; by cause: " + ", ".join(f"{k} {n}" for k, n in sorted(rc["by_original"].items(), key=lambda x: -x[1]))
                + (f" ({rc['estimated']} read from the row's clock alone, an estimate until kumori's marker lands)" if rc.get("estimated") else ""), ""]
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
                "| lane | size | this week | week before | off the no-model baseline | refused |", "|---|---:|---:|---:|---:|---:|"]
        for s in d["speed"]:
            prev = f"{s['prev_accepted']}/{s['prev_targets']}" if s["prev_week"] else "none"
            off = f"{s['accepted_off']}/{s['targets_off']}" if "targets_off" in s else "no baseline"
            out.append(f"| {s['lane']} | {s['size_b'] or '?'}B | {s['accepted']}/{s['targets']} | {prev} | {off} | {s['refused']} |")
        out.append("Off the no-model baseline: targets Lean's automation alone did not prove in replay's tools_alone arm "
                   "(a reject there, not proof that automation cannot); a lift on small models is read there.")
    k = d["kaggle"]
    if k["finished"] or k["failed"]:
        out += ["", "**Kaggle prover batches:** " + "; ".join([f"{b['batch']} finished, {b['answers']} answers" for b in k["finished"]] +
                                                        [f"{b['batch']} FAILED" for b in k["failed"]])]
    out += ["", "| rung | last activity | idle days |", "|---|---|---:|"]
    for r in d["rungs"]:
        extra = ""
        if r["rung"] == "openproblems.bio":
            q = r.get("qualify")
            delta = f"{q['mean_pearson_delta']:+.3f}" if q and q.get("mean_pearson_delta") is not None else "unavailable"
            bar = (f"last qualify {'PASSED' if q['passed'] else 'missed'} {q['at'][:10]} (Pearson delta {delta} over {q['sites']} site{'s' if q['sites'] != 1 else ''})"
                   if q else "no qualify run yet")
            dr = r.get("drift")
            if dr and dr["status"] != "current":
                bar += (f"; upstream main {dr['main']} {'FAILS' if dr['status'] == 'fails' else 'passes'} the reproduce gate"
                        f" ({dr['at'][:10]}), the pin {'stays' if dr['status'] == 'fails' else 'can move'}")
            src = r.get("source")
            if src and not src["ok"]:
                bar += f"; DATA SOURCE DOWN since {src['down_since'][:10]} ({src['code']})"
            elif src and src.get("back_since"):
                bar += f"; data source back since {src['back_since'][:10]}"
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
    d = build(a.ledger, datetime.fromisoformat(a.now), a.hours, a.out)
    if d["window"]["kind"] != "arrived":
        print(f"::warning::daily report counted by row time, not arrival: {d['window']['reason']}")
    out = Path(a.out)
    out.mkdir(parents=True, exist_ok=True)
    earlier = [f for f in sorted(out.glob("*.json")) if f.stem < d["day"]]          # filter first: a backfill reads its own week
    history = [json.loads(f.read_text()) for f in earlier[-daily_brief.HISTORY_DAYS:] if f.read_text().strip()]
    d["brief"] = daily_brief.brief(d, history)
    (out / f"{d['day']}.json").write_text(json.dumps(d, indent=1, sort_keys=True) + "\n")
    (out / f"{d['day']}.md").write_text(render(d))
    print(f"wrote {out / d['day']}.{{json,md}}: {len(d['first_solves'])} first-time solves, {d['totals']['accepted']} accepts")
    return 0


if __name__ == "__main__":
    sys.exit(main())
