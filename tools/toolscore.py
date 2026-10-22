"""The tool scoreboard (DECISIONS.md 2026-10-17, Kumori task #463): every tool in the loop's chain, graded.

The loop's ablation (attempt.py --retro) scores the chain in stages: A as written, B plus the fixer, C plus
holes and Lean's automation. This grades each tool inside the chain by leaving it out. For every stored cold
reject the chain touched, it runs the whole chain again (arm `full`), then once per tool that chain used with
that one tool removed (arm `without`). Same answer, same code, only the tool differs, so the comparison is paired:
  needed = full accepted and the chain without the tool did not (a turn the tool made)
  cost   = full rejected and the chain without the tool accepted (a turn the tool spoiled)
A tool the full chain never used on a reject cannot change it, so only the tools it used are re-run.

Held out: an attempt id's parity splits the rejects. Odd ids are the report half, the numbers the site shows;
even ids are the tune half, for anyone building or tuning a tool against. A new tool is tuned on one half and
reported on the other (later, miniF2F-valid).

Model-call arms (the dossier on or off with the goal closer, #461) are rows with their own arm names in the
same table; this module's arms are Lean only, no model asked.

The speed receipt (task #191) runs the same chain, the `full` arm only, on a frozen sample of each finished week's
rejects (kumori picks it: report half, up to 200 a week by a hash of the id). The rejects above are only those the
chain of the day touched, so a tool that turns one it never touched cannot show there; on the sample it can. Shown
on sparebrains.kumori.ai/loop#speed, a table per chain, so each tool change re-runs every earlier week.

    python3 tools/toolscore.py --slice 0/6 --max-minutes 320          # one slice of the report half
    python3 tools/toolscore.py --half tune --slice 0/1
    python3 tools/toolscore.py --speed --slice 0/6 --max-minutes 60   # the frozen weekly sample, whole chain only
    python3 tools/toolscore.py --resolve --slice 0/6 --max-minutes 60  # fresh cold tries on it, then the chain

The re-solve layer (task #191 step 2, design reviewed 2026-10-22): the replay above reuses stored answers, so a
faster model or a tool that changes what a model writes cannot show there. Here one pinned lane answers each frozen
problem afresh (the plain cold prompt: the statement only, never a past proof), the chain of the day runs on its
answer, and the rows go to ledger/speed/ only: no kumori submit, no verified/ write, fenced from every try reader
(tools/ledger_files.py). The sample per finished week: the week's attempted problems on the report half (a hash of
the problem, not of an attempt id), a few first solved that week and a few still open at its end, frozen once with
their statement hashes in ledger/speed/sample.jsonl. Each run week asks every frozen problem RESOLVE_TRIES times;
a problem no try solves is censored at that budget, and router errors are kept apart from tries.
"""
import argparse, hashlib, json, os, re, subprocess, sys, time, uuid
from datetime import datetime, timedelta, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT), str(ROOT / "tools")]
import fixer                                                         # the form passes
import subgoals                                                      # holes and Lean's automation
from proof_text import PROOF_SEP

# Each tool by its job, as the scoreboard names it. Passes are fixer.fix's names; closers are AUTO_TACTICS.
FIXER_PASSES = {
    "double_by": "drops a second `by` the model wrote after the target's own",
    "layout": "lines tactics up so Lean reads the proof's shape",
    "lean3": "rewrites Lean 3 syntax as Lean 4",
    "names": "swaps an invented library name for the closest real mathlib one",
}
CLOSERS = {t: "closes a failing step: " + t for t in subgoals.AUTO_TACTICS}
CLOSERS["exact?"] = "closes a failing step with a library lemma it searches for (exact?)"
TOOLS = {**FIXER_PASSES, **CLOSERS}
FILES = ("fixer.py", "subgoals.py", "proof_text.py")


SPEED_DIR = ROOT / "ledger" / "speed"
RESOLVE_LANE = "openrouter-minimax-m3-1-flash"   # pinned (task #191, 2026-10-22): another lane starts a new series
RESOLVE_PER_WEEK = (3, 3)        # problems a week: first solved that week, still open at its end
RESOLVE_TRIES, RESOLVE_RETRIES = 3, 2   # cold tries per problem per run week; router-error retries per try
STOP_RUN = re.compile(r"spent its share|is gated|is benched|never_fits|HTTP 404|unknown backend", re.I)


def week_of(ts):
    """Monday (UTC) of an ISO timestamp's week, as YYYY-MM-DD: kumori's date_trunc('week')."""
    d = datetime.fromisoformat(ts.replace("Z", "+00:00")).astimezone(timezone.utc).date()
    return str(d - timedelta(days=d.weekday()))


def problem_hash(tset, target):
    return hashlib.md5(f"{tset}/{target}".encode()).hexdigest()


def problem_half(tset, target):
    """The re-solve's held-out boundary is the problem, not the attempt: odd hash = report half."""
    return "report" if int(problem_hash(tset, target)[:8], 16) % 2 else "tune"


def freeze_sample(rows, now_ts, frozen_weeks, statement_sha, per_week=RESOLVE_PER_WEEK):
    """New sample entries for finished weeks not yet frozen. rows: try rows (ts, target_set, target, verdict).
    statement_sha(tset, target) -> the target file's statement hash, or None when the file is gone."""
    first, seen = {}, {}
    for r in sorted((r for r in rows if r.get("ts") and r.get("target_set") and r.get("target")), key=lambda r: r["ts"]):
        k = (r["target_set"], r["target"])
        seen.setdefault(week_of(r["ts"]), set()).add(k)
        if r.get("verdict") == "accept":
            first.setdefault(k, week_of(r["ts"]))
    out = []
    for wk in sorted(w for w in seen if w < week_of(now_ts) and w not in frozen_weeks):
        report = sorted((k for k in seen[wk] if problem_half(*k) == "report"), key=lambda k: problem_hash(*k))
        solved = [k for k in report if first.get(k) == wk]
        still_open = [k for k in report if k not in first or first[k] > wk]
        for kind, pool, n in (("solved_then", solved, per_week[0]), ("open_then", still_open, per_week[1])):
            for k in pool:
                if n == 0:
                    break
                sha = statement_sha(*k)
                if sha:
                    out.append({"week": wk, "target_set": k[0], "target": k[1], "kind": kind, "statement_sha": sha})
                    n -= 1
    return out


def resolved_keys(rows):
    """Tries already answered: an error row is kept for the record but leaves its try owed."""
    return {(r["run_week"], r["chain"], r["lane"], r["week"], r["target_set"], r["target"], r["try"])
            for r in rows if r.get("verdict") != "error"}


def resolve_queue(sample, done, run_week, chain, lane, slice_k, slice_n, tries=RESOLVE_TRIES):
    """Every (sample entry, try) this run week still owes for this chain and lane, in this slice; done holds
    (run_week, chain, lane, week, set, target, try) of rows already written, so a later job resumes."""
    q = []                       # round-robin over the sample in hash order: every slice the same share (±1 problem)
    ordered = sorted(sample, key=lambda s: (problem_hash(s["target_set"], s["target"]), s["week"]))
    for i, s in enumerate(ordered):
        if i % slice_n != slice_k:
            continue
        for t in range(1, tries + 1):
            if (run_week, chain, lane, s["week"], s["target_set"], s["target"], t) not in done:
                q.append((s, t))
    return q


def resolve_one(s, t, text, prefix, ask, judge, chain_fn, retries=RESOLVE_RETRIES):
    """One fresh cold try: ask (router errors retried, counted apart), judge, then the chain on a reject.
    ask(prompt) -> (reply, meta) or raises; an exception whose text matches STOP_RUN ends the run (returns None)."""
    import attempt                                       # the loop's own cold prompt, unchanged
    from proof_text import extract_proof
    row = {"week": s["week"], "target_set": s["target_set"], "target": s["target"], "kind": s["kind"], "try": t,
           "router_errors": 0}
    t0 = time.monotonic()
    for _ in range(retries + 1):
        try:
            reply, meta = ask(attempt.ASK + text)
            break
        except Exception as e:
            if STOP_RUN.search(str(e)):
                return None
            row["router_errors"] += 1
            row["last_error"] = str(e)[:200]
    else:
        return {**row, "verdict": "error", "call_seconds": round(time.monotonic() - t0, 1)}
    row.update(call_seconds=round(time.monotonic() - t0, 1), response_chars=len(reply or ""), **meta)
    proof = extract_proof(reply or "", s["target"])
    if not proof:
        return {**row, "cold": "reject", "verdict": "reject", "reason": "no proof extracted from reply"}
    j = judge(prefix + "\n" + proof)
    cold = "accept" if j["verdict"] == "accept" else "reject"
    row.update(cold=cold, lean_seconds=j.get("seconds"))
    if cold == "accept":
        return {**row, "verdict": "accept"}
    t1 = time.monotonic()
    c = chain_fn(proof, prefix, j.get("output") or "")
    return {**row, "verdict": c["c_verdict"], "fixes": c["fixes"], "closers": c["rep"].get("closers") or [],
            "chain_seconds": round(time.monotonic() - t1, 1)}


def chain_version():
    """The chain's code, hashed: a scoreboard row counts only against the code that produced it."""
    h = hashlib.sha256()
    for f in FILES:
        h.update((ROOT / "tools" / f).read_bytes())
    return h.hexdigest()[:10]


def half(attempt_id):
    return "report" if int(attempt_id) % 2 else "tune"


def closer_tool(ran):
    """The AUTO_TACTICS entry behind a closer the chain recorded: `exact Foo.bar h` was exact?, `norm_num`
    was `(norm_num; done)`. None for the whole `first | ...` (an all_goals hole: which one ran is unknown)."""
    ran = (ran or "").strip()
    if not ran or ran.startswith("first |"):
        return None
    if ran.startswith("exact"):
        return "exact?"
    for t in subgoals.AUTO_TACTICS:
        if ran == t or t == f"({ran}; done)":
            return t
    return None


def tools_used(fixes, closers):
    """The tools a chain run used, in chain order, each once."""
    out = [f for f in fixes if f in FIXER_PASSES]
    for c in closers:
        t = closer_tool(c)
        if t and t not in out:
            out.append(t)
    return out


def run_chain(proof, prefix, said, names_ix, lean, skip=()):
    """The loop's Lean-only chain on one stored answer: the fixer, then holes and Lean's automation, with the
    tools in `skip` left out. `lean` is tools/lean_tools. Returns {fixes, b_verdict, c_verdict, rep, final}."""
    if not subgoals.errors(said):                    # a stored output with no positioned error: judge it afresh
        said = lean.judge_text(prefix + "\n" + proof)["output"]
    fixed, fixes = fixer.fix(proof, said, *names_ix, skip=skip)
    cand, b_verdict = prefix + "\n" + fixed, "reject"
    if fixes:
        rb = lean.judge_text(cand)
        b_verdict, said = ("accept" if rb["verdict"] == "accept" else "reject"), rb["output"]
    rep = {}
    if b_verdict == "accept":
        return {"fixes": fixes, "b_verdict": "accept", "c_verdict": "accept", "rep": rep, "final": cand}
    tactics = [t for t in subgoals.AUTO_TACTICS if t not in skip]
    try:
        rep = subgoals.repair(cand, prefix, said, ask=None, run_lean=lean.run_lean, judge_text=lean.judge_text,
                              tactics=tactics)
    except Exception as e:
        rep = {"stopped": f"loop error: {type(e).__name__}"}
    final = rep.get("accepted")
    return {"fixes": fixes, "b_verdict": "reject", "c_verdict": "accept" if final else "reject", "rep": rep,
            "final": final}


def arms_to_run(full):
    """The leave-one-out arms worth a Lean run after a full-chain result. A closer can only close steps, so
    without it a rejected chain stays rejected: closers are re-run only on a turn. A fixer pass rewrites the
    proof, so it can also spoil one: passes are re-run either way."""
    used = tools_used(full["fixes"], full["rep"].get("closers") or [])
    return [t for t in used if t in FIXER_PASSES or full["c_verdict"] == "accept"]


def grade_one(a, prefix, names_ix, lean, full_only=False):
    """[(tool, arm, verdict, fixes, closers, seconds)] for one stored reject: the full chain, then each tool out
    (unless full_only, the speed receipt's case)."""
    out = []
    t0 = time.monotonic()
    full = run_chain(a["proof"], prefix, a.get("lean_output") or "", names_ix, lean)
    out.append(("*", "full", full["c_verdict"], full["fixes"], full["rep"].get("closers") or [],
                round(time.monotonic() - t0, 1)))
    for tool in ([] if full_only else arms_to_run(full)):
        t0 = time.monotonic()
        r = run_chain(a["proof"], prefix, a.get("lean_output") or "", names_ix, lean, skip=(tool,))
        out.append((tool, "without", r["c_verdict"], r["fixes"], r["rep"].get("closers") or [],
                    round(time.monotonic() - t0, 1)))
    return out


def speed_report(rows, sample, tries=RESOLVE_TRIES):
    """Compute to first accept on the frozen sample, per run week, chain and lane, then per frozen week. Every frozen
    problem counts, tried or not. A problem's answered tries (accept/reject; errors left out) are taken in the order
    they were answered (ts), and calls to first accept = answered tries up to and including the first accept, so an
    error between them or a slot filled later cannot change it. None accepted: censored when `tries` were answered,
    else owed (still in the run week's queue). The router reports no tokens, so compute is counted in calls for a
    fixed lane; seconds = call + Lean + chain for those tries. 'turned' = the first accept came from the chain. A series
    (run week, chain, lane) appears once it has any row, an error-only one as all owed; one with no rows does not."""
    from collections import defaultdict
    answered = defaultdict(lambda: defaultdict(list))
    for r in rows:
        if r.get("verdict") in ("accept", "reject"):
            answered[(r["run_week"], r["chain"], r["lane"])][(r["week"], r["target_set"], r["target"])].append(r)
    series = sorted({(r["run_week"], r["chain"], r["lane"]) for r in rows})
    out = []
    for key in series:
        weeks = defaultdict(lambda: {"problems": 0, "solved": 0, "censored": 0, "owed": 0, "calls_to_first": [],
                                     "seconds_to_first": [], "open_then_solved": 0, "turned": 0})
        for p in sample:
            w = weeks[p["week"]]
            w["problems"] += 1
            rs = sorted(answered[key].get((p["week"], p["target_set"], p["target"]), []), key=lambda r: r["ts"])
            hit = next((i for i, r in enumerate(rs) if r["verdict"] == "accept"), None)
            if hit is None:
                w["censored" if len(rs) >= tries else "owed"] += 1
                continue
            w["solved"] += 1
            w["calls_to_first"].append(hit + 1)
            w["seconds_to_first"].append(round(sum((r.get("call_seconds") or 0) + (r.get("lean_seconds") or 0)
                                                   + (r.get("chain_seconds") or 0) for r in rs[:hit + 1]), 1))
            w["open_then_solved"] += p["kind"] == "open_then"
            w["turned"] += rs[hit].get("cold") == "reject"
        for wk, w in sorted(weeks.items()):
            out.append({"run_week": key[0], "chain": key[1], "lane": key[2], "week": wk, **w})
    return out


def render_speed(report):
    lines = ["| run week | chain | lane | frozen week | solved | calls to first accept, among solved | censored | owed "
             "| open then, solved | turned by the chain |", "|---|---|---|---|---|---|---|---|---|---|"]
    for r in report:
        at = ", ".join(str(c) for c in sorted(r["calls_to_first"])) or "-"
        lines.append(f"| {r['run_week']} | {r['chain']} | {r['lane']} | {r['week']} | {r['solved']}/{r['problems']} | "
                     f"{at} | {r['censored']} | {r['owed']} | {r['open_then_solved']} | {r['turned']} |")
    return "\n".join(lines)


def statement_sha(tset, target):
    f = ROOT / "targets" / tset / f"{target}.lean"
    if not f.exists():
        return None
    text = f.read_text()
    return hashlib.sha256(text[:PROOF_SEP.search(text).end()].encode()).hexdigest()


def load_jsonl(files):
    return [json.loads(l) for f in files for l in f.read_text().splitlines() if l.strip()]


def resolve_main(args, run_id, chain, names_ix, lean):
    """The re-solve layer: freeze any newly finished week, then this slice's owed tries for this run week."""
    import attempt, ledger_files
    from utilities.kumori_api_client import llm_chat
    SPEED_DIR.mkdir(parents=True, exist_ok=True)
    frozen = load_jsonl(sorted(SPEED_DIR.glob("sample-*.jsonl")))
    now = datetime.now(timezone.utc).isoformat()
    new = freeze_sample(load_jsonl(ledger_files.try_files(ROOT / "ledger")), now, {s["week"] for s in frozen},
                        statement_sha)
    for wk in sorted({s["week"] for s in new}):         # one file a week, written once, the same from every slice
        f = SPEED_DIR / f"sample-{wk}.jsonl"
        if not f.exists():
            f.write_text("".join(json.dumps(s) + "\n" for s in new if s["week"] == wk))
            print(f"resolve: froze {f.name}", flush=True)
    sample = load_jsonl(sorted(SPEED_DIR.glob("sample-*.jsonl")))
    run_week = week_of(now)
    done = resolved_keys(load_jsonl(sorted(SPEED_DIR.glob("resolve-*.jsonl"))))
    k, n = (int(x) for x in args.slice.split("/"))
    queue = resolve_queue(sample, done, run_week, chain, RESOLVE_LANE, k, n)
    rev = subprocess.run(["git", "rev-parse", "HEAD"], capture_output=True, text=True, cwd=ROOT).stdout.strip()
    config = {"max_tokens": 4000, "temperature": 0.2, "timeout_s": 60, "client_read_timeout_s": 180}
    out = SPEED_DIR / f"resolve-{run_id}-{k}.jsonl"
    deadline = time.time() + 60 * args.max_minutes if args.max_minutes else None
    print(f"resolve: run week {run_week}, chain {chain}, lane {RESOLVE_LANE}, {len(sample)} frozen problems, "
          f"{len(queue)} tries owed in slice {args.slice}", flush=True)

    def ask(prompt):
        text, backend, inference = llm_chat(RESOLVE_LANE, [{"role": "user", "content": prompt}],
                                            max_tokens=config["max_tokens"], temperature=config["temperature"],
                                            system=attempt.SYSTEM, app_name="sparebrains", timeout=(10, 180),
                                            timeout_s=config["timeout_s"], include_metadata=True,
                                            request_id=uuid.uuid4().hex)
        return text, {"returned_backend": backend, "inference": inference}
    chain_fn = lambda proof, prefix, said: run_chain(proof, prefix, said, names_ix, lean)
    n_rows = 0
    for s, t in queue:
        if deadline and time.time() > deadline:
            break
        text = (ROOT / "targets" / s["target_set"] / f"{s['target']}.lean").read_text()
        prefix = text[:PROOF_SEP.search(text).end()]
        if hashlib.sha256(prefix.encode()).hexdigest() != s["statement_sha"]:
            print(f"resolve: {s['target_set']}/{s['target']} changed since it was frozen; not asked", flush=True)
            continue
        r = resolve_one(s, t, text, prefix, ask, lean.judge_text, chain_fn)
        if r is None:
            print(f"resolve: {RESOLVE_LANE} refused for this run (share, gate or bench); stopping", flush=True)
            break
        row = {"ts": datetime.now(timezone.utc).isoformat(timespec="seconds"), "run_id": run_id, "run_week": run_week,
               "chain": chain, "git_rev": rev, "lane": RESOLVE_LANE, "request_config": config, "half": "report", **r}
        with out.open("a") as fh:
            fh.write(json.dumps(row) + "\n")
        n_rows += 1
        print(f"[resolve] {s['week']} {s['target_set']}/{s['target']} try {t}: {r['verdict']}", flush=True)
    print(f"resolve: {n_rows} tries written to {out.relative_to(ROOT)}", flush=True)
    return 0


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--half", choices=["report", "tune"], default="report")
    ap.add_argument("--slice", default="0/1", help="k/N: every Nth stored reject from k, for a matrix of jobs")
    ap.add_argument("--max-minutes", type=float, default=0)
    ap.add_argument("--max-rows", type=int, default=100000)
    ap.add_argument("--speed", action="store_true", help="the speed receipt's frozen weekly sample, whole chain only")
    ap.add_argument("--resolve", action="store_true", help="fresh cold tries on the frozen weekly sample (task #191)")
    ap.add_argument("--resolve-report", action="store_true", help="print the re-solve layer's table (no model, no Lean)")
    args = ap.parse_args()
    if args.resolve_report:
        print(render_speed(speed_report(load_jsonl(sorted(SPEED_DIR.glob("resolve-*.jsonl"))),
                                        load_jsonl(sorted(SPEED_DIR.glob("sample-*.jsonl"))))))
        return 0
    if args.speed and args.half != "report":
        sys.exit("--speed is the report half only")
    if not os.environ.get("KUMORI_API_KEY"):
        sys.exit("KUMORI_API_KEY is not set")
    import lean_tools
    from utilities.kumori_api_client import init as kumori_init, sparebrains_toolscore, sparebrains_toolscore_todo
    kumori_init()
    run_id = os.environ.get("GITHUB_RUN_ID") or datetime.now(timezone.utc).strftime("local-%Y%m%dT%H%M%S")
    chain = chain_version()
    names_ix = lean_tools.index()
    if args.resolve:
        return resolve_main(args, run_id, chain, names_ix, lean_tools)
    deadline = time.time() + 60 * args.max_minutes if args.max_minutes else None
    after, n_rows, needed, cost = 0, 0, {}, {}
    rows_kind = "speed" if args.speed else "touched"
    print(f"toolscore: chain {chain}, {args.half} half, slice {args.slice}, {rows_kind} rows", flush=True)
    while n_rows < args.max_rows and not (deadline and time.time() > deadline):
        page = sparebrains_toolscore_todo(chain, args.half, args.slice, after, 50, rows=rows_kind)
        if not page:
            break
        for a in page:
            after = a["id"]
            if n_rows >= args.max_rows or (deadline and time.time() > deadline):
                break
            tfile = ROOT / "targets" / a["target_set"] / f"{a['target']}.lean"
            if not tfile.exists():
                continue
            text = tfile.read_text()
            prefix = text[:PROOF_SEP.search(text).end()]
            rows = grade_one(a, prefix, names_ix, lean_tools, full_only=args.speed)
            full = rows[0][2]
            for tool, arm, verdict, fixes, closers, secs in rows:
                sparebrains_toolscore({"run_id": run_id, "chain": chain, "attempt_id": a["id"], "tool": tool,
                                       "arm": arm, "half": args.half, "verdict": verdict,
                                       "fixes": "+".join(fixes) or None, "closers": ", ".join(closers) or None,
                                       "seconds": secs})
                if arm == "without":
                    needed[tool] = needed.get(tool, 0) + (full == "accept" and verdict != "accept")
                    cost[tool] = cost.get(tool, 0) + (full != "accept" and verdict == "accept")
            n_rows += 1
            if n_rows % 25 == 0:
                print(f"[toolscore {args.slice}] {n_rows} graded; needed {needed}; cost {cost}", flush=True)
    print(f"toolscore: {n_rows} stored rejects graded; needed {needed}; cost {cost}", flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
