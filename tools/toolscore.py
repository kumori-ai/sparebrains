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
from collections import defaultdict
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
# Pinned (task #191): a new lane starts a new series. openrouter-minimax-m3-1-flash (2026-10-22) answers "HTTP 404:
# unknown backend" since; re-pinned 2026-10-24 to the live, active lane with the most answers and fewest errors among
# the strong ones: 353/584 cold accepts (60.4%) and 37 errors in the 14 days to 2026-10-24 (DECISIONS.md).
RESOLVE_LANE = "agnes-agnes-2-5-flash"
RESOLVE_PER_WEEK = (3, 3)        # problems a week: first solved that week, still open at its end
# The size series (2026-10-24, non-negotiable 6; DECISIONS.md): solved targets re-run by one model family at three
# sizes, dated snapshots, with this week's chain. A pilot: 45 problems frozen once, per rung, weights kept.
SIZE_LANES = (("mistral-ministral-3b-2512", 3), ("mistral-ministral-8b-2512", 8), ("mistral-ministral-14b-2512", 14))
SOLVED_CUTOFF = "2026-10-24T00:00:00+00:00"   # eligible: first accepted before this
SOLVED_N, SOLVED_MIN_PER_RUNG = 45, 3
MAX_REQUESTS = 80                # per process (one slice): every request, retries included
RESOLVE_TRIES, RESOLVE_RETRIES = 3, 2   # cold tries per problem per run week; router-error retries per try
STOP_RUN = re.compile(r"spent its share|is gated|is benched|never_fits", re.I)
# A pinned lane kumori no longer has is a broken series, not a spent share: openrouter-minimax-m3-1-flash answered
# "HTTP 404 : unknown backend" and the re-solve stopped quietly for 4 nights, 0 tries (2026-10-24).
CATALOG_MISS = re.compile(r"catalog lookup failed", re.I)
GONE = re.compile(r"HTTP 404\b")   # kumori 2026-10-24: only a retired or never-catalogued lane answers 404


class LaneGone(RuntimeError):
    """The pinned lane does not exist in kumori any more: re-pin the series (a new lane starts a new series)."""


class Refused(RuntimeError):
    """The lane refused this request (share spent, gated, benched, rate limited, never fits): the router's text, its
    error_code and, when it knows, how many seconds until the lane recovers (retry_after)."""
    def __init__(self, msg, error_code=None, retry_after=None):
        super().__init__(msg)
        self.error_code, self.retry_after = error_code, retry_after


# kumori's error_code for a lane that is refusing, not failing (api_v1_llm_bp): waited for and asked again
REFUSAL_CODES = {"rate_limited_429", "quota_paced", "rpm_spacing", "benched", "pool_gated", "daily_cap_exhausted"}
NO_RETRY_CODES = {"daily_cap_exhausted"}     # does not come back within a run
REFUSAL_WAIT_MAX_S = 600


REFUSAL_WAIT_S = 180   # a refused lane is waited for and asked again, like the relay's PARK_WAIT_S (run 40114239227: every
REFUSAL_RETRIES = 2    # lane refused once around 17:03Z and answered by 17:45Z), at most this many times a run


class CapReached(Exception):
    """The process's request budget is spent; raised before the request that would exceed it."""


class Budget:
    """Requests one process may still make, shared by every lane and cohort, retries and refusals included."""
    def __init__(self, n):
        self.left = n

    def take(self):
        if self.left <= 0:
            return False
        self.left -= 1
        return True


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


def cohort_of(entry):
    """A sample entry's or row's cohort: the frozen weekly sample (rows from before 2026-10-24 carry none) or `solved`."""
    return entry.get("cohort") or "weekly"


def frozen_weekly_weeks(sample):
    """The weeks the weekly cohort has frozen; the solved cohort never counts as a frozen week."""
    return {s["week"] for s in sample if cohort_of(s) == "weekly"}


def freeze_solved(rows, cutoff, statement_sha, n=SOLVED_N, min_per_rung=SOLVED_MIN_PER_RUNG):
    """The size series' pilot sample: targets first accepted before `cutoff`, report half, file unchanged; per rung at
    least `min_per_rung` (or all it has), each rung's picks taken in problem
    hash order. Proportional to rung size by largest remainder, then each rung raised to its minimum at the cost of the
    largest rungs. weight = the rung's eligible count / its picks, so a rung-weighted rate can be reported beside the raw."""
    import ladder
    first = {}
    for r in sorted((r for r in rows if r.get("verdict") == "accept" and r.get("ts")), key=lambda r: r["ts"]):
        first.setdefault((r["target_set"], r["target"]), r)
    by_rung = {}
    for (tset, name), r in first.items():
        if r["ts"] < cutoff and problem_half(tset, name) == "report" and statement_sha(tset, name):
            by_rung.setdefault(r.get("rung") or ladder.rung_of(tset, name)[0], []).append((tset, name))
    total = sum(len(v) for v in by_rung.values())
    share = {g: n * len(v) / total for g, v in by_rung.items()} if total else {}
    take = {g: min(int(share[g]), len(by_rung[g])) for g in by_rung}          # proportional first, largest remainder
    for g in sorted(by_rung, key=lambda g: (-(share[g] - int(share[g])), g)):
        if sum(take.values()) >= min(n, total):
            break
        if take[g] < len(by_rung[g]):
            take[g] += 1
    for g in by_rung:                                                         # then every rung gets its minimum,
        take[g] = max(take[g], min(len(by_rung[g]), min_per_rung))
    while sum(take.values()) > n:                                             # paid for by the largest rungs
        g = max((g for g in take if take[g] > min(len(by_rung[g]), min_per_rung)), key=lambda g: (take[g], g), default=None)
        if g is None:
            break
        take[g] -= 1
    week = "solved-" + cutoff[:10]
    out = []
    for g in sorted(by_rung):
        picks = sorted(by_rung[g], key=lambda k: problem_hash(*k))[:take[g]]
        for tset, name in picks:
            out.append({"week": week, "cohort": "solved", "target_set": tset, "target": name, "rung": g,
                        "weight": len(by_rung[g]) / len(picks), "statement_sha": statement_sha(tset, name)})
    return out


def resolved_keys(rows):
    """Tries already answered: an error row is kept for the record but leaves its try owed."""
    return {(r["run_week"], r["chain"], r["lane"], cohort_of(r), r["week"], r["target_set"], r["target"], r["try"])
            for r in rows if r.get("verdict") not in ("error", "lane_gone", "refused")}


def raw_solved(rows):
    """Problems a lane already solved raw in a run week: their later tries are not owed (each arm's cost runs to its
    own first accept; Codex 20261024T150248489394Z)."""
    return {(r["run_week"], r["chain"], r["lane"], cohort_of(r), r["week"], r["target_set"], r["target"])
            for r in rows if r.get("cold") == "accept"}


def resolve_queue(sample, done, run_week, chain, lane, slice_k, slice_n, tries=RESOLVE_TRIES, cohort="weekly",
                  raw_solved=()):
    """Every (sample entry, try) this run week still owes for this chain and lane, in this slice; done holds
    (run_week, chain, lane, week, set, target, try) of rows already written, so a later job resumes."""
    q = []                       # round-robin over the sample in hash order: every slice the same share (±1 problem)
    ordered = sorted((s for s in sample if cohort_of(s) == cohort),
                     key=lambda s: (problem_hash(s["target_set"], s["target"]), s["week"]))
    for i, s in enumerate(ordered):
        if i % slice_n != slice_k:
            continue
        if (run_week, chain, lane, cohort, s["week"], s["target_set"], s["target"]) in raw_solved:
            continue
        for t in range(1, tries + 1):
            if (run_week, chain, lane, cohort, s["week"], s["target_set"], s["target"], t) not in done:
                q.append((s, t))
    return q


def resolve_one(s, t, text, prefix, ask, judge, chain_fn, retries=RESOLVE_RETRIES):
    """One fresh cold try: ask (router errors retried, counted apart), judge, then the chain on a reject.
    ask(prompt) -> (reply, meta) or raises; an exception whose text matches STOP_RUN ends the run (returns None)."""
    import attempt                                       # the loop's own cold prompt, unchanged
    from proof_text import extract_proof
    row = {"week": s["week"], "target_set": s["target_set"], "target": s["target"], "kind": s.get("kind"), "try": t,
           "router_errors": 0, "requests": 0, "cohort": cohort_of(s)}
    t0 = time.monotonic()
    for _ in range(retries + 1):
        row["requests"] += 1
        try:
            reply, meta = ask(attempt.ASK + text)
            break
        except CapReached:
            raise
        except Exception as e:
            if getattr(e, "status_code", None) == 404 or (getattr(e, "status_code", None) is None and GONE.search(str(e))):
                raise LaneGone(str(e)[:200]) from e
            code = getattr(e, "error_code", None)
            payload = getattr(e, "payload", None) if isinstance(getattr(e, "payload", None), dict) else {}
            retry_after = getattr(e, "retry_after", None) or payload.get("retry_after_s")
            # a paused, flaky or newly found lane says paused; a catalog miss says so (kumori api_v1_llm_bp, 2026-10-24).
            # Not every clock-bearing 503: an upstream 5xx comes back as 503 {retry_after_s: 30} too, and that is a
            # router error, retried as one (Codex 20261024T203935061717Z)
            if STOP_RUN.search(str(e)) or code in REFUSAL_CODES or payload.get("paused") \
                    or CATALOG_MISS.search(str(e)):
                raise Refused(str(e)[:300], code or ("paused" if payload.get("paused") else None), retry_after) from e
            row["router_errors"] += 1
            row["last_error"] = str(e)[:200]
    else:
        return {**row, "verdict": "error", "call_seconds": round(time.monotonic() - t0, 1)}
    inference = (meta or {}).get("inference") or {}
    usage = inference.get("usage") or {}                 # the provider's counts (kumori #562); None = not reported
    row.update(call_seconds=round(time.monotonic() - t0, 1), response_chars=len(reply or ""), **meta,
               returned_model=inference.get("returned_model"), prompt_tokens=usage.get("prompt_tokens"),
               completion_tokens=usage.get("completion_tokens"), thinking_tokens=usage.get("thinking_tokens"))
    proof = extract_proof(reply or "", s["target"])
    row["answer"] = proof or ""                          # kept for the paired replay through a later chain
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


LEAN_ENV = (ROOT / "tools" / "check.py", ROOT / "tools" / "lean_tools.py", ROOT / "lean-toolchain", ROOT / "lake-manifest.json")


def file_hash(paths):
    h = hashlib.sha256()
    for f in paths:
        h.update(f.read_bytes() if f.exists() else b"")
    return h.hexdigest()[:10]


def resolve_round(queue, lanes, ask_for, text_for, judge, chain_fn, write, max_requests=MAX_REQUESTS,
                  owed=lambda lane, s, t: True, deadline=None, stop_at_raw=True, gone=None, sleep=time.sleep,
                  now=time.time):
    """One process's re-solve over (sample entry, try) items, the lanes interleaved item by item (Mistral's lanes share
    one rate limit). A lane that is gone (404) is written down as `lane_gone` and skipped, a refused one (share, gate,
    bench) is skipped for this run; neither stops the others. Every request is taken from the budget before it is
    made, retries and refusals included (max_requests: a Budget shared across rounds, or a number). With stop_at_raw
    (the solved cohort) a lane stops a problem at its first raw accept; the weekly series keeps all its tries.
    Every request spent is on the record: a try the cap cuts short is an error row, a refusal a `refused` row, each
    with its requests. Returns the lanes found gone, appended to `gone` as they are found, so a caller still has them
    when a later item raises."""
    budget = max_requests if isinstance(max_requests, Budget) else Budget(max_requests)
    gone = [] if gone is None else gone
    refused, raw_hit, refusals = set(), set(), defaultdict(int)

    def counted(ask):
        def go(prompt):                                  # every request: the deadline, then the budget
            if deadline is not None and now() > deadline:
                raise CapReached("deadline reached")
            if not budget.take():
                raise CapReached("request cap reached")
            go.n += 1
            return ask(prompt)
        go.n = 0
        return go
    for s, t in queue:
        for lane in lanes:
            if lane in gone or lane in refused or (lane, s["week"], s["target_set"], s["target"]) in raw_hit \
                    or not owed(lane, s, t):
                continue
            if budget.left <= 0 or (deadline is not None and now() > deadline):
                return gone
            text, prefix = text_for(s)
            where = {"lane": lane, "cohort": cohort_of(s), "week": s["week"], "target_set": s["target_set"],
                     "target": s["target"], "try": t}
            while True:                                  # a refusal is waited out, up to REFUSAL_RETRIES a run
                if deadline is not None and now() > deadline:   # every request, a retry after a wait included
                    return gone
                ask = counted(ask_for(lane))
                try:
                    r = resolve_one(s, t, text, prefix, ask, judge, chain_fn)
                except CapReached as e:
                    if ask.n:
                        write({**where, "verdict": "error", "reason": str(e), "requests": ask.n})
                    return gone
                except LaneGone as e:
                    gone.append(lane)
                    write({**where, "verdict": "lane_gone", "reason": str(e), "requests": ask.n})
                    r = None
                except Refused as e:
                    write({**where, "verdict": "refused", "reason": str(e), "error_code": e.error_code,
                           "requests": ask.n})
                    refusals[lane] += 1
                    wait = e.retry_after if e.retry_after else REFUSAL_WAIT_S
                    if refusals[lane] > REFUSAL_RETRIES or e.error_code in NO_RETRY_CODES \
                            or wait > REFUSAL_WAIT_MAX_S \
                            or (deadline is not None and now() + wait > deadline):
                        refused.add(lane)
                        r = None
                    else:                                # the server's own clock when it gives one; longer: next run
                        sleep(wait)
                        continue
                break
            if r is None:
                continue
            if stop_at_raw and r.get("cold") == "accept":
                raw_hit.add((lane, s["week"], s["target_set"], s["target"]))
            write({**r, "lane": lane})
    return gone


def run_rounds(rounds):
    """Run each round (a callable given the shared list of gone lanes to append to). A gone lane always ends in
    GONE_EXIT, even when that round or a later one raises (the red run must not turn into a warning); without one, the exception propagates."""
    gone = []
    try:
        for f in rounds:
            f(gone)
    except Exception:
        if not gone:
            raise
        import traceback
        traceback.print_exc()
    for lane in gone:
        print(f"::error::resolve: the pinned lane {lane} is gone from kumori; its series is broken until it is "
              f"re-pinned (a new lane starts a new series)", flush=True)
    return GONE_EXIT if gone else 0


GOOGLE_NATIVE = re.compile(r"^(gemini|gemma|google)", re.I)


def output_tokens(row):
    """A try's output tokens, thinking included, per the adapter that answered (kumori shared/kumori_free_llm/
    _backends.py): OpenAI-shaped lanes already count thinking inside completion_tokens; Google's own API (gemini-*,
    gemma-*) reports it apart. None when the provider gave no counts."""
    out, think = row.get("completion_tokens"), row.get("thinking_tokens")
    if out is None and think is None:
        return None
    if GOOGLE_NATIVE.match(str(row.get("returned_backend") or row.get("lane") or "")):
        return (out or 0) + (think or 0)
    return out if out is not None else think


def wilson95(k, n):
    """Wilson score interval for k of n (95%), per problem: tries are never counted as independent problems."""
    if not n:
        return None
    z, p = 1.96, k / n
    d = 1 + z * z / n
    c = (p + z * z / (2 * n)) / d
    h = z * ((p * (1 - p) / n + z * z / (4 * n * n)) ** 0.5) / d
    return round(max(0.0, c - h), 3), round(min(1.0, c + h), 3)


def size_report(rows, sample, tries=RESOLVE_TRIES):
    """The size series per (run week, chain, lane), on the solved cohort: each arm (raw = the model's own answer;
    with tools = after this chain) solved within `tries`, its attempts to first accept (answered tries in answer
    order, through that arm's own first accept), and the requests (retries included) and output chars it spent up to
    there, and the provider's output tokens (output_tokens: thinking included, per adapter) over the answered tries, error rows included in requests and
    chars; problems not solved within `tries` (never counted as `tries`) and owed ones; yield =
    solved / the arm's attempts spent (None when nothing solved); a per-problem Wilson interval. Every series with any
    row shows, an error-only or gone one too. Tries a provider gave no counts for are counted apart (tries_without_tokens)."""
    from collections import defaultdict
    solved = [p for p in sample if cohort_of(p) == "solved"]
    by = defaultdict(lambda: defaultdict(list))
    reqs, gone = defaultdict(int), set()
    for r in rows:
        if cohort_of(r) != "solved" or not r.get("run_week"):
            continue
        key = (r["run_week"], r["chain"], r["lane"])
        reqs[key] += r.get("requests") or 0
        if r.get("verdict") == "lane_gone":
            gone.add(key)
            continue
        by[key][(r["week"], r["target_set"], r["target"])].append(r)
    out = []
    for key in sorted(set(reqs) | gone):
        rep = {"run_week": key[0], "chain": key[1], "lane": key[2], "problems": len(solved), "requests": reqs[key],
               "gone": key in gone, "by_rung": defaultdict(lambda: {"problems": 0, "raw": 0, "assisted": 0})}
        for arm, field in (("raw", "cold"), ("assisted", "verdict")):
            a = {"solved": 0, "attempts_to_first": [], "not_solved_within": 0, "owed": 0, "spent": 0, "requests": 0,
                 "chars": 0, "output_tokens": 0, "tries": 0, "tries_without_tokens": 0, "finished": 0}
            for p in solved:
                allr = sorted(by[key].get((p["week"], p["target_set"], p["target"]), []), key=lambda r: r["ts"])
                answered = [r for r in allr if r.get("verdict") in ("accept", "reject")]
                hit = next((i for i, r in enumerate(answered) if r.get(field) == "accept"), None)
                upto = allr if hit is None else allr[:allr.index(answered[hit]) + 1]
                a["requests"] += sum(r.get("requests") or 0 for r in upto)
                a["chars"] += sum(r.get("response_chars") or 0 for r in upto)
                tried = [r for r in upto if r.get("verdict") in ("accept", "reject")]
                a["output_tokens"] += sum(output_tokens(r) or 0 for r in tried)
                a["tries_without_tokens"] += sum(1 for r in tried if output_tokens(r) is None)
                a["tries"] += len(tried)
                if arm == "raw":
                    rep["by_rung"][p.get("rung")]["problems"] += 1
                if hit is None:
                    a["spent"] += len(answered)
                    a["not_solved_within" if len(answered) >= tries else "owed"] += 1
                    continue
                a["solved"] += 1
                a["spent"] += hit + 1
                a["attempts_to_first"].append(hit + 1)
                rep["by_rung"][p.get("rung")][arm] += 1
            a["attempts_to_first"].sort()
            a["yield"] = round(a["solved"] / a["spent"], 3) if a["solved"] else None
            a["finished"] = a["solved"] + a["not_solved_within"]          # owed problems are not failures
            a["wilson95"] = wilson95(a["solved"], a["finished"])
            rep[arm] = a
        rep["by_rung"] = dict(rep["by_rung"])
        out.append(rep)
    return out


def render_size(report):
    def tok(a):
        """Output tokens, never a 0 that means "not reported"."""
        tries, missing = a["tries"], a["tries_without_tokens"]
        if not tries or missing == tries:
            return "unknown"
        return f"{a['output_tokens']}" + (f" ({missing} of {tries} tries without counts)" if missing else "")
    lines = ["| run week | chain | lane | raw solved (95% CI) | with the chain (95% CI) | raw attempts to first | "
             "chain attempts to first | not solved within 3, raw / chain | requests, raw / chain | chars, raw / chain | "
             "output tokens, raw / chain |", "|---|---|---|---|---|---|---|---|---|---|---|"]
    for r in report:
        f = lambda a: (f"{a['solved']}/{a['finished']} ({a['wilson95'][0]:.2f}-{a['wilson95'][1]:.2f})" if a["wilson95"]
                       else "-") + (f", {a['owed']} owed" if a["owed"] else "")
        lines.append(f"| {r['run_week']} | {r['chain']} | {r['lane']} | {f(r['raw'])} | {f(r['assisted'])} | "
                     f"{', '.join(map(str, r['raw']['attempts_to_first'])) or '-'} | "
                     f"{', '.join(map(str, r['assisted']['attempts_to_first'])) or '-'} | "
                     f"{r['raw']['not_solved_within']} / {r['assisted']['not_solved_within']} | "
                     f"{r['raw']['requests']} / {r['assisted']['requests']} | {r['raw']['chars']} / {r['assisted']['chars']} | "
                     f"{tok(r['raw'])} / {tok(r['assisted'])} |"
                     + (" **lane gone from kumori**" if r["gone"] else ""))
    return "\n".join(lines)


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


def row_ids(run_id, row, seq):
    """try_id: the logical try (run, lane, cohort, problem, try), shared by a refusal and the answer after it;
    answer_id: this one event, unique within the process by seq (Codex 20261024T191033337558Z)."""
    key = [run_id, row["lane"], row.get("cohort"), row.get("week"), row.get("target_set"), row.get("target"), row.get("try")]
    h = lambda v: hashlib.sha256(json.dumps(v).encode()).hexdigest()[:12]
    return {"try_id": h(key), "answer_id": h(key + [seq])}


GONE_EXIT = 3          # --resolve's exit code when a pinned lane is gone; attempt.yml turns it into a red run


def resolve_main(args, run_id, chain, names_ix, lean):
    """The re-solve layer: freeze any newly finished week (and the solved cohort, once), then this slice's owed tries
    for this run week: the weekly series on RESOLVE_LANE, the size series on SIZE_LANES. Returns GONE_EXIT when a
    pinned lane is gone from kumori, after every other lane has had its turn."""
    import attempt, ledger_files
    from utilities.kumori_api_client import llm_chat
    SPEED_DIR.mkdir(parents=True, exist_ok=True)
    frozen = load_jsonl(sorted(SPEED_DIR.glob("sample-*.jsonl")))
    now = datetime.now(timezone.utc).isoformat()
    tries_rows = load_jsonl(ledger_files.try_files(ROOT / "ledger"))
    new = freeze_sample(tries_rows, now, frozen_weekly_weeks(frozen), statement_sha)
    for wk in sorted({s["week"] for s in new}):         # one file a week, written once, the same from every slice
        f = SPEED_DIR / f"sample-{wk}.jsonl"
        if not f.exists():
            f.write_text("".join(json.dumps(s) + "\n" for s in new if s["week"] == wk))
            print(f"resolve: froze {f.name}", flush=True)
    solved_file = SPEED_DIR / f"sample-solved-{SOLVED_CUTOFF[:10]}.jsonl"
    if not solved_file.exists():                         # frozen once; the same from every slice (deterministic)
        picks = freeze_solved(tries_rows, SOLVED_CUTOFF, statement_sha)
        solved_file.write_text("".join(json.dumps(s) + "\n" for s in picks))
        print(f"resolve: froze {solved_file.name}: {len(picks)} solved targets", flush=True)
    sample = [s for s in load_jsonl(sorted(SPEED_DIR.glob("sample-*.jsonl")))
              if statement_sha(s["target_set"], s["target"]) == s["statement_sha"]]
    run_week = week_of(now)
    past = load_jsonl(sorted(SPEED_DIR.glob("resolve-*.jsonl")))
    done, raw = resolved_keys(past), raw_solved(past)
    k, n = (int(x) for x in args.slice.split("/"))
    rev = subprocess.run(["git", "rev-parse", "HEAD"], capture_output=True, text=True, cwd=ROOT).stdout.strip()
    config = {"max_tokens": 4000, "temperature": 0.2, "timeout_s": 60, "client_read_timeout_s": 180}
    tools_hash = file_hash([ROOT / "tools" / f for f in FILES + ("toolscore.py",)])
    lean_env = file_hash(LEAN_ENV)
    out = SPEED_DIR / f"resolve-{run_id}-{k}.jsonl"
    sizes = dict(SIZE_LANES)
    seq = [0]                                            # this process's row count, for unique event ids

    def ask_for(lane):
        def ask(prompt):
            text, backend, inference = llm_chat(lane, [{"role": "user", "content": prompt}],
                                                max_tokens=config["max_tokens"], temperature=config["temperature"],
                                                system=attempt.SYSTEM, app_name="sparebrains", timeout=(10, 180),
                                                timeout_s=config["timeout_s"], include_metadata=True,
                                                request_id=uuid.uuid4().hex)
            return text, {"returned_backend": backend, "inference": inference}
        return ask

    def text_for(s):
        text = (ROOT / "targets" / s["target_set"] / f"{s['target']}.lean").read_text()
        return text, text[:PROOF_SEP.search(text).end()]

    def write(r):
        row = {"ts": datetime.now(timezone.utc).isoformat(timespec="seconds"), "run_id": run_id, "run_week": run_week,
               "chain": chain, "tools_hash": tools_hash, "lean_env": lean_env, "git_rev": rev, "request_config": config,
               "half": "report", "size_b": sizes.get(r["lane"]), **r}
        row.update(row_ids(f"{run_id}-{os.environ.get('GITHUB_RUN_ATTEMPT', '1')}-{k}", row, seq[0]))
        seq[0] += 1
        with out.open("a") as fh:
            fh.write(json.dumps(row) + "\n")
        print(f"[resolve] {row['lane']} {row.get('cohort')} {row.get('target_set')}/{row.get('target')} "
              f"try {row.get('try')}: {row['verdict']}", flush=True)

    chain_fn = lambda proof, prefix, said: run_chain(proof, prefix, said, names_ix, lean)
    deadline = time.time() + 60 * args.max_minutes if args.max_minutes else None
    budget = Budget(args.max_requests)                   # one budget for the whole process, both cohorts

    def round_for(cohort, lanes, stop_at_raw):
        def go(gone):
            solved_keys = raw if stop_at_raw else ()
            queue = []
            for lane in lanes:                           # the union of what any lane still owes, in queue order
                for item in resolve_queue(sample, done, run_week, chain, lane, k, n, cohort=cohort,
                                          raw_solved=solved_keys):
                    if item not in queue:
                        queue.append(item)
            owed = lambda lane, s, t: (run_week, chain, lane, cohort, s["week"], s["target_set"], s["target"], t) \
                not in done and (run_week, chain, lane, cohort, s["week"], s["target_set"], s["target"]) not in solved_keys
            print(f"resolve: run week {run_week}, chain {chain}, {cohort} cohort, lanes {', '.join(lanes)}: "
                  f"{len(queue)} (problem, try) items owed in slice {args.slice}; {budget.left} requests left", flush=True)
            return resolve_round(queue, lanes, ask_for, text_for, lean.judge_text, chain_fn, write, budget, owed,
                                 deadline, stop_at_raw, gone)
        return go
    code = run_rounds([round_for("weekly", [RESOLVE_LANE], False),
                       round_for("solved", [l for l, _ in SIZE_LANES], True)])
    print(f"resolve: {sum(1 for _ in open(out)) if out.exists() else 0} rows in {out.relative_to(ROOT)}, "
          f"{args.max_requests - budget.left} requests", flush=True)
    return code


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--half", choices=["report", "tune"], default="report")
    ap.add_argument("--slice", default="0/1", help="k/N: every Nth stored reject from k, for a matrix of jobs")
    ap.add_argument("--max-minutes", type=float, default=0)
    ap.add_argument("--max-rows", type=int, default=100000)
    ap.add_argument("--speed", action="store_true", help="the speed receipt's frozen weekly sample, whole chain only")
    ap.add_argument("--resolve", action="store_true", help="fresh cold tries on the frozen weekly sample (task #191)")
    ap.add_argument("--resolve-report", action="store_true", help="print the re-solve layer's table (no model, no Lean)")
    ap.add_argument("--max-requests", type=int, default=MAX_REQUESTS, help="--resolve: requests this process may make")
    args = ap.parse_args()
    if args.resolve_report:
        rows = load_jsonl(sorted(SPEED_DIR.glob("resolve-*.jsonl")))
        sample = load_jsonl(sorted(SPEED_DIR.glob("sample-*.jsonl")))
        print(render_speed(speed_report([r for r in rows if cohort_of(r) == "weekly" and r.get("verdict") != "lane_gone"],
                                        [s for s in sample if cohort_of(s) == "weekly"])))
        print("\nThe size series (solved cohort):\n" + render_size(size_report(rows, sample)))
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
