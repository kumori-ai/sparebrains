"""The head-to-head (DECISIONS.md 2026-10-19): the same model, alone and with our tools, on the same problems, the
same day, with the same budget. The receipt behind "our tools make a model better, and cheaper per result".

Each problem gets two arms, run in a random order per problem so the time of day and the API's load fall on both:
  alone  Leanstral writes the whole proof, `CALLS` times at most, stopping at the first the kernel accepts; the
         raw answer is judged, with no fixer and no loop (the model as it is)
  tools  tools/decompose.py on the whole theorem, `CALLS` Leanstral calls at most across every level: steps, the
         fixer, the loop's automation (grind included), recursion
Both are judged by the same kernel (tools/check.py). Per arm: problems solved with a 95% interval; the paired
disagreements (solved by one arm only), which are the test; calls, tokens and seconds per solve.

The set is fixed by a seed: open problems first in the open list's order, then solved ones from the harder rungs
(a solved problem still measures calls and time per solve). The rows (ledger/headtohead/) are measurements, not
tries: `outcome` and `at`, so no try count moves; an open problem either arm solves is recorded as a try of its
arm's lane and published like any other.

    python3 tools/headtohead.py run --open 15 --solved 15 --calls 4 --out ledger/headtohead/run-ID.jsonl
    python3 tools/headtohead.py run --arms alone,lessons --lessons-by conclusion --lane mistral-ministral-8b-2512 ...

`--lane` (kumori #574, 2026-10-29) puts a Kumori router lane in Leanstral's seat for the alone and lessons arms: the
same prompt, budget and judge; the model is whatever the router serves under that name. `--lessons-by` picks the
lessons arm's retrieval (tools/lessons.py: statement, the 2026-10-28 pilot; conclusion, the goal-shape variant with
the problem's stored one-step goals shown where the loop left any); each lessons row records which it got.

`--manifest` (2026-11-08, the skeleton pilot) runs a frozen protocol file instead of flags: lane, arms, calls,
sampling, cohort (a ledger/speed sample) and the schedule, checked before any call. The `skeleton` arm is Burton's
fixed schedule (arXiv 2601.16172, Appendix A): call i asks for a proof that begins with skeleton i, the 16th with
the paper's generic hint, judged raw like `alone`. A chat lane is asked, not locked (the paper prefixes the
completion); each row counts the answers that began as asked (`skeleton_followed`). Codex 20261108T152000037394Z,
20261108T152326970171Z.

    python3 tools/headtohead.py run --manifest ledger/headtohead/manifest-skeleton-pilot-2026-11-08.json --out ...
"""
import argparse, hashlib, json, math, random, re, sys, threading, time
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT), str(ROOT / "tools")]
import decompose, goal_closer, replay, subgoals
from proof_text import PROOF_SEP, extract_proof

CALLS = 4
HARD_RUNGS = ("math-L4", "math-L5", "amc12", "aime", "imo", "custom")
SEED = "headtohead-2026-10-19"
ALONE = {"backend": "mistral-leanstral-1-5", "provider": "mistral", "model": "labs-leanstral-1-5-1",
         "mode": "leanstral", "file": "leanstral"}
LESSONS = {**ALONE, "mode": "lessons", "file": "lessons"}     # the same lane, taught by verified proofs (2026-10-28)
ROUTER_MAX_TOKENS = 4000                                     # the size series' cap (tools/toolscore.py)
SKELETONS = ("", "simp", "intro", "intros", "constructor", "refine ?_", "refine ⟨?_, ?_⟩", "aesop", "norm_num",
             "linarith", "nlinarith", "ring", "ring_nf", "simp\ntry aesop", "simp\ntry nlinarith")   # 2601.16172 A.2
SKELETON_HINT = "Start by simplifying the goal and hypotheses using simp."
MANIFEST_KEYS = ("id", "kind", "lane", "arms", "calls", "max_tokens", "temperature", "top_p", "jobs", "max_minutes",
                 "cohort", "schedule", "claim")


def schedule():
    """The paper's 16 ordered attempts: its 15 skeletons (the empty one first), then the empty one with the hint."""
    return [(k, None) for k in SKELETONS] + [("", SKELETON_HINT)]


def lane_of(backend):
    """A Kumori router lane as the writer: what its rows and verified proofs are filed under."""
    return {"backend": backend, "provider": backend.split("-")[0], "model": None, "mode": "headtohead", "file": "headtohead"}


def router_call(backend, llm_chat, max_tokens=ROUTER_MAX_TOKENS, tries=3, sleep=time.sleep, temperature=0.2):
    """A prompt to a Kumori router lane, answered in leanstral.call_prompt's shape ({text, tokens, finish} or
    {error, reason}). The call is the ladder's cold try (attempt.py: long_call, LADDER_CALL_S): run 40977072274
    asked the default ceiling and the lane's answers were cut at 30 s, which opened the router's breaker. A park
    the router puts a clock on (a 429's spacing, a 503 bench) is waited out, up to relay.PARK_WAIT_S a time and
    `tries` - 1 times across `tries` attempts, as the ladder waits; a refusal with no clock (gate, share) is the call
    lost, not retried. Every answer or error says how many chat POSTs it made (`chat_requests`), apart from the one
    logical call; the client's recovery GETs are not counted (Codex 20261108T152326970171Z f6, 20261108T154012903462Z f6)."""
    import uuid
    import attempt, relay
    from utilities.kumori_api_client import KumoriAPIError

    def call(prompt):
        for i in range(tries):
            try:
                text, served, inf = llm_chat(backend, [{"role": "user", "content": prompt}], max_tokens=max_tokens,
                                             temperature=temperature, system=attempt.SYSTEM, app_name="sparebrains",
                                             timeout=(10, attempt.LADDER_CALL_S + 15), timeout_s=attempt.LADDER_CALL_S,
                                             long_call=True, include_metadata=True, request_id=uuid.uuid4().hex)
                inf = inf or {}
                return {"text": text or "", "tokens": (inf.get("usage") or {}).get("completion_tokens"),
                        "finish": inf.get("finish_reason") or inf.get("finish"), "backend": served, "chat_requests": i + 1}
            except KumoriAPIError as e:
                wait = e.retry_after or 0
                parked = e.status_code in (429, 503) or "RPM spacing" in str(e) or "benched" in str(e)
                if i + 1 < tries and parked and wait > 0:       # a clock longer than PARK_WAIT_S is waited that long, not refused
                    sleep(min(wait, relay.PARK_WAIT_S))        # (Codex f1, 2026-10-30: the void run's bench was 194 s)
                    continue
                return {"error": f"{type(e).__name__}: {str(e)[:160]}", "chat_requests": i + 1,
                        "reason": e.error_code or ("benched" if "benched" in str(e) else f"http_{e.status_code}")}
            except Exception as e:
                return {"error": f"{type(e).__name__}: {str(e)[:160]}", "reason": type(e).__name__, "chat_requests": i + 1}
        return {"error": f"parked on every try ({tries})", "reason": "parked", "chat_requests": tries}
    return call


def theorem_as_goal(target_text):
    """The problem's theorem, renamed `sb_goal`, as decompose takes a goal: the statement through `:= by`."""
    prefix = target_text[:PROOF_SEP.search(target_text).end()]
    decl = subgoals.DECL.search(prefix).start()
    return re.sub(r"^(theorem|lemma)\s+\S+", "theorem sb_goal", prefix[decl:], count=1).rstrip()


def same_set(rows):
    """The exact problems an earlier run measured, in its order (Codex f1, 2026-10-29: a seed re-draws the solved
    problems as the solved list grows, so a replication on 'the same 30' must name them)."""
    seen, out = set(), []
    for r in rows:
        k = (r["target_set"], r["target"])
        if k not in seen:
            seen.add(k)
            out.append({"target_set": r["target_set"], "target": r["target"], "rung": r.get("rung"), "status": r["status"]})
    return out


def pick(targets, n_open, n_solved, exists, slice_=(0, 1), seed=SEED, used=()):
    """The fixed set: open problems in the open list's order, then solved ones from the harder rungs, ordered by
    a hash of `seed` and their name so the choice is the same on every run and owes nothing to their results.
    Slice k/N keeps the open problems whose name hashes to k (always by SEED), so a solve between two slices' runs
    moves none. A replication passes a new seed and `used`, the names earlier runs measured, to draw fresh ones."""
    key = lambda t, sd=SEED: hashlib.sha256(f"{sd}/{t['target_set']}/{t['target']}".encode()).hexdigest()
    k, n = slice_
    opened = [t for t in sorted(targets["open"], key=lambda t: t["order"])
              if exists(t) and int(key(t), 16) % n == k][:n_open]
    solved = sorted((t for t in targets["solved"] if t.get("rung") in HARD_RUNGS and exists(t)
                     and t["target"] not in used), key=lambda t: key(t, seed))[:n_solved]
    return [dict(t, status="open") for t in opened] + [dict(t, status="solved") for t in solved]


class Meter:
    """An asker that counts calls and tokens for one arm of one problem, and keeps what the ledger needs to tell a
    refusal or a cut-off answer from a wrong proof (Codex f3, f4, 2026-10-29): calls with no token count
    (`unmetered`, so the row's tokens are null, never an undercount), errors, answers cut at the cap, lanes served."""
    def __init__(self, call):
        self.call, self.calls, self.tokens, self.lock = call, 0, 0, threading.Lock()
        self.unmetered, self.errors, self.cut, self.served, self.reasons = 0, 0, 0, set(), {}
        self.chat_requests = 0

    def ask(self, prompt):
        r = self.call(prompt)
        with self.lock:
            self.calls += 1
            self.chat_requests += r.get("chat_requests", 1) if isinstance(r, dict) else 1
            if isinstance(r, dict) and "error" not in r:
                if r.get("tokens") is None:
                    self.unmetered += 1
                else:
                    self.tokens += r["tokens"]
                self.cut += r.get("finish") == "length"
                if r.get("backend"):
                    self.served.add(r["backend"])
            else:                                        # an error's usage is unknown too (Codex round 2, f3)
                self.errors += 1
                self.unmetered += 1
                why = (r.get("reason") or r.get("error") or "none")[:60] if isinstance(r, dict) else "none"
                self.reasons[why] = self.reasons.get(why, 0) + 1
        if not isinstance(r, dict) or "error" in r:
            return r if isinstance(r, dict) else None
        import leanstral
        return leanstral.reply(r)


def alone(target_text, ask, judge_text, calls=CALLS, preface=""):
    """(proof file or None, calls to the solve): the whole proof, raw, until one is accepted. `preface` is the
    lessons arm's block (tools/lessons.py), put before the same prompt; the file judged is the target's, unchanged."""
    import leanstral
    for i in range(calls):
        reply = ask(preface + leanstral.PROMPT.format(target=target_text))
        name = re.search(r"theorem\s+(\S+)", target_text).group(1)
        proof = extract_proof(reply, name) if isinstance(reply, str) else None
        if proof:
            cand = target_text[:PROOF_SEP.search(target_text).end()] + "\n" + proof.lstrip("\n")
            if judge_text(cand)["verdict"] == "accept":
                return cand, i + 1
    return None, None


def skeleton_prompt(target_text, skel, hint):
    import leanstral
    p = leanstral.PROMPT.format(target=target_text)
    if skel:
        p += "\n\nThe proof must begin with exactly these tactics, in this order:\n```lean4\n" + skel + "\n```"
    if hint:
        p += "\n\nHint: " + hint
    return p


def skeleton(target_text, ask, judge_text, calls=16):
    """(proof file or None, calls to the solve, answers that began as asked): `alone` with call i asking for the
    schedule's entry i (cycled past 16); an empty skeleton is followed by any proof."""
    name = re.search(r"theorem\s+(\S+)", target_text).group(1)
    sched, followed = schedule(), 0
    for i in range(calls):
        skel, hint = sched[i % len(sched)]
        reply = ask(skeleton_prompt(target_text, skel, hint))
        proof = extract_proof(reply, name) if isinstance(reply, str) else None
        if proof is None:
            continue
        lines = [l.strip() for l in proof.strip().splitlines() if l.strip()]
        want = skel.splitlines()
        followed += lines[:len(want)] == want
        cand = target_text[:PROOF_SEP.search(target_text).end()] + "\n" + proof.lstrip("\n")
        if judge_text(cand)["verdict"] == "accept":
            return cand, i + 1, followed
    return None, None, followed


def check_manifest(m):
    """The frozen protocol, refused before any call when a key is missing, the schedule is not the paper's, or it
    claims a top_p the router never sends (kumori _backends.py passes none; Codex 20261108T152326970171Z f1)."""
    missing = [k for k in MANIFEST_KEYS if k not in m]
    assert not missing, f"manifest misses {missing}"
    assert [tuple(e) for e in m["schedule"]] == schedule(), "manifest schedule is not 2601.16172 Appendix A"
    assert isinstance(m["top_p"], str), "top_p: the router sends none, so it is recorded as unreported, never a value"
    assert all(a in ARMS for a in m["arms"]) and "alone" in m["arms"] and len(m["arms"]) >= 2
    return m


def cohort(path):
    """The problems of a ledger/speed sample, in its order, as solved problems."""
    rows = [json.loads(l) for l in (ROOT / path).read_text().splitlines() if l.strip()]
    return [{"target_set": r["target_set"], "target": r["target"], "rung": r.get("rung"), "status": "solved"} for r in rows]


def refused_row(m, why):
    """A run the lane budget refused before any call: one void row, so the ledger says it was tried, and no claim."""
    return {"at": datetime.now(timezone.utc).isoformat(timespec="seconds"), "manifest": m["id"], "arm": None,
            "target": None, "void": "preflight", "reason": str(why)[:300], "claim": m["claim"]}


def refused_summary(m, row, expected):
    """The last line of a refused run: what a cut run reports, with nothing measured."""
    return {"manifest": m["id"], "claim": m["claim"], "chat_requests": 0,
            **summary([row], tuple(m["arms"]), expected=expected)}


def with_tools(target_text, ask, run_lean, judge_text, fix=None, calls=CALLS):
    """(proof file or None, calls used): decomposition on the whole theorem within the same call budget."""
    prefix = target_text[:PROOF_SEP.search(target_text).end()]
    budget = {"asks": 0, "max": calls}
    body = decompose.decompose(theorem_as_goal(target_text), prefix, ask=ask, run_lean=run_lean,
                               judge_text=judge_text, budget=budget, fix=fix)
    if not body:
        return None, None
    cand = prefix + "\n" + body.lstrip("\n")
    return (cand, budget["asks"]) if judge_text(cand)["verdict"] == "accept" else (None, None)


ARMS = ("alone", "tools", "lessons", "skeleton")


BREAKER = 12          # consecutive errored calls before the lane is read as down: 3 problems' arms at 4 calls, ~1 h of parks


def run(problems, read_target, call, run_lean, judge_text, fix=None, calls=CALLS, jobs=3, arms=("alone", "tools"),
        lesson_block=None, writer=None, deadline=None, breaker=BREAKER, extra=None):
    """Every arm in `arms` on every problem, in a random order per problem (seeded). The lessons arm is `alone` with
    tools/lessons.py's block in front (`lesson_block(target_set, target, text)` -> str), never the problem's own
    proof. Returns (rows, solves). Bounded two ways (run 40980090085, 2026-10-30: a lane that answered nothing was
    asked for 5 h 38 min, nothing printed, the job's timeout cancelled it and nothing was published): past `deadline`
    (time.monotonic) no call is made, and after `breaker` consecutive errored calls the lane is down and not called
    again; an arm any such refusal touched is a row marked `void` (deadline / lane_down), kept for the record and
    left out of every count and pair; an arm not started is no row. Every arm prints one line when it ends."""
    state = {"errors": 0, "down": None, "lock": threading.Lock()}

    def refusal():
        if deadline is not None and time.monotonic() > deadline:
            return "deadline"
        return state["down"]

    def guarded(prompt):
        why = refusal()
        if why:
            return {"error": f"not asked: {why}", "reason": why, "chat_requests": 0}
        r = call(prompt)
        with state["lock"]:
            if not isinstance(r, dict) or "error" in r:
                state["errors"] += 1
                if breaker and state["errors"] >= breaker and not state["down"]:
                    state["down"] = "lane_down"
                    print(f"lane down: {breaker} consecutive errored calls; the rest of the run is void", flush=True)
            else:
                state["errors"] = 0
        return r

    def one(t):
        text = read_target(t["target_set"], t["target"])
        order = list(arms)
        random.Random(f"{SEED}/{t['target']}").shuffle(order)
        rows, solves = [], []
        for arm in order:
            if refusal():                                # not started: no row, the summary says how many were measured
                continue
            m, t0, meta = Meter(guarded), time.monotonic(), None
            if arm == "alone":
                cand, k = alone(text, m.ask, judge_text, calls)
            elif arm == "skeleton":
                cand, k, meta = skeleton(text, m.ask, judge_text, calls)
            elif arm == "lessons":
                pre = lesson_block(t["target_set"], t["target"], text)
                pre, meta = pre if isinstance(pre, tuple) else (pre, None)      # (block, how it was retrieved)
                cand, k = alone(text, m.ask, judge_text, calls, preface=pre)
            else:
                cand, k = with_tools(text, m.ask, run_lean, judge_text, fix, calls)
            rows.append({"at": datetime.now(timezone.utc).isoformat(timespec="seconds"), "arm": arm,
                         "target_set": t["target_set"], "target": t["target"], "rung": t.get("rung"),
                         "status": t["status"], "outcome": "solved" if cand else "failed", "calls_to_solve": k,
                         "calls": m.calls, "tokens": None if m.unmetered else m.tokens,
                         "seconds": round(time.monotonic() - t0, 1), "errors": m.errors, "cut": m.cut,
                         "reasons": m.reasons, "chat_requests": m.chat_requests,
                         **({"writer": writer, "served": sorted(m.served)} if writer else {}),
                         **({"skeleton_followed": meta} if arm == "skeleton" else
                            {"lessons": meta} if meta is not None else {}), **(extra or {})})
            void = next((w for w in ("deadline", "lane_down") if w in m.reasons), None)
            if void:
                rows[-1]["void"] = void
            print(f"{t['target']} {arm}: {rows[-1]['outcome']}{' (void: ' + void + ')' if void else ''} "
                  f"calls={m.calls} errors={m.errors} {rows[-1]['seconds']}s"
                  + (f" every call errored {m.reasons}" if m.errors == m.calls and m.calls else ""), flush=True)
            if cand and t["status"] == "open" and not void:
                solves.append((arm, t, cand))
        return rows, solves

    with ThreadPoolExecutor(jobs) as pool:
        out = list(pool.map(one, problems))
    return [r for rs, _ in out for r in rs], [s for _, ss in out for s in ss]


def sign_p(only_a, only_b):
    """Two-sided exact sign test (exact McNemar) on the problems only one arm solved."""
    n, k = only_a + only_b, min(only_a, only_b)
    return min(1.0, 2 * sum(math.comb(n, i) for i in range(k + 1)) / 2 ** n) if n else 1.0


def wilson(k, n, z=1.96):
    if not n:
        return (None, None)
    p = k / n
    d = 1 + z * z / n
    c = (p + z * z / (2 * n)) / d
    h = z * math.sqrt(p * (1 - p) / n + z * z / (4 * n * n)) / d
    return (round(100 * (c - h), 1), round(100 * (c + h), 1))


def baseline_or_why(ledger):
    """The no-model baseline for a report, or why there is none: a report never fails for want of it."""
    try:
        return replay.no_model_set(ledger), None
    except ValueError as e:
        return None, str(e)


def summary(rows, arms=None, expected=None, baseline=None):
    """Per arm: solved, interval, calls/tokens/seconds per solve; and the paired disagreements. Void rows (a
    deadline or a lane down touched the arm) are counted apart, and a problem is paired only when every configured
    arm (`arms`; the arms seen in the rows when not given) has a measured row for it: a treatment arm that finished
    before the cutoff while its control never started is no win (Codex 20261101T180816309622Z f5)."""
    void = [r for r in rows if r.get("void")]
    arms_ran = set(arms) if arms else {r["arm"] for r in rows}
    measured = [r for r in rows if not r.get("void")]
    complete = {n for n in {r["target"] for r in measured if r.get("target")}
                if {r["arm"] for r in measured if r["target"] == n} == arms_ran}
    rows = [r for r in measured if r["target"] in complete]
    by = {arm: [] for arm in sorted(arms_ran)}             # an arm that ran shows, even with nothing measured
    for r in rows:
        by.setdefault(r["arm"], []).append(r)
    out = {}
    for arm, rs in by.items():
        won = [r for r in rs if r["outcome"] == "solved"]
        per = lambda f: None if not won or any(r.get(f) is None for r in rs) else round(sum(r[f] for r in rs) / len(won), 1)
        out[arm] = {"problems": len(rs), "solved": len(won), "pct_ci": wilson(len(won), len(rs)),
                    "calls_per_solve": per("calls"), "tokens_per_solve": per("tokens"),
                    "seconds_per_solve": per("seconds"), "calls_total": sum(r["calls"] for r in rs)}
    solved = {(r["target"], r["arm"]) for r in rows if r["outcome"] == "solved"}
    names = {r["target"] for r in rows}
    # The paired test is between the treatment arm that ran (tools or lessons) and alone; a run with both treatment
    # arms reports each against alone (Codex f1, 2026-10-28: the old code compared tools vs alone whatever ran).
    for arm in ("tools", "lessons", "skeleton"):
        if arm not in by:
            continue
        only_t = sorted(n for n in names if (n, arm) in solved and (n, "alone") not in solved)
        only_a = sorted(n for n in names if (n, "alone") in solved and (n, arm) not in solved)
        out[f"only_{arm}"], out[f"only_alone_vs_{arm}"] = only_t, only_a
        out[f"p_{arm}"] = round(sign_p(len(only_t), len(only_a)), 4)
    if "tools" in by:                                   # the names earlier runs and tests read
        out["only_alone"], out["p"] = out["only_alone_vs_tools"], out["p_tools"]
    out["problems_paired"], out["void_rows"] = len(complete), len(void)
    if expected is not None:                            # a run cut by quota or the clock says so (Codex f5)
        out["complete"] = len(complete) == expected
    if baseline is not None:
        # beside the totals, never instead (#574): the same paired read on targets the no-model baseline did not prove
        key = lambda r: (r.get("target_set"), r["target"])
        out["in_baseline"] = len({key(r) for r in rows if key(r) in baseline["set"]})
        out["off_baseline"] = summary([r for r in rows if key(r) not in baseline["set"]], tuple(sorted(arms_ran)))
        out["off_baseline_means"], out["baseline"] = replay.OFF_BASELINE_MEANS, baseline["version"]
    return out


def record(solves, run_id, judge_text, writer=ALONE):
    """An open problem either arm solved: a try of its arm's lane, with the proof in verified/ and the site."""
    import prover
    post = None
    try:
        from utilities.kumori_api_client import init, sparebrains_attempt
        init()
        post = sparebrains_attempt
    except Exception as e:
        print(f"site recording off ({type(e).__name__}); the ledger still gets every row", flush=True)
    for arm, t, cand in solves:
        lane = writer if arm == "alone" else {**writer, "mode": "lessons", "file": "lessons"} if arm == "lessons" else decompose.LANE
        rec = prover.Recorder(f"headtohead-{run_id}", post, lane)
        prefix = cand[:PROOF_SEP.search(cand).end()]
        r = judge_text(cand)                                  # the kernel again, on the way in
        a = {"batch": run_id, "target_set": t["target_set"], "target": t["target"], "sample": 0, "text": cand}
        row = {**prover.base_row(a, f"headtohead-{run_id}", prefix, lane), "try_mode": f"headtohead-{arm}",
               "verdict": r["verdict"], "reason": (r.get("reason") or "")[:300], "lean_seconds": r.get("seconds"),
               "proof_sha": hashlib.sha256(cand.encode()).hexdigest()}
        rec(row, cand, cand, cand, r.get("output"))
        if r["verdict"] == "accept":
            rec.verified(t["target_set"], t["target"], cand)


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("cmd", choices=["run"])
    ap.add_argument("--open", type=int, default=15)
    ap.add_argument("--solved", type=int, default=15)
    ap.add_argument("--calls", type=int, default=CALLS)
    ap.add_argument("--slice", default="0/1", help="k/N: the open problems whose name hashes to k (a run too long for one job)")
    ap.add_argument("--seed", default=SEED, help="a replication's own seed: its solved problems skip every one an "
                    "earlier run in ledger/headtohead/ measured")
    ap.add_argument("--arms", default="alone,tools", help="comma-separated from alone, tools, lessons")
    ap.add_argument("--lessons", type=int, default=3, help="lessons arm: solved theorems shown")
    ap.add_argument("--lessons-by", default="statement", help="lessons arm: statement (the pilot) or conclusion (goal shape)")
    ap.add_argument("--lane", default="", help="a Kumori router lane in Leanstral's seat for alone and lessons (needs KUMORI_API_KEY)")
    ap.add_argument("--max-minutes", type=float, default=300,
                    help="the run's clock, inside the job's 340: past it nothing new is asked and what finished is published")
    ap.add_argument("--same-as", default="", help="run id: the exact problems that run measured, in its order (--open/--solved/--seed/--slice unused)")
    ap.add_argument("--manifest", default="", help="a frozen protocol file: lane, arms, calls, sampling, cohort, schedule")
    ap.add_argument("--out", required=True)
    a = ap.parse_args()
    import fixer, lean_tools, leanstral, relay
    man = None
    if a.manifest:
        man = check_manifest(json.loads((ROOT / a.manifest).read_text()))
        a.lane, a.arms, a.calls, a.max_minutes = man["lane"], ",".join(man["arms"]), man["calls"], man["max_minutes"]
        print(f"manifest {man['id']} ({man['kind']}): {a.lane}, arms {a.arms}, {a.calls} calls, "
              f"max_tokens {man['max_tokens']}, temperature {man['temperature']}, top_p {man['top_p']}; claim: {man['claim']}", flush=True)
    arms = tuple(x.strip() for x in a.arms.split(",") if x.strip())
    assert all(x in ARMS for x in arms) and len(arms) >= 2, f"--arms from {ARMS}, at least two"
    assert not (a.lane and "tools" in arms), "--lane runs the alone and lessons arms only (the tools arm is Leanstral's)"
    lesson_block = None
    if "lessons" in arms:
        import lessons
        assert a.lessons_by in lessons.BY, f"--lessons-by from {lessons.BY}"
        ix = lessons.index()
        print(f"lessons: {len(ix)} solved targets in the index, retrieval by {a.lessons_by}", flush=True)

        def lesson_block(tset, name, text):
            key = f"{tset}/{name}"
            goals = lessons.goals_for(key) if a.lessons_by == "conclusion" else []
            return (lessons.block(ix, text, a.lessons, exclude=key, by=a.lessons_by, goals=goals),
                    {"by": a.lessons_by, "goals": len(goals)})
    writer = ALONE
    if a.lane:
        from utilities.kumori_api_client import init as kumori_init, llm_chat
        kumori_init()
        writer = lane_of(a.lane)
        call = (router_call(a.lane, llm_chat, max_tokens=man["max_tokens"], temperature=man["temperature"]) if man
                else router_call(a.lane, llm_chat))
        print(f"writer: {a.lane} via the kumori router", flush=True)
    else:
        key = leanstral.key_from_env()
    targets = relay.fetch_json("/targets.json")
    path = lambda t: ROOT / "targets" / t["target_set"] / f"{t['target']}.lean"
    used = set() if a.seed == SEED else {json.loads(l)["target"] for f in (ROOT / "ledger" / "headtohead").glob("*.jsonl")
                                         for l in open(f) if l.strip()}
    if man:
        problems = [t for t in cohort(man["cohort"]) if path(t).exists()]
        print(f"set: {len(problems)} problems of {man['cohort']}", flush=True)
    elif a.same_as:
        f = ROOT / "ledger" / "headtohead" / f"run-{a.same_as}.jsonl"
        problems = [t for t in same_set(json.loads(l) for l in f.read_text().splitlines() if l.strip()) if path(t).exists()]
        print(f"set: the {len(problems)} problems of run {a.same_as}", flush=True)
    else:
        problems = pick(targets, a.open, a.solved, lambda t: path(t).exists(), tuple(int(x) for x in a.slice.split("/")),
                        a.seed, used)
    if a.lane:      # every call an arm may make, errors included, against the lane's daily cap (lane_budget, 2026-11-03)
        import lane_budget
        from utilities.kumori_api_client import llm_backends, llm_backoff_state, llm_usage
        try:
            lane_budget.preflight(a.lane, len(problems) * len(arms) * a.calls, llm_usage, llm_backoff_state, catalog_fn=llm_backends)
        except SystemExit as e:
            if not man:
                raise
            Path(a.out).parent.mkdir(parents=True, exist_ok=True)
            row = refused_row(man, e.code)
            with open(a.out, "a") as f:
                f.write(json.dumps(row, ensure_ascii=False) + "\n")
            print(f"lane budget refused: {e.code}", flush=True)
            print("headtohead: " + json.dumps({"writer": writer["backend"], **refused_summary(man, row, len(problems))}))
            return 0
    pacer = leanstral.Pacer(leanstral.MIN_GAP_S)
    if not a.lane:
        def call(prompt):
            try:
                return leanstral.call_prompt(key, prompt, pacer)
            except Exception as e:
                return {"error": f"{type(e).__name__}: {str(e)[:160]}"}

    names_ix = lean_tools.index()
    rows, solves = run(problems, lambda s, t: (ROOT / "targets" / s / f"{t}.lean").read_text(), call,
                       lean_tools.run_lean, lean_tools.judge_text,
                       fix=lambda proof, out: fixer.fix(proof, out, *names_ix), calls=a.calls, arms=arms,
                       lesson_block=lesson_block, writer=writer["backend"], jobs=man["jobs"] if man else 3,
                       extra={"manifest": man["id"], "requested": {"max_tokens": man["max_tokens"],
                              "temperature": man["temperature"], "top_p": man["top_p"]}} if man else None,
                       deadline=time.monotonic() + 60 * a.max_minutes if a.max_minutes else None)
    Path(a.out).parent.mkdir(parents=True, exist_ok=True)
    with open(a.out, "a") as f:
        f.writelines(json.dumps(r, ensure_ascii=False) + "\n" for r in rows)
    if solves:
        record(solves, datetime.now(timezone.utc).strftime("%Y%m%dT%H%M"), lean_tools.judge_text, writer)
    base, why = baseline_or_why(ROOT / "ledger")
    s = {"writer": writer["backend"], **({"lessons_by": a.lessons_by} if "lessons" in arms else {}),
         **({"manifest": man["id"], "claim": man["claim"], "chat_requests": sum(r["chat_requests"] for r in rows)} if man else {}),
         **summary(rows, arms, expected=len(problems) if man else None, baseline=base)}
    if why:
        s["baseline_missing"] = why
    print("headtohead: " + json.dumps(s) + (f"; Leanstral stopped: {pacer.stop}" if pacer.stop else ""))
    return 0


if __name__ == "__main__":
    sys.exit(main())
