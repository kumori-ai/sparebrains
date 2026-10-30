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
"""
import argparse, hashlib, json, math, random, re, sys, threading, time
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT), str(ROOT / "tools")]
import decompose, goal_closer, subgoals
from proof_text import PROOF_SEP, extract_proof

CALLS = 4
HARD_RUNGS = ("math-L4", "math-L5", "amc12", "aime", "imo", "custom")
SEED = "headtohead-2026-10-19"
ALONE = {"backend": "mistral-leanstral-1-5", "provider": "mistral", "model": "labs-leanstral-1-5-1",
         "mode": "leanstral", "file": "leanstral"}
LESSONS = {**ALONE, "mode": "lessons", "file": "lessons"}     # the same lane, taught by verified proofs (2026-10-28)
ROUTER_MAX_TOKENS, ROUTER_WAIT_S = 4000, 300                 # the size series' cap (tools/toolscore.py); a 429's longest wait


def lane_of(backend):
    """A Kumori router lane as the writer: what its rows and verified proofs are filed under."""
    return {"backend": backend, "provider": backend.split("-")[0], "model": None, "mode": "headtohead", "file": "headtohead"}


def router_call(backend, llm_chat, max_tokens=ROUTER_MAX_TOKENS, tries=3, sleep=time.sleep):
    """A prompt to a Kumori router lane, answered in leanstral.call_prompt's shape ({text, tokens, finish} or
    {error}). A 429 with a clock is waited out up to `tries` times, as attempt.make_ask does; any other refusal
    (gate, bench, share) is an error, not a retry: a refused call is a call the arm lost."""
    import uuid
    import attempt
    from utilities.kumori_api_client import KumoriAPIError

    def call(prompt):
        for i in range(tries):
            try:
                text, served, inf = llm_chat(backend, [{"role": "user", "content": prompt}], max_tokens=max_tokens,
                                             temperature=0.2, system=attempt.SYSTEM, app_name="sparebrains",
                                             timeout=(10, 180), timeout_s=60, include_metadata=True,
                                             request_id=uuid.uuid4().hex)
                inf = inf or {}
                return {"text": text or "", "tokens": (inf.get("usage") or {}).get("completion_tokens"),
                        "finish": inf.get("finish_reason") or inf.get("finish"), "backend": served}
            except KumoriAPIError as e:
                wait = e.retry_after or 0
                if i + 1 < tries and (e.status_code == 429 or "RPM spacing" in str(e)) and 0 < wait <= ROUTER_WAIT_S:
                    sleep(wait)
                    continue
                return {"error": f"{type(e).__name__}: {str(e)[:160]}"}
            except Exception as e:
                return {"error": f"{type(e).__name__}: {str(e)[:160]}"}
        return {"error": "refused: 429 on every try"}
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
        self.unmetered, self.errors, self.cut, self.served = 0, 0, 0, set()

    def ask(self, prompt):
        r = self.call(prompt)
        with self.lock:
            self.calls += 1
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


ARMS = ("alone", "tools", "lessons")


def run(problems, read_target, call, run_lean, judge_text, fix=None, calls=CALLS, jobs=3, arms=("alone", "tools"),
        lesson_block=None, writer=None):
    """Every arm in `arms` on every problem, in a random order per problem (seeded). The lessons arm is `alone` with
    tools/lessons.py's block in front (`lesson_block(target_set, target, text)` -> str), never the problem's own
    proof. Returns (rows, solves)."""
    def one(t):
        text = read_target(t["target_set"], t["target"])
        order = list(arms)
        random.Random(f"{SEED}/{t['target']}").shuffle(order)
        rows, solves = [], []
        for arm in order:
            m, t0, meta = Meter(call), time.monotonic(), None
            if arm == "alone":
                cand, k = alone(text, m.ask, judge_text, calls)
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
                         **({"writer": writer, "served": sorted(m.served)} if writer else {}),
                         **({"lessons": meta} if meta is not None else {})})
            if cand and t["status"] == "open":
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


def summary(rows):
    """Per arm: solved, interval, calls/tokens/seconds per solve; and the paired disagreements."""
    by = {}
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
    for arm in ("tools", "lessons"):
        if arm not in by:
            continue
        only_t = sorted(n for n in names if (n, arm) in solved and (n, "alone") not in solved)
        only_a = sorted(n for n in names if (n, "alone") in solved and (n, arm) not in solved)
        out[f"only_{arm}"], out[f"only_alone_vs_{arm}"] = only_t, only_a
        out[f"p_{arm}"] = round(sign_p(len(only_t), len(only_a)), 4)
    if "tools" in by:                                   # the names earlier runs and tests read
        out["only_alone"], out["p"] = out["only_alone_vs_tools"], out["p_tools"]
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
    ap.add_argument("--same-as", default="", help="run id: the exact problems that run measured, in its order (--open/--solved/--seed/--slice unused)")
    ap.add_argument("--out", required=True)
    a = ap.parse_args()
    import fixer, lean_tools, leanstral, relay
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
        writer, call = lane_of(a.lane), router_call(a.lane, llm_chat)
        print(f"writer: {a.lane} via the kumori router", flush=True)
    else:
        key = leanstral.key_from_env()
    targets = relay.fetch_json("/targets.json")
    path = lambda t: ROOT / "targets" / t["target_set"] / f"{t['target']}.lean"
    used = set() if a.seed == SEED else {json.loads(l)["target"] for f in (ROOT / "ledger" / "headtohead").glob("*.jsonl")
                                         for l in open(f) if l.strip()}
    if a.same_as:
        f = ROOT / "ledger" / "headtohead" / f"run-{a.same_as}.jsonl"
        problems = [t for t in same_set(json.loads(l) for l in f.read_text().splitlines() if l.strip()) if path(t).exists()]
        print(f"set: the {len(problems)} problems of run {a.same_as}", flush=True)
    else:
        problems = pick(targets, a.open, a.solved, lambda t: path(t).exists(), tuple(int(x) for x in a.slice.split("/")),
                        a.seed, used)
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
                       lesson_block=lesson_block, writer=writer["backend"])
    Path(a.out).parent.mkdir(parents=True, exist_ok=True)
    with open(a.out, "a") as f:
        f.writelines(json.dumps(r, ensure_ascii=False) + "\n" for r in rows)
    if solves:
        record(solves, datetime.now(timezone.utc).strftime("%Y%m%dT%H%M"), lean_tools.judge_text, writer)
    s = {"writer": writer["backend"], **({"lessons_by": a.lessons_by} if "lessons" in arms else {}), **summary(rows)}
    print("headtohead: " + json.dumps(s) + (f"; Leanstral stopped: {pacer.stop}" if pacer.stop else ""))
    return 0


if __name__ == "__main__":
    sys.exit(main())
