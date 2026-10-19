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
"""
import argparse, hashlib, json, math, os, random, re, sys, threading, time
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


def theorem_as_goal(target_text):
    """The problem's theorem, renamed `sb_goal`, as decompose takes a goal: the statement through `:= by`."""
    prefix = target_text[:PROOF_SEP.search(target_text).end()]
    decl = subgoals.DECL.search(prefix).start()
    return re.sub(r"^(theorem|lemma)\s+\S+", "theorem sb_goal", prefix[decl:], count=1).rstrip()


def pick(targets, n_open, n_solved, exists):
    """The fixed set: open problems in the open list's order, then solved ones from the harder rungs, ordered by
    a hash of SEED and their name so the choice is the same on every run and owes nothing to their results."""
    opened = [t for t in sorted(targets["open"], key=lambda t: t["order"]) if exists(t)][:n_open]
    key = lambda t: hashlib.sha256(f"{SEED}/{t['target_set']}/{t['target']}".encode()).hexdigest()
    solved = sorted((t for t in targets["solved"] if t.get("rung") in HARD_RUNGS and exists(t)), key=key)[:n_solved]
    return [dict(t, status="open") for t in opened] + [dict(t, status="solved") for t in solved]


class Meter:
    """A Leanstral asker that counts calls and tokens for one arm of one problem."""
    def __init__(self, call):
        self.call, self.calls, self.tokens, self.lock = call, 0, 0, threading.Lock()

    def ask(self, prompt):
        r = self.call(prompt)
        with self.lock:
            self.calls += 1
            self.tokens += (r.get("tokens") or 0) if isinstance(r, dict) else 0
        if not isinstance(r, dict) or "error" in r:
            return r if isinstance(r, dict) else None
        import leanstral
        return leanstral.reply(r)


def alone(target_text, ask, judge_text, calls=CALLS):
    """(proof file or None, calls to the solve): the whole proof, raw, until one is accepted."""
    import leanstral
    for i in range(calls):
        reply = ask(leanstral.PROMPT.format(target=target_text))
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


def run(problems, read_target, call, run_lean, judge_text, fix=None, calls=CALLS, jobs=3):
    """Both arms on every problem, in a random order per problem (seeded). Returns (rows, solves)."""
    def one(t):
        text = read_target(t["target_set"], t["target"])
        order = ["alone", "tools"]
        random.Random(f"{SEED}/{t['target']}").shuffle(order)
        rows, solves = [], []
        for arm in order:
            m, t0 = Meter(call), time.monotonic()
            if arm == "alone":
                cand, k = alone(text, m.ask, judge_text, calls)
            else:
                cand, k = with_tools(text, m.ask, run_lean, judge_text, fix, calls)
            rows.append({"at": datetime.now(timezone.utc).isoformat(timespec="seconds"), "arm": arm,
                         "target_set": t["target_set"], "target": t["target"], "rung": t.get("rung"),
                         "status": t["status"], "outcome": "solved" if cand else "failed", "calls_to_solve": k,
                         "calls": m.calls, "tokens": m.tokens, "seconds": round(time.monotonic() - t0, 1)})
            if cand and t["status"] == "open":
                solves.append((arm, t, cand))
        return rows, solves

    with ThreadPoolExecutor(jobs) as pool:
        out = list(pool.map(one, problems))
    return [r for rs, _ in out for r in rs], [s for _, ss in out for s in ss]


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
        per = lambda f: round(sum(r[f] for r in rs) / len(won), 1) if won else None
        out[arm] = {"problems": len(rs), "solved": len(won), "pct_ci": wilson(len(won), len(rs)),
                    "calls_per_solve": per("calls"), "tokens_per_solve": per("tokens"),
                    "seconds_per_solve": per("seconds"), "calls_total": sum(r["calls"] for r in rs)}
    solved = {(r["target"], r["arm"]) for r in rows if r["outcome"] == "solved"}
    names = {r["target"] for r in rows}
    out["only_tools"] = sorted(n for n in names if (n, "tools") in solved and (n, "alone") not in solved)
    out["only_alone"] = sorted(n for n in names if (n, "alone") in solved and (n, "tools") not in solved)
    return out


def record(solves, run_id, judge_text):
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
        lane = ALONE if arm == "alone" else decompose.LANE
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
    ap.add_argument("--out", required=True)
    a = ap.parse_args()
    key = os.environ.get("SPAREBRAINS_LEANSTRAL_KEY", "").strip()
    if not key:
        sys.exit("SPAREBRAINS_LEANSTRAL_KEY is not set")
    import fixer, lean_tools, leanstral, relay
    targets = relay.fetch_json("/targets.json")
    path = lambda t: ROOT / "targets" / t["target_set"] / f"{t['target']}.lean"
    problems = pick(targets, a.open, a.solved, lambda t: path(t).exists())
    pacer = leanstral.Pacer(leanstral.MIN_GAP_S)

    def call(prompt):
        try:
            return leanstral.call_prompt(key, prompt, pacer)
        except Exception as e:
            return {"error": f"{type(e).__name__}: {str(e)[:160]}"}

    names_ix = lean_tools.index()
    rows, solves = run(problems, lambda s, t: (ROOT / "targets" / s / f"{t}.lean").read_text(), call,
                       lean_tools.run_lean, lean_tools.judge_text,
                       fix=lambda proof, out: fixer.fix(proof, out, *names_ix), calls=a.calls)
    Path(a.out).parent.mkdir(parents=True, exist_ok=True)
    with open(a.out, "a") as f:
        f.writelines(json.dumps(r, ensure_ascii=False) + "\n" for r in rows)
    if solves:
        record(solves, datetime.now(timezone.utc).strftime("%Y%m%dT%H%M"), lean_tools.judge_text)
    s = summary(rows)
    print("headtohead: " + json.dumps(s) + (f"; Leanstral stopped: {pacer.stop}" if pacer.stop else ""))
    return 0


if __name__ == "__main__":
    sys.exit(main())
