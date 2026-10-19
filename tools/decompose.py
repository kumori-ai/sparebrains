"""Decomposition (roadmap #8; DECISIONS.md 2026-10-19): the steps the loop left open, broken into smaller steps
until Lean's automation can take them.

The diagnosis of 2026-10-19 found the 223 open real-step goals are not one lemma away (Lean's `apply?` named only
restructuring lemmas; one-shot tactics, plain or hinted, closed what they could). So a model writes steps: Leanstral
(Mistral's open Lean prover, $0 on its Labs API, tools/leanstral.py) is asked for the goal as short `have` steps.
The kernel judges; if it rejects, the loop's Lean-only pass (subgoals.repair, no model) turns the failing steps into
holes and closes what automation can; each step still open becomes a goal of its own, one level down, until the
depth or the ask budget runs out. A proved goal is spliced into its problem's sketches by goal_closer.close, so the
kernel decides every solve. The approach of Hilbert (arXiv 2509.22819) and DeepSeek-Prover-V2's subgoals, on our
own loop.

Problems in the stage-3 bar's 50 are skipped until it is graded (2026-10-24 18:30 UTC). Each goal tried is one
measurement row in ledger/decompose/ (outcome, at: not a try, so no try count moves); a solve is recorded as a
goal-closer try through prover.judge_goals, the goal batches' own path.

    python3 tools/decompose.py run --max-goals 40 --out ledger/decompose/run-ID.jsonl   # needs SPAREBRAINS_LEANSTRAL_KEY
"""
import argparse, json, os, re, sys, time
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT), str(ROOT / "tools")]
import goal_closer, subgoals
from proof_text import extract_proof

DEPTH = 2              # a goal's steps, and their steps: deeper did not pay in Hilbert's ablation past a few levels
MAX_ASKS = 8           # model calls per top goal, across every level
WORKERS = 3            # goals at once; each Leanstral call takes ~45 s, so starts stay under 0.5 a second
TACTICS = subgoals.AUTO_TACTICS            # grind among them since the stage-3 bar was graded (2026-10-19)
STEPS = ("Prove the following Lean 4 lemma. Write the proof as a short sequence of `have` steps, each small "
         "enough that one of linarith, nlinarith, omega, norm_num, simp, positivity or grind closes it, then "
         "finish from those steps. Reply with the whole lemma in one ```lean4 block: exactly the statement below, "
         "then `:= by` and tactics. No `sorry`. Lean 4 and current mathlib names only.\n\n```lean4\n{statement}\n```")
LANE = {"backend": "leanstral-decompose", "provider": "mistral", "model": "labs-leanstral-1-5-1",
        "mode": "goal-closer", "file": "decompose"}


def lemma_prefix(prefix, statement):
    """The text before a lemma's proof: the target's header, then the statement (which ends `:= by`)."""
    return subgoals.lemma_file(prefix, statement, "")


def body_of(text, statement_prefix):
    """The proof lines of a lemma file, as a body for close()."""
    return text[len(statement_prefix):].lstrip("\n")


RETRY = ("\n\nYour previous proof:\n```lean4\n{last}\n```\nLean said:\n```\n{said}\n```\nWrite it again as smaller "
         "steps, keeping the ones Lean accepted.")


def decompose(statement, prefix, *, ask, run_lean, judge_text, depth=DEPTH, budget=None, log=None, fix=None,
              _last=None):
    """A proof body for `statement` (a `theorem sb_goal ... := by`), or None. `log` collects what happened at
    each level: asks, how far the kernel got, the steps left. A level that cannot be taken apart is asked once
    more with Lean's error (prove_goal's second ask; APOLLO's repair loop). `fix` is the loop's form repair."""
    budget = budget if budget is not None else {"asks": 0}
    log = log if log is not None else []
    if budget["asks"] >= budget.get("max", MAX_ASKS):
        log.append({"depth": depth, "stopped": "ask budget"})
        return None
    budget["asks"] += 1
    prompt = STEPS.format(statement=statement)
    if _last:
        prompt += RETRY.format(last=_last[0][-2500:], said=_last[1][-1500:])
    reply = ask(prompt)
    if not isinstance(reply, str) or not reply:
        log.append({"depth": depth, "stopped": "no answer" + (f": {reply['error']}" if isinstance(reply, dict) else "")})
        return None
    body = extract_proof(re.sub(r"\blemma\s+sb_goal\b", "theorem sb_goal", reply), "sb_goal")
    if not body:
        log.append({"depth": depth, "stopped": "no proof in the answer"})
        return None
    head = lemma_prefix(prefix, statement)
    cand = head + body
    r = judge_text(cand)
    if r["verdict"] == "accept":
        log.append({"depth": depth, "outcome": "proved"})
        return body
    rep = subgoals.repair(cand, head, r.get("output") or "", ask=None, run_lean=run_lean, judge_text=judge_text,
                          tactics=TACTICS, fix=fix)
    if rep.get("accepted"):
        log.append({"depth": depth, "outcome": "proved by Lean's automation on its steps"})
        return body_of(rep["accepted"], head)
    sketch, goals = rep.get("sketch"), rep.get("goals") or []
    top = head.count("\n") + 1
    open_holes = subgoals.holes(sketch, top) if sketch else None
    entry = {"depth": depth, "steps_left": len(goals), "stopped": rep.get("stopped")}
    log.append(entry)
    if not goals or not open_holes or len(open_holes) != len(goals) or len(goals) > subgoals.MAX_HOLES:
        if _last is None:                                 # nothing to recurse on: one more ask, with Lean's error
            return decompose(statement, prefix, ask=ask, run_lean=run_lean, judge_text=judge_text, depth=depth,
                             budget=budget, log=log, fix=fix, _last=(body, r.get("output") or ""))
        return None
    if depth <= 0:
        return None
    plan = {}
    for hole, goal in zip(open_holes, goals):
        sub = decompose(goal, prefix, ask=ask, run_lean=run_lean, judge_text=judge_text, depth=depth - 1,
                        budget=budget, log=log, fix=fix)
        if sub is None:
            return None                                   # one step unproved leaves the proof open
        lines = sub.rstrip("\n").split("\n")
        base = min(subgoals.indent(l) for l in lines if l.strip())
        plan[hole] = [l[base:] if l.strip() else "" for l in lines]
    final = subgoals._with_tactics(sketch, plan)
    r = judge_text(final)
    entry["spliced"] = r["verdict"]
    return body_of(final, head) if r["verdict"] == "accept" else None


def leanstral_ask(key):
    """ask(prompt) -> text or None, paced and stopping at the first 402/429 like tools/leanstral.py."""
    import leanstral
    pacer = leanstral.Pacer(leanstral.MIN_GAP_S)

    def ask(prompt):
        try:
            return leanstral.call_prompt(key, prompt, pacer)["text"]
        except Exception as e:                        # the reason goes into the goal's row, not away
            return {"error": f"{type(e).__name__}: {str(e)[:160]}"}
    return ask, pacer


def run(goals, read_target, ask, run_lean, judge_text, jobs=WORKERS, fix=None):
    """Each goal decomposed, then its proof spliced into its problem (goal_closer.close). Returns (rows, solves):
    rows are measurements; solves are [(goal, body)] the kernel accepted whole."""
    def one(g):
        t0, budget, log = time.monotonic(), {"asks": 0}, []
        target_text = read_target(g["target_set"], g["target"])
        body = decompose(g["goal"], goal_closer.prefix_of(target_text), ask=ask, run_lean=run_lean,
                         judge_text=judge_text, budget=budget, log=log, fix=fix)
        r = goal_closer.close(g, target_text, body, judge_text) if body else None
        row = {"at": datetime.now(timezone.utc).isoformat(timespec="seconds"), "sha": g["sha"],
               "target_set": g["target_set"], "target": g["target"], "kind": goal_closer.kind(g["goal"]),
               "restates": g.get("restates"), "asks": budget["asks"], "levels": log,
               "outcome": "solved" if r and r["verdict"] == "accept" else ("goal proved, splice failed" if r else "failed"),
               "seconds": round(time.monotonic() - t0, 1)}
        return row, ((g, body) if r and r["verdict"] == "accept" else None)

    with ThreadPoolExecutor(jobs) as pool:
        out = list(pool.map(one, goals))
    return [r for r, _ in out], [s for _, s in out if s]


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("cmd", choices=["run"])
    ap.add_argument("--max-goals", type=int, default=40)
    ap.add_argument("--out", required=True)
    a = ap.parse_args()
    key = os.environ.get("SPAREBRAINS_LEANSTRAL_KEY", "").strip()
    if not key:
        sys.exit("SPAREBRAINS_LEANSTRAL_KEY is not set")
    import lean_tools, prover, relay
    targets = relay.fetch_json("/targets.json")
    rung = {(t["target_set"], t["target"]): t.get("rung") for t in targets["open"]}
    tried = set()
    for f in (ROOT / "ledger" / "decompose").glob("*.jsonl"):
        tried |= {json.loads(l)["sha"] for l in f.read_text().splitlines() if l.strip()}
    goals = [g for g in json.loads(goal_closer.QUEUE.read_text())
             if g.get("file_ok") and (g["target_set"], g["target"]) in rung
             and rung[(g["target_set"], g["target"])] not in goal_closer.BAR_RUNGS and g["sha"] not in tried]
    goals = goals[:a.max_goals]                           # the queue's order: real steps first
    read = lambda s, t: (ROOT / "targets" / s / f"{t}.lean").read_text()
    ask, pacer = leanstral_ask(key)
    import fixer
    names_ix = lean_tools.index()
    rows, solves = run(goals, read, ask, lean_tools.run_lean, lean_tools.judge_text,
                       fix=lambda proof, out: fixer.fix(proof, out, *names_ix))
    Path(a.out).parent.mkdir(parents=True, exist_ok=True)
    with open(a.out, "a") as f:
        f.writelines(json.dumps(r, ensure_ascii=False) + "\n" for r in rows)
    published = {}
    if solves:
        from utilities.kumori_api_client import init, sparebrains_attempt
        post = None
        try:
            init()
            post = sparebrains_attempt
        except Exception as e:
            print(f"site recording off ({type(e).__name__}); the ledger still gets every row", flush=True)
        run_id = "decompose-" + datetime.now(timezone.utc).strftime("%Y%m%dT%H%M")
        answers = [{"batch": run_id, "target_set": g["target_set"], "target": g["target"], "sample": i, "goal": g["sha"],
                    "text": "```lean4\n" + g["goal"] + "\n" + body + "```"} for i, (g, body) in enumerate(solves)]
        published = prover.judge_goals(answers, prover.prover_rows(lane=LANE), {g["sha"]: g for g, _ in solves},
                                       judge_text=lean_tools.judge_text,
                                       record=prover.Recorder("run", post, LANE), run_id=run_id, lane=LANE)
    asks = sum(r["asks"] for r in rows)
    print(f"decompose: {len(rows)} goals, {asks} Leanstral asks, {len(solves)} problems solved "
          f"{sorted(g['target'] for g, _ in solves)}; published {published}"
          + (f"; Leanstral stopped: {pacer.stop}" if pacer.stop else ""))
    return 0


if __name__ == "__main__":
    sys.exit(main())
