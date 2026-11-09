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

    python3 tools/decompose.py run --max-goals 40 --out ledger/decompose/run-ID.jsonl   # needs the Mistral key (leanstral.KEY_ENV)
"""
import argparse, json, re, sys, threading, time
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT), str(ROOT / "tools")]
import ledger_files
import goal_closer, subgoals
from ladder import RUNGS
from proof_text import extract_proof

DEPTH = 2              # a goal's steps, and their steps: deeper did not pay in Hilbert's ablation past a few levels
MAX_ASKS = 8           # model calls per top goal, across every level
WORKERS = 3            # goals at once; a Leanstral ask took 236 s median, 2,031 s p99 (ledger/decompose to 2026-11-09)
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
    if budget.get("deadline") is not None and time.monotonic() > budget["deadline"]:
        log.append({"depth": depth, "stopped": "run deadline"})
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

    def ask(prompt, effort=None):
        try:
            return leanstral.reply(leanstral.call_prompt(key, prompt, pacer, effort))
        except Exception as e:                        # the reason goes into the goal's row, not away
            return {"error": f"{type(e).__name__}: {str(e)[:160]}"}
    return ask, pacer


def lane_of(backend):
    """The lane a run records under: Leanstral's by default, else any router lane (charter: every tool, any lane)."""
    if not backend:
        return LANE
    return {"backend": f"{backend}-decompose", "provider": "kumori-router", "model": backend, "mode": "goal-closer",
            "file": "decompose"}


def pick_goals(queue, rung, tried, reachable, bar, n, first=()):
    """The goals to try: readable, untried by this lane, outside the bar's rungs unless `bar` (once the plan arm is
    judged, as for the Leanstral lane and the 32B), goals on problems a published prover reached as stated first
    (tools/reachable.py), else the queue's order (real steps first). `first`: goals this lane solved whose problem is
    still open, so the solve was lost; they go ahead of everything (#642: run 42124394793 left 4 of them past its 25)."""
    ok = [g for g in queue if g.get("file_ok") and (g["target_set"], g["target"]) in rung and g["sha"] not in tried
          and (bar or rung[(g["target_set"], g["target"])] not in goal_closer.BAR_RUNGS)]
    # a goal that restates its whole theorem goes last (2026-10-22: 20 of 20 failed in runs 39513404578 and
    # 39541439510, 25% and 34% of their goals, pulled forward because their problems are reachable)
    return sorted(ok, key=lambda g: (g["sha"] not in first, bool(g.get("restates")),
                                     (g["target_set"], g["target"]) not in reachable))[:n]


def cut_at_cap(rows, backend):
    """Goals whose asks on this lane ran out at the token cap twice or more: asked with reasoning_effort 'none' next,
    the prover lane's rule (leanstral.effort_for). 2026-10-22: 'empty reply (finish=length, 120000 tokens)' was the
    most common stop in decompose runs 39513404578 (24 levels) and 39541439510 (18), and such a goal counts as
    untried, so it was asked the same way again every run."""
    import leanstral
    at_cap = f"finish=length, {leanstral.MAX_TOKENS} tokens"         # today's cap only, as effort_for counts
    # a stream that ended with no finish (cut near an hour) or at leanstral.CALL_DEADLINE_S ran out the same way (#642)
    stalled = ("finish=None", "finish=deadline")
    n = Counter()
    for r in rows:
        if r.get("backend", LANE["backend"]) == backend and not r.get("effort"):
            n[r["sha"]] += sum(at_cap in str(e.get("stopped", "")) or any(x in str(e.get("stopped", "")) for x in stalled)
                           for e in r.get("levels") or [])
    return {sha for sha, k in n.items() if k >= 2}


def tried_by(rows, backend):
    """Goals this lane already tried; rows from before 2026-10-19's router lanes carry no backend and are Leanstral's.
    A goal whose every ask came back with no answer was not tried (2026-10-20: 45 of Leanstral's 83, mostly the
    40,000-token cap)."""
    blank = lambda r: r.get("levels") and all(str(e.get("stopped", "")).startswith("no answer") for e in r["levels"])
    # a goal cut by the run deadline, at any depth, was not tried either: it is asked whole next run (#642, Codex f2)
    # and a call cut at leanstral.CALL_DEADLINE_S at any depth (Codex 20261109T025317855518Z f4: after a parent answer)
    cut = lambda r: r.get("run_deadline") or any(e.get("stopped") == "run deadline" or "finish=deadline" in str(e.get("stopped", ""))
                                                 for e in r.get("levels") or [])
    # a solved goal is not 'tried': its problem, if still open, lost the proof (2026-11-05, run 42061251877), so ask again
    mine = [r for r in rows if r.get("backend", LANE["backend"]) == backend]
    return {r["sha"] for r in mine if not blank(r) and not cut(r)} - solved_by(rows, backend)   # a solve wins over any failed row


def solved_by(rows, backend):
    return {r["sha"] for r in rows if r.get("backend", LANE["backend"]) == backend and r.get("outcome") == "solved"}


def pick_lane(live, rows, now_iso):
    """`--lane auto`: the strongest live lane by hard solves (relay.strongest), leaving out any lane the relay has
    benched or that is failing now, so a lane name is never guessed from the ledger (2026-10-19: two guesses failed,
    one at Groq's token limit, one retired from the router)."""
    import relay
    ok = [l for l in live if not relay.relay_benched(rows, l["backend"], now_iso)
          and not relay.relay_failing(rows, l["backend"], now_iso)]
    top = relay.strongest(ok, relay.lane_strength(rows, RUNGS), 1)
    return top[0] if top else None


def router_ask(backend, chat=None, max_tokens=16000):
    """ask(prompt) -> text, or {"error": why}, through Kumori's router like attempt.py's lemma asks: the router paces
    each lane, so a short retry_after is waited out (twice at most), anything else ends the ask with its reason."""
    if chat is None:
        from utilities.kumori_api_client import init, llm_chat
        init()
        chat = llm_chat

    class NoPacer:
        stop = None

    def ask(prompt):
        for tries in (1, 2, 3):
            try:
                reply, _, _ = chat(backend, [{"role": "user", "content": prompt}], max_tokens=max_tokens, temperature=0.2,
                                   app_name="sparebrains", include_metadata=True, timeout=(10, 315), timeout_s=300,
                                   long_call=True)
                return reply
            except Exception as e:
                wait = getattr(e, "retry_after", 0) or 0
                if tries < 3 and 0 < wait <= 60:
                    time.sleep(wait + 0.5)
                    continue
                return {"error": f"{type(e).__name__}: {str(e)[:160]}"}
    return ask, NoPacer()


def run(goals, read_target, ask, run_lean, judge_text, jobs=WORKERS, fix=None, on_row=None, effort_of=None, deadline=None,
        hard=None):
    """Each goal decomposed, then its proof spliced into its problem (goal_closer.close). Returns (rows, solves):
    rows are measurements; solves are [(goal, body)] the kernel accepted whole. `on_row` gets each row as its goal
    finishes, so a run stopped by its time limit keeps every goal it finished (2026-10-21). `deadline` (monotonic
    seconds): past it no goal starts and no ask is made. `hard`: every Lean call's timeout is clamped to it and past it
    a call is refused, so each goal ends and writes its row before the step's timeout kills it (#642, Codex f3). A goal
    either one cut is marked run_deadline and stays untried."""
    if hard is not None:
        lean_fn, judge_fn = run_lean, judge_text
        left = lambda: hard - time.monotonic()

        def run_lean(text, timeout=180):
            if left() <= 1:
                return "run deadline: Lean not started", 0.0
            return lean_fn(text, timeout=min(timeout, left()))

        def judge_text(text, timeout=300):
            if left() <= 1:
                return {"verdict": "timeout", "reason": "run deadline: Lean not started", "seconds": 0.0, "output": ""}
            return judge_fn(text, timeout=min(timeout, left()))

    def one(g):
        if deadline is not None and time.monotonic() > deadline:
            return None
        t0, budget, log = time.monotonic(), {"asks": 0, "deadline": deadline}, []
        effort = effort_of(g) if effort_of else None
        target_text = read_target(g["target_set"], g["target"])
        body = decompose(g["goal"], goal_closer.prefix_of(target_text),
                         ask=(lambda p: ask(p, effort=effort)) if effort else ask, run_lean=run_lean,
                         judge_text=judge_text, budget=budget, log=log, fix=fix)
        r = goal_closer.close(g, target_text, body, judge_text) if body else None
        row = {"at": datetime.now(timezone.utc).isoformat(timespec="seconds"), "sha": g["sha"],
               "target_set": g["target_set"], "target": g["target"], "kind": goal_closer.kind(g["goal"]),
               "restates": g.get("restates"), "asks": budget["asks"], "levels": log, "effort": effort,
               "outcome": "solved" if r and r["verdict"] == "accept" else
                          ("goal proved, splice failed" if r and r.get("stage") != "goal" else "failed"),
               "seconds": round(time.monotonic() - t0, 1)}
        if row["outcome"] != "solved" and (any(e.get("stopped") == "run deadline" for e in log)
                                           or (hard is not None and time.monotonic() >= hard - 1)):
            row["run_deadline"] = True                  # cut, not tried: asked again next run (tried_by)
        if r:
            row["stage"] = r.get("stage")
        if r and r.get("stage") != "goal":
            # the goal is proved: keep its proof. A solve is published from these rows (publish_rows), so a job killed
            # at its cap loses none (2026-11-05: two solves lost in run 42061251877); an unspliced goal waits for a
            # later splice (imo_1974_p3's, proved 10-21, was lost)
            row.update(body=body, goal=g["goal"], sketches=g.get("sketches", []))   # the row alone can publish it
            if r["verdict"] != "accept":
                row["splice_output"] = (r.get("output") or "")[-600:]
        if on_row:
            on_row(row)
        return row, ((g, body) if r and r["verdict"] == "accept" else None)

    with ThreadPoolExecutor(jobs) as pool:
        out = [o for o in pool.map(one, goals) if o]
    return [r for r, _ in out], [s for _, s in out if s]


def publish_rows(rows, goals_by_sha, *, judge_goals, prover_rows, judge_text, record, lane, run_id=None):
    """Every solved row that kept its body, judged again and published through the goal batches' own path
    (prover.judge_goals: splice, the kernel, the ledger row, verified/, the site). The one way solves are published."""
    # the goal from the queue, else from the row itself (a refreshed queue lives only in its job's temp dir)
    goal_of = lambda r: goals_by_sha.get(r["sha"]) or ({k: r[k] for k in ("sha", "target_set", "target", "goal", "sketches")}
                                                       if r.get("goal") and r.get("sketches") is not None else None)
    solves = [(goal_of(r), r["body"]) for r in rows if r.get("outcome") == "solved" and r.get("body") and goal_of(r)]
    if not solves:
        return {}
    run_id = run_id or "decompose-" + datetime.now(timezone.utc).strftime("%Y%m%dT%H%M")
    answers = [{"batch": run_id, "target_set": g["target_set"], "target": g["target"], "sample": i, "goal": g["sha"],
                "text": "```lean4\n" + g["goal"] + "\n" + body + "```"} for i, (g, body) in enumerate(solves)]
    return judge_goals(answers, prover_rows, {g["sha"]: g for g, _ in solves}, judge_text=judge_text, record=record,
                       run_id=run_id, lane=lane)


def lane_from_rows(rows, given=None):
    """The lane the rows were written under: each row carries its backend (keep()), so `--lane auto` is never guessed."""
    backends = {r.get("backend") for r in rows if r.get("backend")}
    if len(backends) == 1:
        b = backends.pop()
        return LANE if b == LANE["backend"] else lane_of(b.removesuffix("-decompose"))
    return lane_of(None if given in (None, "", "auto") else given)


def publish_main(a):
    """`publish`: the solves in a run's rows file, after the run step (a timeout included)."""
    import lean_tools, prover
    out = Path(a.out)
    rows = [json.loads(l) for l in out.read_text().splitlines() if l.strip()] if out.exists() else []
    lane = lane_from_rows(rows, a.lane)
    qfile = Path(a.queue) if a.queue and Path(a.queue).exists() else goal_closer.QUEUE
    goals = {g["sha"]: g for g in json.loads(qfile.read_text())}
    from utilities.kumori_api_client import init, sparebrains_attempt
    post = None
    try:
        init()
        post = sparebrains_attempt
    except Exception as e:
        print(f"site recording off ({type(e).__name__}); the ledger still gets every row", flush=True)
    published = publish_rows(rows, goals, judge_goals=prover.judge_goals, prover_rows=prover.prover_rows(lane=lane),
                             judge_text=lean_tools.judge_text, record=prover.Recorder("run", post, lane), lane=lane)
    solved = sorted({r["target"] for r in rows if r.get("outcome") == "solved"})
    print(f"decompose publish: {len(rows)} rows, solved {solved}; published {published}", flush=True)
    return 0


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("cmd", choices=["run", "publish"])
    ap.add_argument("--max-goals", type=int, default=40)
    ap.add_argument("--stop-after", type=int, help="seconds from start: past it no goal starts and no ask is made (#642)")
    ap.add_argument("--hard-stop", type=int, help="seconds from start: Lean calls are clamped to it and refused past it (#642)")
    ap.add_argument("--lane", help="a router lane (a backend name) to ask instead of Leanstral, or `auto` for the "
                    "strongest live one")
    ap.add_argument("--out", required=True)
    ap.add_argument("--queue", help="a goal queue to read instead of ledger/goal-queue.json (goal_closer.py refresh --out)")
    a = ap.parse_args()
    if a.cmd == "publish":
        return publish_main(a)
    max_tokens = 16000
    if a.lane == "auto":
        import attempt
        from utilities.kumori_api_client import init
        init()
        known, unknown = attempt.lanes(None, skip_benched=True)
        rows = [json.loads(l) for f in ledger_files.try_files(ROOT / "ledger") for l in f.read_text().splitlines() if l.strip()]
        picked = pick_lane(known + unknown, rows, datetime.now(timezone.utc).isoformat())
        if not picked:
            sys.exit("auto: no live lane has a solve above MATH level 2 in the ledger")
        a.lane, max_tokens = picked["backend"], attempt.lane_max_tokens(picked, 4000)
        print(f"auto: {a.lane}, {max_tokens} tokens", flush=True)
    lane = lane_of(a.lane)
    import leanstral
    key = None if a.lane else leanstral.key_from_env()
    import lean_tools, prover, relay
    targets = relay.fetch_json("/targets.json")
    rung = {(t["target_set"], t["target"]): t.get("rung") for t in targets["open"]}
    past = [json.loads(l) for f in (ROOT / "ledger" / "decompose").glob("*.jsonl") for l in f.read_text().splitlines()
            if l.strip()]
    tried = tried_by(past, lane["backend"])
    reach = ({(r["target_set"], r["target"]) for r in json.loads(prover.REACHABLE.read_text())["reachable"]}
             if prover.REACHABLE.exists() else set())
    qfile = Path(a.queue) if a.queue and Path(a.queue).exists() else goal_closer.QUEUE
    print(f"queue: {qfile}", flush=True)
    goals = pick_goals(json.loads(qfile.read_text()), rung, tried, reach, prover.plan_owed(open_keys=set(rung)) is None,
                       a.max_goals, first=solved_by(past, lane["backend"]))
    read = lambda s, t: (ROOT / "targets" / s / f"{t}.lean").read_text()
    ask, pacer = router_ask(a.lane, max_tokens=max_tokens) if a.lane else leanstral_ask(key)
    import fixer
    names_ix = lean_tools.index()
    Path(a.out).parent.mkdir(parents=True, exist_ok=True)
    lock = threading.Lock()

    def keep(r):                                        # one line per finished goal, flushed at once
        with lock, open(a.out, "a") as f:
            f.write(json.dumps({**r, "backend": lane["backend"]}, ensure_ascii=False) + "\n")
    cut = set() if a.lane else cut_at_cap(past, lane["backend"])     # router lanes take no effort setting here
    print(f"{len(cut & {g['sha'] for g in goals})} of {len(goals)} goals asked with reasoning_effort none "
          f"(cut at the token cap twice before)", flush=True)
    rows, solves = run(goals, read, ask, lean_tools.run_lean, lean_tools.judge_text,
                       fix=lambda proof, out: fixer.fix(proof, out, *names_ix), on_row=keep,
                       effort_of=lambda g: "none" if g["sha"] in cut else None,
                       deadline=time.monotonic() + a.stop_after if a.stop_after else None,
                       hard=time.monotonic() + a.hard_stop if a.hard_stop else None)
    # solves are published by `publish`, the workflow's next step, from the rows file: a run cut at its cap keeps them
    asks = sum(r["asks"] for r in rows)
    print(f"decompose: {len(rows)} goals, {asks} {a.lane or 'Leanstral'} asks, {len(solves)} problems solved "
          f"{sorted(g['target'] for g, _ in solves)} (published by the publish step)"
          + (f"; Leanstral stopped: {pacer.stop}" if pacer.stop else ""))
    return 0


if __name__ == "__main__":
    sys.exit(main())
