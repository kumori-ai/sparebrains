"""The worst-lane replay (2026-10-24, non-negotiable 6; DECISIONS.md): one lane's frozen answers re-run with zero model
calls, to measure what tools give the weakest free model. Each stored raw reply goes through extraction with Lean 3
recovery off (today) and on (proof_text.recover_lean3), then the loop's Lean-only chain (toolscore.run_chain);
tools alone (subgoals.whole_goal) runs once per problem on the bare statement, the denominator for every claim.

    python3 tools/replay.py --slice 0/6 --max-minutes 300      # in CI's judge sandbox only: the replies are untrusted
    python3 tools/replay.py --report                           # the report half's table, no Lean

Held out by problem (toolscore.problem_half): recovery is built on the tune half; the report half is the evidence,
less the attempts read during diagnosis (EXPOSED). Results go to ledger/replay/, fenced from every try reader.
"""
import argparse, gzip, json, os, sys, time
from collections import defaultdict
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT), str(ROOT / "tools")]
from proof_text import PROOF_SEP, extract_proof, recover_lean3
from toolscore import file_hash, problem_hash, problem_half, statement_sha, wilson95

REPLAY = ROOT / "ledger" / "replay"
COHORT = REPLAY / "groq-allam-ladder-x3-2026-10-24.jsonl.gz"
EXPOSED = {15335, 15336, 15354}      # read in full during diagnosis: their problems never enter the reported numbers
ARMS = ("off", "on")


def load_cohort(path=COHORT):
    with gzip.open(path, "rt") as fh:
        return [json.loads(l) for l in fh if l.strip()]


def eligible(cohort, sha=statement_sha):
    """(rows to replay, {reason: [attempt ids]}): an exposed attempt or one whose statement changed since it was
    answered is left out and named, never judged against a different theorem."""
    keep, dropped = [], {"exposed": [], "statement_changed": []}
    for r in cohort:
        if r["id"] in EXPOSED:
            dropped["exposed"].append(r["id"])
        elif r.get("statement_sha") != sha(r["target_set"], r["target"]):
            dropped["statement_changed"].append(r["id"])
        else:
            keep.append(r)
    return keep, dropped


def replay_one(row, prefix, arm, judge, chain):
    """One stored reply in one arm: extract (recovery only in arm `on`), judge it as extracted, and only a reject goes
    on to the chain, so an answer that was already right stays right (Codex 20261024T161801868685Z: run_chain
    discards a first accept)."""
    resp, name = row.get("response") or "", row["target"]
    proof, transforms = extract_proof(resp, name), []
    if proof is None and arm == "on":
        got = recover_lean3(resp, name)
        if got:
            proof, transforms = got
    if proof is None:
        return {"verdict": "reject", "reason": "no proof extracted from reply", "transforms": transforms}
    j = judge(prefix + "\n" + proof)
    if j["verdict"] == "accept":
        return {"verdict": "accept", "stage": "as_extracted", "transforms": transforms}
    c = chain(proof, prefix, j.get("output") or "")
    return {"verdict": c["c_verdict"], "stage": "chain", "transforms": transforms, "fixes": c.get("fixes") or [],
            "stopped": (c.get("rep") or {}).get("stopped")}


def owns_baseline(tset, target, k, n):
    """The one slice that runs tools alone for a problem, by its hash, so six slices never run it six times."""
    return int(problem_hash(tset, target)[:8], 16) % n == k


def report(rows, cohort, tools_hash=None, lean_env=None):
    """The report half, per problem: solved = any accept over its attempts. Counted only from results of this code
    (tools_hash, lean_env) for attempts in `cohort` (the eligible ones, plus any EXPOSED attempt so its problem is
    taken out), and only for complete problems: every attempt in both arms and tools alone done. Every other report
    problem is pending, named and never counted as a failure (Codex 20261024T170221251251Z). Per arm and per rung,
    problem-level Wilson intervals; model_assisted_only = on and not tools alone, tools_alone_only the reverse."""
    exposed = {(r["target_set"], r["target"]) for r in cohort if r["id"] in EXPOSED}
    attempts = defaultdict(set)
    rung = {}
    for r in cohort:
        key = (r["target_set"], r["target"])
        if problem_half(*key) == "report" and r["id"] not in EXPOSED and key not in exposed:
            attempts[key].add(r["id"])
            rung[key] = r.get("rung")
    current = [r for r in rows if (tools_hash is None or r.get("tools_hash") == tools_hash)
               and (lean_env is None or r.get("lean_env") == lean_env)]
    seen, hit = defaultdict(set), defaultdict(set)
    for r in current:
        key = (r["target_set"], r["target"])
        if key not in attempts:
            continue
        if r["arm"] == "tools_alone":
            seen[key].add("tools_alone")
        elif r.get("attempt_id") in attempts[key]:
            seen[key].add((r["attempt_id"], r["arm"]))
        else:
            continue
        if r.get("verdict") == "accept":
            hit[r["arm"]].add(key)
    for r in cohort:
        if r.get("verdict") == "accept":
            hit["recorded"].add((r["target_set"], r["target"]))
    complete = {k for k, ids in attempts.items()
                if "tools_alone" in seen[k] and all((i, a) in seen[k] for i in ids for a in ARMS)}
    arms = ("recorded",) + ARMS + ("tools_alone",)
    out = {"problems": len(complete), "pending": len(attempts) - len(complete), "exposed_problems": len(exposed),
           "complete": complete}
    for arm in arms:
        k = len(hit[arm] & complete)
        out[arm] = {"solved": k, "wilson95": wilson95(k, len(complete))}
    on, tools = hit["on"] & complete, hit["tools_alone"] & complete
    out["model_assisted_only"], out["tools_alone_only"] = len(on - tools), len(tools - on)
    by = defaultdict(set)
    for k in complete:
        by[rung[k]].add(k)
    out["by_rung"] = {}
    for g, keys in sorted(by.items(), key=lambda kv: str(kv[0])):
        out["by_rung"][g] = {"problems": len(keys),
                             **{arm: {"solved": len(hit[arm] & keys), "wilson95": wilson95(len(hit[arm] & keys), len(keys))}
                                for arm in arms}}
    return out


def render(r):
    def f(a, n=None, src=None):
        src = src or r
        n = r["problems"] if n is None else n
        w = src[a]["wilson95"]
        return f"{src[a]['solved']}/{n}" + (f" ({w[0]:.2f}-{w[1]:.2f})" if w else "")
    lines = [f"report half: {r['problems']} complete problems; {r['pending']} pending (not yet replayed in every arm, "
             f"not counted); {r['exposed_problems']} exposed (read during diagnosis, left out)",
             f"  recorded (as stored): {f('recorded')}", f"  recovery off + chain: {f('off')}",
             f"  recovery on + chain: {f('on')}", f"  tools alone: {f('tools_alone')}",
             f"  model-assisted only (on, not tools alone): {r['model_assisted_only']}; "
             f"tools alone only: {r['tools_alone_only']}",
             "| rung | problems | recorded | off | on | tools alone |", "|---|---|---|---|---|---|"]
    for g, v in r["by_rung"].items():
        lines.append(f"| {g} | {v['problems']} | " + " | ".join(f(a, v["problems"], v) for a in
                                                               ("recorded",) + ARMS + ("tools_alone",)) + " |")
    return "\n".join(lines)


def versions():
    """(tools_hash, lean_env) of this checkout: a result counts only against the code and Lean that produced it."""
    import toolscore
    return file_hash([ROOT / "tools" / f for f in toolscore.FILES + ("replay.py", "toolscore.py")]), file_hash(toolscore.LEAN_ENV)


def load_results():
    return [json.loads(l) for f in sorted(REPLAY.glob("results-*.jsonl")) for l in f.read_text().splitlines() if l.strip()]


def run_baseline(args):
    """BASELINE_RECIPES on every target in targets/{minif2f/test,primer,mil}, one slice, rows to ledger/replay as arm
    tools_alone with the recipe list on each row. A target already done by this code and Lean is skipped, so a run cut
    by --max-minutes is finished by the next."""
    import lean_tools
    tools_hash, lean_env = versions()
    k, n = (int(x) for x in args.slice.split("/"))
    run_id = BASELINE_V2_ID
    out = REPLAY / f"results-{run_id}-{os.environ.get('GITHUB_RUN_ID', 'local')}-{k}.jsonl"
    # done = decided under this id, code and Lean; an incomplete target is asked again on every dispatch (retry
    # policy), and no_model_set reads each target's latest row (Codex f2)
    done = {(r["target_set"], r["target"]) for r in load_results() if r.get("arm") == "tools_alone"
            and r.get("run_id") == run_id and r.get("verdict") in ("accept", "reject")
            and r.get("tools_hash") == tools_hash and r.get("lean_env") == lean_env}
    files = sorted(f for d in ("minif2f/test", "primer", "mil") for f in (ROOT / "targets" / d).glob("*.lean"))
    prior = {(r["target_set"], r["target"]): r.get("closer") for r in load_results()
             if r.get("arm") == "tools_alone" and r.get("run_id") == BASELINE_RUN and r.get("closer")}
    mine = [f for i, f in enumerate(files) if i % n == k]
    deadline = time.time() + 60 * args.max_minutes if args.max_minutes else None
    counts = defaultdict(int)
    print(f"baseline: {len(files)} targets, {len(mine)} in slice {args.slice}, {len(BASELINE_RECIPES)} recipes; "
          f"tools {tools_hash}, lean {lean_env}", flush=True)
    for f in mine:
        tset, target = str(f.parent.relative_to(ROOT / "targets")), f.stem
        if (tset, target) in done:
            continue
        if deadline and time.time() > deadline:
            print("baseline: out of time; the next run finishes the slice", flush=True)
            break
        t0 = time.time()
        res = baseline_one(f.read_text(), lean_tools.run_lean, lean_tools.judge_text, first=prior.get((tset, target)))
        counts[res["verdict"]] += 1
        with out.open("a") as fh:
            fh.write(json.dumps({"ts": datetime.now(timezone.utc).isoformat(timespec="seconds"), "run_id": run_id,
                                 "tools_hash": tools_hash, "lean_env": lean_env, "attempt_id": None, "arm": "tools_alone",
                                 "baseline": 2, "tactics": BASELINE_RECIPES, "target_set": tset, "target": target,
                                 "seconds": round(time.time() - t0, 1), **res}) + "\n")
        print(f"[baseline] {tset}/{target}: {res['verdict']} {res.get('closer') or ''}", flush=True)
    print(f"baseline: {dict(counts)}", flush=True)
    return 0


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--slice", default="0/1")
    ap.add_argument("--max-minutes", type=float, default=0)
    ap.add_argument("--report", action="store_true")
    ap.add_argument("--baseline", action="store_true", help="the extended no-model baseline over every target (#574)")
    args = ap.parse_args()
    if args.baseline:
        return run_baseline(args)
    cohort = load_cohort()
    keep, dropped = eligible(cohort)
    if args.report:
        print(f"cohort {len(cohort)} attempts; left out: " + ", ".join(f"{k} {len(v)}" for k, v in dropped.items()))
        print(render(report(load_results(), keep + [r for r in cohort if r["id"] in EXPOSED], *versions())))
        return 0
    import lean_tools, subgoals, toolscore
    names_ix = lean_tools.index()
    chain = lambda proof, prefix, said: toolscore.run_chain(proof, prefix, said, names_ix, lean_tools)
    tools_hash, lean_env = versions()
    k, n = (int(x) for x in args.slice.split("/"))
    run_id = os.environ.get("GITHUB_RUN_ID") or datetime.now(timezone.utc).strftime("local-%Y%m%dT%H%M%S")
    out = REPLAY / f"results-{run_id}-{os.environ.get('GITHUB_RUN_ATTEMPT', '1')}-{k}.jsonl"
    done = {(r.get("attempt_id"), r["arm"], r.get("target_set"), r.get("target")) for r in load_results()
            if r.get("tools_hash") == tools_hash and r.get("lean_env") == lean_env}
    deadline = time.time() + 60 * args.max_minutes if args.max_minutes else None
    accepts, written = 0, 0

    def write(row):
        nonlocal written
        with out.open("a") as fh:
            fh.write(json.dumps({"ts": datetime.now(timezone.utc).isoformat(timespec="seconds"), "run_id": run_id,
                                 "tools_hash": tools_hash, "lean_env": lean_env, **row}) + "\n")
        written += 1

    def prefix_of(r):
        text = (ROOT / "targets" / r["target_set"] / f"{r['target']}.lean").read_text()
        return text[:PROOF_SEP.search(text).end()]
    mine = [r for r in keep if r["id"] % n == k]
    print(f"replay: {len(cohort)} attempts, {len(keep)} eligible, {len(mine)} in slice {args.slice}; "
          f"tools {tools_hash}, lean {lean_env}", flush=True)
    for r in mine:
        if deadline and time.time() > deadline:
            break
        base = {"attempt_id": r["id"], "target_set": r["target_set"], "target": r["target"], "rung": r.get("rung"),
                "half": problem_half(r["target_set"], r["target"]), "recorded": r.get("verdict")}
        prev = None
        for arm in ARMS:
            if (r["id"], arm, r["target_set"], r["target"]) in done:
                continue
            if arm == "on" and prev is not None and extract_proof(r.get("response") or "", r["target"]) is not None:
                res = {**prev, "same_as": "off"}           # recovery only acts where extraction failed
            else:
                res = replay_one(r, prefix_of(r), arm, lean_tools.judge_text, chain)
            prev = res
            accepts += arm == "on" and res["verdict"] == "accept"
            write({**base, "arm": arm, **res})
            print(f"[replay] {r['id']} {r['target_set']}/{r['target']} {arm}: {res['verdict']} "
                  f"{','.join(res.get('transforms') or [])}", flush=True)
    seen = set()
    for r in sorted(keep, key=lambda r: r["id"]):            # tools alone: once per problem, in its one owner slice
        key = (r["target_set"], r["target"])
        if key in seen or not owns_baseline(*key, k, n) or (None, "tools_alone", *key) in done \
                or (deadline and time.time() > deadline):
            seen.add(key)
            continue
        seen.add(key)
        closer = subgoals.whole_goal(prefix_of(r), lean_tools.judge_text)
        write({"attempt_id": None, "target_set": key[0], "target": key[1], "rung": r.get("rung"),
               "half": problem_half(*key), "arm": "tools_alone", "verdict": "accept" if closer else "reject",
               "closer": closer})
    print(f"replay: {written} rows to {out.relative_to(ROOT)}", flush=True)
    if os.environ.get("GITHUB_OUTPUT"):
        with open(os.environ["GITHUB_OUTPUT"], "a") as fh:
            fh.write(f"calls=0\naccepts={accepts}\nmode=replay\nlanes=0\nremaining=0\n")
    return 0


# The no-model baseline's tactics by the tools hash its rows carry (the rows record no list). b6dddd8ade is run
# 40123591430, 2026-10-24: subgoals.AUTO_TACTICS at ec8e9d25, hashed and read by Codex 20261109T032109853848Z.
BASELINE_TACTICS = {"b6dddd8ade": ["omega", "linarith", "nlinarith", "positivity", "decide", "(norm_num; done)",
                                   "(simp; done)", "(aesop; done)", "grind", "exact?"]}
OFF_BASELINE_MEANS = ("not accepted by the recorded no-model baseline (replay tools_alone); not proof that automation "
                      "cannot prove it: a timeout reads as a reject there")


BASELINE_RUN = "40123591430"     # the baseline in force; a new one replaces it here, by a reviewed change, once complete
BASELINE_V2_ID = "baseline-2-2026-11-09"   # every dispatch of the extended baseline writes under this one id (Codex f2)


def no_model_set(ledger, run_id=None):
    """The targets Lean's automation alone proved in a replay's tools_alone arm, with that run's version. #574: every
    skeleton-pilot solve was in it. Refuses no rows (an empty set would make every off-set read pass) and a mix of
    versions unless `run_id` names one."""
    rows = [json.loads(l) for f in sorted((Path(ledger) / "replay").glob("results-*.jsonl"))
            for l in f.read_text().splitlines() if l.strip()]
    rows = [r for r in rows if r.get("arm") == "tools_alone"]
    if run_id is None and len({r.get("run_id") for r in rows}) > 1 and any(r.get("run_id") == BASELINE_RUN for r in rows):
        run_id = BASELINE_RUN                            # several recorded: the one in force
    rows = [r for r in rows if run_id is None or r.get("run_id") == run_id]
    latest = {}
    for r in sorted(rows, key=lambda r: r.get("ts") or ""):   # a retried target counts by its latest row
        latest[(r.get("target_set"), r.get("target"))] = r
    rows = list(latest.values())
    if not rows:
        raise ValueError("no tools_alone rows: no baseline recorded, so nothing can be read off it")
    versions = {(r.get("run_id"), r.get("lean_env"), r.get("tools_hash")) for r in rows}
    if len(versions) > 1:
        raise ValueError(f"{len(versions)} baseline versions recorded {sorted(map(str, versions))}; name one with run_id")
    (run, env, tools), = versions
    return {"set": {(r["target_set"], r["target"]) for r in rows if r.get("verdict") == "accept"},
            "targets": len({(r["target_set"], r["target"]) for r in rows}),
            "incomplete": sum(r.get("verdict") == "incomplete" for r in rows),
            "unknown": {(r["target_set"], r["target"]) for r in rows if r.get("verdict") == "incomplete"},
            "version": {"run_id": run, "lean_env": env, "tools_hash": tools, "date": min(r.get("ts") or "" for r in rows)[:10],
                        "tactics": rows[0].get("tactics") or BASELINE_TACTICS.get(tools)}}


# The extended baseline (#574, 2026-11-09): the first one's closers plus the entries of DuoTactic's fixed table
# (huggingface Duoia/duotactic, 32.8% of miniF2F test with no model) it lacked, and the plain forms of the skeletons.
# Each is written on one line, so `a; b` runs b after a, as in that table. No composition search in this version.
BASELINE_RECIPES = list(dict.fromkeys(__import__("subgoals").AUTO_TACTICS + [
    "rfl", "trivial", "norm_num", "simp", "aesop", "simp_all", "ring", "ring_nf", "field_simp; ring", "simp_all; ring",
    "simp_all; norm_num", "simp_all; omega", "simp_all; linarith", "simp_all; nlinarith", "gcongr", "bound",
    "simp; try aesop", "simp; try nlinarith", "norm_num; linarith", "norm_num; nlinarith"]))
BATCH_TIMEOUT_S = 300
# Search-heavy closers run in their own batch, after the rest found nothing: in one file with the others, a 2026-11-09
# canary (primer_lessorequal_06_le_antisymm) took 9 min of batches timing out and halving before omega's pass counted.
SLOW = {"exact?", "(aesop; done)", "aesop", "bound", "grind", "simp; try aesop"}


def baseline_one(target_text, run_lean, judge_text, recipes=None, first=None):
    """Every recipe on one target with no model: one Lean file holding the theorem once per recipe; a batch that times
    out is halved and run again, so one slow recipe cannot hide the rest; each pass is then judged alone as the
    target itself. accept (with the closer), reject, or incomplete when a recipe never finished in Lean."""
    import re, goal_closer, subgoals
    recipes = recipes or BASELINE_RECIPES
    pre = goal_closer.prefix_of(target_text)
    at = subgoals.DECL.search(pre).start()
    preamble, header = pre[:at], pre[at:]
    m = re.match(r"(?:theorem|lemma)\s+(\S+)", header)
    named = lambda nm: header[:m.start(1)] + nm + header[m.end(1):]

    def batch(ix):
        text, starts = preamble, []
        for i in ix:
            starts.append((f"sb_goal_r{i}", text.count("\n") + 1))
            text += named(f"sb_goal_r{i}") + "\n  " + recipes[i] + "\n\n"
        out, _ = run_lean(text, timeout=BATCH_TIMEOUT_S)
        if "timeout after" in out:
            if len(ix) == 1:
                return [], list(ix)
            h = len(ix) // 2
            (p1, t1), (p2, t2) = batch(ix[:h]), batch(ix[h:])
            return p1 + p2, t1 + t2
        return [ix[j] for j in goal_closer.recipes_passing(out, starts, text.count("\n") + 1)], []

    timed_out = []
    # `first`: a closer the last baseline found, judged alone before any batch (it is one of these recipes)
    tiers = ([[recipes.index(first)]] if first in recipes else []) + \
            [[i for i in range(len(recipes)) if (recipes[i] in SLOW) == slow] for slow in (False, True)]
    for ix in tiers:
        passing, t = batch(ix) if len(ix) > 1 else (ix, [])   # one recipe: the judge below is its run
        timed_out += t
        for i in sorted(passing):
            r = judge_text(pre + "\n  " + recipes[i])
            if r["verdict"] == "accept":
                return {"verdict": "accept", "closer": recipes[i]}
            if r["verdict"] == "timeout" or str(r.get("reason", "")).startswith("timeout after"):
                timed_out.append(i)           # check.judge reports a timeout as reject + "timeout after Ns" (Codex f1)
    return {"verdict": "incomplete" if timed_out else "reject", "closer": None,
            **({"unfinished": [recipes[i] for i in sorted(timed_out)]} if timed_out else {})}


if __name__ == "__main__":
    sys.exit(main())
