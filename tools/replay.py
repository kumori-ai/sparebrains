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


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--slice", default="0/1")
    ap.add_argument("--max-minutes", type=float, default=0)
    ap.add_argument("--report", action="store_true")
    args = ap.parse_args()
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


if __name__ == "__main__":
    sys.exit(main())
