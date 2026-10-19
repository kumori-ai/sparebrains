"""The goal closer (Kumori task #461): the single steps the loop left open, proved one at a time.

The loop's Lean-only pass (fixer, holes, Lean's automation) leaves a sketch: the model's proof with its failing
steps turned into `sorry`, and each open step printed by Lean as a standalone goal (`theorem sb_goal ...`).
Where one step is left, proving that one goal solves the problem. Chat lanes proved 0 of 176 lemma asks; APOLLO
(arXiv 2505.05758) sends such goals to a Lean-trained prover instead, and Goedel-Prover-V2-8B already runs on
Kaggle (tools/prover_kernel.py). This module is the bookkeeping around that: which goals, in what order, and how
a proved goal goes back into its sketches and in front of the kernel.

Some goals are the theorem again: the sketch kept nothing but `sorry`, so its goal has the theorem's own
conclusion (aime_1987_p5's sketch is a comment and a `sorry`). Those are flagged `restates` and go last; a goal
that is the hard part of a problem (imo_1962_p2's one direction of the set equality) is a real step.

    python3 tools/goal_closer.py list [--out FILE] [--check]     # the open one-step goals, real steps first
    python3 tools/goal_closer.py try --goal SHA --proof FILE     # a proof of one goal: judge it, splice, judge
    python3 tools/goal_closer.py tactic --tactic grind [--jobs 4] [--out FILE]   # one tactic on every readable goal

`tactic` is the tactic-recipe search: no model, Lean only. Every goal here is a step the loop's automation
(subgoals.AUTO_TACTICS) already failed, so each goal a new tactic closes, and whose splice the kernel accepts, is a
problem that tactic solves. It is the evidence for adding a tactic to the chain; it publishes nothing.
"""
import argparse, ast, hashlib, json, re, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT), str(ROOT / "tools")]
import subgoals
from proof_text import PROOF_SEP, extract_proof

NUM_ASCRIPTION = re.compile(r"\(\s*([^():]+?)\s*:\s*[ℝℕℤℚℂ]\s*\)")    # `(3 : ℝ)`, as extract_goal prints numbers


def norm(text):
    return re.sub(r"\s+", " ", text or "").strip()


def goal_sha(goal):
    return hashlib.sha256(norm(goal).encode()).hexdigest()[:12]


def conclusion(signature):
    """The text after a signature's last top-level colon, numbers' type ascriptions dropped, spaces removed."""
    sig = re.sub(r":=\s*by\s*$", "", signature.strip())
    depth, last = 0, None
    for i, c in enumerate(sig):
        if c in "([{⟨":
            depth += 1
        elif c in ")]}⟩":
            depth -= 1
        elif c == ":" and depth == 0 and sig[i + 1:i + 2] != "=":
            last = i
    tail = sig[last + 1:] if last is not None else sig
    return re.sub(r"\s+", "", NUM_ASCRIPTION.sub(r"\1", tail))


def restates(goal, target_text):
    """True when the goal's conclusion is the theorem's own: the sketch did not get past the statement."""
    m = re.search(r"theorem\s+\S+(.*?):=\s*by", target_text, re.S)
    return bool(m) and conclusion("theorem t" + m.group(1) + ":= by") == conclusion(goal)


def _subgoals(row):
    sg = (row.get("tools") or {}).get("subgoals")
    if isinstance(sg, str):
        try:
            sg = ast.literal_eval(sg)
        except (ValueError, SyntaxError):
            return {}
    return sg or {}


def collect(rows, open_keys, read_target):
    """The open problems' one-step goals from the ledger's loop rows, deduplicated by text. Each carries every
    distinct sketch it closes. Real steps first, then by how many sketches one proof would close."""
    by_goal = {}
    for r in rows:
        key = (r.get("target_set"), r.get("target"))
        sketch = (r.get("tools") or {}).get("sketch")
        goals = _subgoals(r).get("goals") or []
        if key not in open_keys or not sketch or len(goals) != 1:
            continue
        sha = goal_sha(goals[0])
        g = by_goal.setdefault(sha, {"sha": sha, "target_set": key[0], "target": key[1], "goal": goals[0],
                                     "sketches": []})
        if key == (g["target_set"], g["target"]) and sketch not in g["sketches"]:
            g["sketches"].append(sketch)
    out = list(by_goal.values())
    for g in out:
        g["restates"] = restates(g["goal"], read_target(g["target_set"], g["target"]))
    return sorted(out, key=lambda g: (g["restates"], -len(g["sketches"]), g["target"], g["sha"]))


def prefix_of(target_text):
    return target_text[:PROOF_SEP.search(target_text).end()]


def goal_file(target_text, goal):
    """The goal as a Lean file of its own, the target's imports and opens above it: what a prover is asked."""
    return subgoals.lemma_file(prefix_of(target_text), goal, "  sorry\n")


def splice(target_text, sketch, body):
    """The sketch with its one `sorry` replaced by a proof of the goal: the full candidate file, or None."""
    prefix = prefix_of(target_text)
    text = prefix + "\n" + sketch.lstrip("\n")
    hs = subgoals.holes(text, prefix.count("\n") + 1)
    if not hs or len(hs) != 1:
        return None
    lines = [l for l in body.rstrip("\n").split("\n")]
    base = min(subgoals.indent(l) for l in lines if l.strip())
    return subgoals._with_tactics(text, {hs[0]: [l[base:] if l.strip() else "" for l in lines]})


def check(goals, read_target, judge_text):
    """Marks each goal `file_ok`: its own file type-checks with `sorry`. extract_goal can print a goal that does
    not elaborate alone (amc12a_2020_p15's `‖a - b‖` with untyped a and b, 1 of the first 5 checked on
    2026-10-17), and a prover cannot be judged on a statement Lean cannot read."""
    for g in goals:
        r = judge_text(goal_file(read_target(g["target_set"], g["target"]), g["goal"]))
        g["file_ok"] = r["verdict"] == "wellformed"
    return goals


def close(goal, target_text, body, judge_text):
    """A proof body of one goal: the goal judged alone, then spliced into each sketch until the kernel accepts.
    Returns {verdict, stage, candidate, output}: stage is where it stopped (goal, splice, problem)."""
    r = judge_text(subgoals.lemma_file(prefix_of(target_text), goal["goal"], body))
    if r["verdict"] != "accept":
        return {"verdict": "reject", "stage": "goal", "output": r.get("output") or r.get("reason") or ""}
    last = {"verdict": "reject", "stage": "splice", "output": "no sketch had exactly one hole"}
    for sketch in goal["sketches"]:
        cand = splice(target_text, sketch, body)
        if cand is None:
            continue
        r = judge_text(cand)
        if r["verdict"] == "accept":
            return {"verdict": "accept", "stage": "problem", "candidate": cand, "output": r.get("output") or ""}
        last = {"verdict": "reject", "stage": "problem", "output": r.get("output") or r.get("reason") or ""}
    return last


def try_tactic(goals, tactic, read_target, judge_text, jobs=4):
    """[{sha, target_set, target, restates, verdict, stage, seconds}] for `tactic` as the whole proof of each
    readable goal, judged alone and, where Lean accepts it, spliced into the goal's sketches (close())."""
    from concurrent.futures import ThreadPoolExecutor
    import time

    def one(g):
        t0 = time.monotonic()
        r = close(g, read_target(g["target_set"], g["target"]), f"  {tactic}\n", judge_text)
        return {"sha": g["sha"], "target_set": g["target_set"], "target": g["target"], "restates": g["restates"],
                "verdict": r["verdict"], "stage": r["stage"], "seconds": round(time.monotonic() - t0, 1),
                **({"candidate": r["candidate"]} if r["verdict"] == "accept" else {})}

    with ThreadPoolExecutor(jobs) as pool:                       # each judge is its own Lean process
        return list(pool.map(one, [g for g in goals if g.get("file_ok")]))


QUEUE = ROOT / "ledger" / "goal-queue.json"


def queue(goals, read_target, n):
    """Prover problems for a goal batch: one entry per goal whose own file Lean can read, real steps before
    restatements (collect's order), each the goal's file as the statement and its sha as `goal`."""
    return [{"target_set": g["target_set"], "target": g["target"], "goal": g["sha"], "n": n,
             "statement": goal_file(read_target(g["target_set"], g["target"]), g["goal"])}
            for g in goals if g.get("file_ok")]


def _load():
    import relay
    rows = []
    for f in (ROOT / "ledger").glob("**/*.jsonl"):
        for line in f.open():
            if '"sketch"' in line:
                try:
                    rows.append(json.loads(line))
                except ValueError:
                    pass
    open_keys = {(t["target_set"], t["target"]) for t in relay.fetch_json("/targets.json")["open"]}
    read = lambda s, t: (ROOT / "targets" / s / f"{t}.lean").read_text()
    return collect(rows, open_keys, read), read


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("cmd", choices=["list", "try", "tactic"])
    ap.add_argument("--tactic", help="tactic: the tactic tried as the whole proof of every readable goal")
    ap.add_argument("--jobs", type=int, default=4, help="tactic: Lean processes at once (~3 GB each)")
    ap.add_argument("--out")
    ap.add_argument("--check", action="store_true", help="list: judge each goal's own file (Lean, ~20 s a goal)")
    ap.add_argument("--goal", help="try: a goal's sha from `list`")
    ap.add_argument("--proof", help="try: a file with the proof, a whole `theorem sb_goal ... := by` or tactics")
    args = ap.parse_args()
    if args.cmd == "tactic":                       # the stored queue, file_ok already judged: no ledger rescan
        import lean_tools
        goals = json.loads(QUEUE.read_text())
        read = lambda s, t: (ROOT / "targets" / s / f"{t}.lean").read_text()
        rows = try_tactic(goals, args.tactic, read, lean_tools.judge_text, args.jobs)
        solved = sorted({(r["target_set"], r["target"]) for r in rows if r["verdict"] == "accept"})
        stages = {s: sum(r["stage"] == s and r["verdict"] == "reject" for r in rows) for s in ("goal", "splice", "problem")}
        print(f"{args.tactic}: {len(rows)} goals tried, {sum(r['verdict'] == 'accept' for r in rows)} closed and "
              f"spliced, {len(solved)} problems; rejected at goal {stages['goal']}, no one-hole sketch "
              f"{stages['splice']}, splice rejected {stages['problem']}", file=sys.stderr)
        for s, t in solved:
            print(f"  solved: {s}/{t}", file=sys.stderr)
        if args.out:
            Path(args.out).write_text(json.dumps(rows, ensure_ascii=False, indent=1))
        return 0
    goals, read = _load()
    if args.cmd == "list":
        if args.check:
            import lean_tools
            check(goals, read, lean_tools.judge_text)
            print(f"{sum(g['file_ok'] for g in goals)} of {len(goals)} goal files type-check", file=sys.stderr)
        real = [g for g in goals if not g["restates"]]
        print(f"{len(goals)} one-step goals on {len({(g['target_set'], g['target']) for g in goals})} open problems; "
              f"{len(real)} real steps, {len(goals) - len(real)} restate the theorem", file=sys.stderr)
        text = json.dumps(goals, ensure_ascii=False, indent=1)
        Path(args.out).write_text(text) if args.out else print(text)
        return 0
    g = next((g for g in goals if g["sha"] == args.goal), None)
    if not g:
        sys.exit(f"no open one-step goal {args.goal}")
    raw = Path(args.proof).read_text()
    body = extract_proof(raw, "sb_goal") if "sb_goal" in raw else raw
    import lean_tools
    r = close(g, read(g["target_set"], g["target"]), body, lean_tools.judge_text)
    print(json.dumps({k: v for k, v in r.items() if k != "candidate"}, ensure_ascii=False)[:2000])
    if r["verdict"] == "accept":
        print(r["candidate"])
    return 0 if r["verdict"] == "accept" else 1


if __name__ == "__main__":
    sys.exit(main())
