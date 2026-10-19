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


BINDER = re.compile(r"\(([^():]+?)\s*:\s*(ℝ|ℕ|ℤ|ℚ)\)")


def goal_vars(goal):
    """{type: [names]} of the goal's own variables, from its binders before `:= by` (`(x y : ℝ)`)."""
    out = {}
    for names, ty in BINDER.findall(goal.split(":= by")[0]):
        out.setdefault(ty, []).extend(n for n in names.split() if n.isidentifier() or n[0].isalpha())
    return out


def expand(recipe, goal):
    """A recipe for this goal: plain recipes as written; a template built from the goal's own variables, the way
    our verified proofs use these tactics (2026-10-19: nlinarith 191 times, mostly with sq_nonneg hints over the
    problem's variables; interval_cases 40 times on a bounded natural). None when the template does not apply.
      @nlinarith-sq    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), ..., sq_nonneg a, ...] over ℝ/ℚ variables
      @interval-cases  interval_cases n <;> omega, for the first ℕ/ℤ variable"""
    if not recipe.startswith("@"):
        return recipe
    v = goal_vars(goal)
    if recipe == "@nlinarith-sq":
        xs = (v.get("ℝ", []) + v.get("ℚ", []))[:4]
        if not xs:
            return None
        hints = [f"sq_nonneg ({a} - {b})" for i, a in enumerate(xs) for b in xs[i + 1:]]
        hints += [f"sq_nonneg ({a} + {b})" for i, a in enumerate(xs) for b in xs[i + 1:]]
        hints += [f"sq_nonneg {a}" for a in xs]
        return "nlinarith [" + ", ".join(hints) + "]"
    if recipe == "@interval-cases":
        ns = v.get("ℕ", []) + v.get("ℤ", [])
        return f"interval_cases {ns[0]} <;> omega" if ns else None
    raise ValueError(f"unknown recipe template {recipe}")


def recipe_body(recipe):
    """A recipe's tactics as a proof body: steps split on `;`, each its own line (`field_simp; ring_nf`)."""
    return "".join(f"  {s.strip()}\n" for s in recipe.split(";") if s.strip())


def recipe_file(target_text, goal, recipes):
    """One Lean file holding the goal once per recipe (sb_goal_r0, sb_goal_r1, ...), so Lean and mathlib load once
    for all of them, and the first line of each theorem: [(name, first line)]."""
    text, starts = prefix_of(target_text), []
    text = text[:subgoals.DECL.search(text).start()]
    for i, recipe in enumerate(recipes):
        name = f"sb_goal_r{i}"
        starts.append((name, text.count("\n") + 1))
        text += goal.replace("sb_goal", name, 1) + "\n" + recipe_body(recipe) + "\n"
    return text, starts


def recipes_passing(output, starts, n_lines):
    """The recipe indexes whose theorem drew no error and no `sorry` in one Lean run's output. A filter only:
    every pass is judged again by the kernel (close()) before it counts."""
    bad = set()
    bounds = [l for _, l in starts] + [n_lines + 1]
    for line in output.splitlines():
        m = subgoals.MSG.match(line)
        if not m or not (m.group(3) == "error" or "sorry" in m.group(4)):
            continue
        at = int(m.group(1))
        for i in range(len(starts)):
            if bounds[i] <= at < bounds[i + 1]:
                bad.add(i)
    if "timeout after" in output:                    # no messages to place: nothing passes
        return []
    return [i for i in range(len(starts)) if i not in bad]


def sweep(goals, recipes, read_target, run_lean, judge_text, status_of, jobs=3):
    """Every recipe on every goal: one Lean run per goal for all recipes, then the kernel's full judge and splice
    (close()) on each recipe that passed. Rows are the record (no proof text: the repository is public and a solve
    on a measured problem waits for its bar); `candidates` maps (sha, recipe) to an accepted file, kept in memory.
    Rows say `outcome` and `at`, never `verdict` or `ts`: they are measurements, not tries, so the ladder and the
    daily log, which read every ledger row's verdict, never count them."""
    from concurrent.futures import ThreadPoolExecutor
    import time
    from datetime import datetime, timezone
    candidates = {}

    def one(g):
        target_text = read_target(g["target_set"], g["target"])
        mine = [(r, expand(r, g["goal"])) for r in recipes]
        mine = [(r, c) for r, c in mine if c]            # a template with nothing to build from is not tried
        if not mine:
            return []
        text, starts = recipe_file(target_text, g["goal"], [c for _, c in mine])
        out, secs = run_lean(text)
        passing = set(recipes_passing(out, starts, text.count("\n") + 1))
        rows = []
        for i, (template, recipe) in enumerate(mine):
            row = {"at": datetime.now(timezone.utc).isoformat(timespec="seconds"), "recipe": template,
                   **({"tactics": recipe} if recipe != template else {}), "sha": g["sha"],
                   "target_set": g["target_set"], "target": g["target"], "status": status_of(g),
                   "restates": g.get("restates"), "outcome": "failed", "stage": "goal", "lean_s": round(secs, 1)}
            if i in passing:
                t0 = time.monotonic()
                r = close(g, target_text, recipe_body(recipe), judge_text)
                row.update(outcome="solved" if r["verdict"] == "accept" else "failed", stage=r["stage"],
                           judge_s=round(time.monotonic() - t0, 1))
                if r["verdict"] == "accept":
                    candidates[(g["sha"], recipe)] = r["candidate"]
            rows.append(row)
        return rows

    with ThreadPoolExecutor(jobs) as pool:
        rows = [r for rs in pool.map(one, goals) for r in rs]
    return rows, candidates


QUEUE = ROOT / "ledger" / "goal-queue.json"


def queue(goals, read_target, n):
    """Prover problems for a goal batch: one entry per goal whose own file Lean can read, real steps before
    restatements (collect's order), each the goal's file as the statement and its sha as `goal`."""
    return [{"target_set": g["target_set"], "target": g["target"], "goal": g["sha"], "n": n,
             "statement": goal_file(read_target(g["target_set"], g["target"]), g["goal"])}
            for g in goals if g.get("file_ok")]


def _load(keys="open"):
    """(goals, read): the one-step goals of the open problems, or with keys="solved" those of the solved ones (the
    sweep's back-check: how today's recipes would have done on what is already done)."""
    import relay
    rows = []
    for f in (ROOT / "ledger").glob("**/*.jsonl"):
        for line in f.open():
            if '"sketch"' in line:
                try:
                    rows.append(json.loads(line))
                except ValueError:
                    pass
    want = {(t["target_set"], t["target"]) for t in relay.fetch_json("/targets.json")[keys]}
    want = {k for k in want if (ROOT / "targets" / k[0] / f"{k[1]}.lean").exists()}
    read = lambda s, t: (ROOT / "targets" / s / f"{t}.lean").read_text()
    return collect(rows, want, read), read


BAR_RUNGS = ("amc12", "math-L5", "aime")             # tools/prover.py RUNGS: the stage-3 bar's 50
# Who wrote a sweep solve: no model, a recipe of Lean tactics. Recorded through the goal batches' own path
# (prover.judge_goals: the kernel's judge, the ledger row as try mode goal-closer, verified/, the site).
TACTIC_LANE = {"backend": "lean-tactic-recipe", "provider": "lean", "model": "no model", "mode": "goal-closer",
               "file": "tactic"}


def publish_solves(solves, goals_by_sha, run_id, record, judge_text):
    """Record each (sha, recipe) solve on a problem outside the bar as a goal-closer try: judged again by the
    kernel on the way in. Returns judge_goals' counts."""
    import prover
    answers = [{"batch": run_id, "target_set": goals_by_sha[sha]["target_set"], "target": goals_by_sha[sha]["target"],
                "sample": i, "goal": sha, "text": "```lean4\n" + goals_by_sha[sha]["goal"] + "\n" + recipe_body(recipe)
                + "```", "config": {"model": f"recipe: {recipe}"}}
               for i, (sha, recipe) in enumerate(solves)]
    return prover.judge_goals(answers, prover.prover_rows(lane=TACTIC_LANE), goals_by_sha, judge_text=judge_text,
                              record=record, run_id=run_id, lane=TACTIC_LANE)


def run_sweep(args):
    """`sweep`: every recipe on the open goals (the stored queue, readable ones) and on the solved problems' goals,
    one slice of them. Rows go to --out (the ledger); solves are reported by name only, never as proof text."""
    import lean_tools, relay
    recipes = [r.strip() for r in args.recipes.split(",") if r.strip()]
    k, n = (int(x) for x in args.slice.split("/"))
    targets = relay.fetch_json("/targets.json")
    rung = {(t["target_set"], t["target"]): t.get("rung") for t in targets["open"] + targets["solved"]}
    open_goals = [{**g, "status": "open"} for g in json.loads(QUEUE.read_text()) if g.get("file_ok")]
    solved_goals, read = _load("solved")
    goals = sorted(open_goals + [{**g, "status": "solved"} for g in solved_goals], key=lambda g: g["sha"])[k::n]
    rows, cands = sweep(goals, recipes, read, lean_tools.run_lean, lean_tools.judge_text, lambda g: g["status"],
                        args.jobs)
    for r in rows:
        r["slice"] = args.slice
    if args.out:
        Path(args.out).parent.mkdir(parents=True, exist_ok=True)
        with open(args.out, "a") as f:
            f.writelines(json.dumps(r, ensure_ascii=False) + "\n" for r in rows)
    print(f"sweep {args.slice}: {len(goals)} goals ({sum(g['status'] == 'open' for g in goals)} open), "
          f"{len(recipes)} recipes", file=sys.stderr)
    for recipe in recipes:
        mine = [r for r in rows if r["recipe"] == recipe]
        won = sorted({(r["status"], r["target_set"], r["target"]) for r in mine if r["outcome"] == "solved"})
        times = sorted(r["judge_s"] for r in mine if r["outcome"] == "solved")
        print(f"  {recipe!r}: {sum(r['outcome'] == 'solved' for r in mine)} goals closed and spliced, "
              f"{len({w[1:] for w in won if w[0] == 'open'})} open problems, "
              f"{len({w[1:] for w in won if w[0] == 'solved'})} solved ones re-solved"
              + (f", judge {times[len(times) // 2]} s median" if times else ""), file=sys.stderr)
        for status, s, t in won:
            if status == "open":
                held = rung.get((s, t)) in BAR_RUNGS
                print(f"    open {s}/{t}: " + ("HELD, in the bar's 50" if held else "solved, published below"),
                      file=sys.stderr)
    publish = [(sha, recipe) for sha, recipe in cands
               if next(g for g in goals if g["sha"] == sha)["status"] == "open"
               and rung.get(next((g["target_set"], g["target"]) for g in goals if g["sha"] == sha)) not in BAR_RUNGS]
    if publish and args.publish:
        import prover
        from utilities.kumori_api_client import init, sparebrains_attempt
        init()
        stats = publish_solves(publish, {g["sha"]: g for g in goals}, f"tactics-{args.slice.replace('/', 'of')}",
                               prover.Recorder("sweep", sparebrains_attempt, TACTIC_LANE), lean_tools.judge_text)
        print(f"published: {stats}", file=sys.stderr)
    return 0


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("cmd", choices=["list", "try", "tactic", "sweep"])
    ap.add_argument("--recipes", help="sweep: recipes separated by `,`, steps within one by `;`")
    ap.add_argument("--slice", default="0/1", help="sweep: k/N, every Nth goal from k, for a matrix of jobs")
    ap.add_argument("--publish", action="store_true", help="sweep: record solves outside the bar (needs KUMORI_API_KEY)")
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
    if args.cmd == "sweep":
        return run_sweep(args)
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
