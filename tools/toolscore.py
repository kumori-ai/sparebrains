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
"""
import argparse, hashlib, os, sys, time
from datetime import datetime, timezone
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


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--half", choices=["report", "tune"], default="report")
    ap.add_argument("--slice", default="0/1", help="k/N: every Nth stored reject from k, for a matrix of jobs")
    ap.add_argument("--max-minutes", type=float, default=0)
    ap.add_argument("--max-rows", type=int, default=100000)
    ap.add_argument("--speed", action="store_true", help="the speed receipt's frozen weekly sample, whole chain only")
    args = ap.parse_args()
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
