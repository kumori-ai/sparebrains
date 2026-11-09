"""A guide's blueprint for a stalled problem: statements only (DECISIONS.md 2026-11-09, the stall router).

A guide (Codex or Claude, from a local session; the strongest reader we have, never a lane) is asked for 2 to 6 Lean
propositions that, proved, give the target. This tool writes every line of proof text itself: one `have bp_i : <s> :=
by sorry` per statement and a closing line of Lean's own closers (FINAL). Then the gate, three Lean runs:
  1. audit: each statement elaborated in the target's context; a proof subterm that is not one of the context's own
     hypotheses fails it (Codex 20261109T205417832903Z: `(show P → P from id) = id` is a Prop that carries a proof).
  2. duplicates: a statement Lean's automation proves equivalent to the target is no decomposition (a limited filter:
     a timeout or a miss drops nothing, Codex 204946451069Z f2).
  3. the sketch must judge `wellformed`: the statements type-check and FINAL assembles the target from them; `accept`
     means the statements alone closed it (nothing left for a small lane), a reject means they do not imply it.
Every kernel-checked step then comes from Lean's automation or a small lane (subgoals.prove_sketch); the guide's
contribution is which propositions to prove, credited as try_mode `guided`, never as "free models plus tools".
"""
import argparse
import json
import re
import sys
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT), str(ROOT / "tools")]
import goal_closer
import subgoals

MIN_STEPS, MAX_STEPS = 2, 6
HAVE = re.compile(r"^  have bp_(\d+) : (.+) := by$")
FINAL = "first | assumption | " + " | ".join(subgoals.AUTO_TACTICS)
BLUEPRINTS = ROOT / "ledger" / "stall" / "blueprints"
# forEachExpr' instantiates binders, so a quantified statement's body is visited with its variables as fvars; a
# hypothesis named in a statement is an fvar and passes; any other proof-typed subterm is the guide supplying a proof.
AUDIT = '''
-- the blueprint gate's audit (tools/blueprint.py): a statement may name a hypothesis, never carry a proof
open Lean Elab Tactic Meta in
elab "audit_prop " t:term : tactic => do
  let e ← elabTermEnsuringType t (mkSort Level.zero)
  Term.synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  forEachExpr' e fun sub => do
    if sub.isFVar then return false
    if sub.hasLooseBVars then return true
    if ← isProof sub then throwError "AUDIT_FAIL proof term in statement: {sub}"
    return true
  logInfo m!"AUDIT_OK"
'''


def statements(reply):
    """The first JSON list in the reply, its string items stripped; everything else in the reply is ignored."""
    dec = json.JSONDecoder()
    for m in re.finditer(r"\[", reply or ""):
        try:
            got, _ = dec.raw_decode(reply, m.start())
        except ValueError:
            continue
        if isinstance(got, list):
            return [s.strip() for s in got if isinstance(s, str) and s.strip()]
    return []


def sketch(prefix, stmts):
    body = "".join(f"  have bp_{i} : {s} := by\n    sorry\n" for i, s in enumerate(stmts, 1))
    return prefix + "\n" + body + f"  {FINAL}\n"


def _parts(prefix):
    """(imports and the rest of the preamble split after the last import line, the declaration header)."""
    at = subgoals.DECL.search(prefix).start()
    pre, header = prefix[:at], prefix[at:]
    lines = pre.split("\n")
    last = max((i for i, l in enumerate(lines) if l.startswith("import ")), default=-1)
    return "\n".join(lines[:last + 1]), "\n".join(lines[last + 1:]), header


def audit_text(prefix, stmts):
    """(the audit file, the 1-based line of each statement's audit_prop). One `example` per statement in the target's
    binders, the earlier statements as hypotheses bp_j, so one failure stops nothing else (in one tactic block the first
    AUDIT_FAIL ended the block and the rest went unaudited, 2026-11-09) and a statement may name bp_1."""
    imports, rest, _ = _parts(prefix)
    binders, _ = split_signature(prefix)
    text, lines = imports + "\n" + AUDIT + rest, []
    for i, s in enumerate(stmts, 1):
        earlier = "".join(f" (bp_{j} : {stmts[j - 1]})" for j in range(1, i))
        text += f"example {binders}{earlier} : True := by\n"
        lines.append(text.count("\n") + 1)
        text += f"  audit_prop ({s})\n  trivial\n\n"
    return text, lines


def audit(prefix, stmts, run_lean):
    """[{i, ok, why}] per statement, 1-based: an error Lean places in a statement's example is that statement's; fewer
    AUDIT_OK lines than clean statements means Lean did not get to them (no pass by silence)."""
    text, lines = audit_text(prefix, stmts)
    out, _ = run_lean(text)
    bounds = [l - 1 for l in lines] + [text.count("\n") + 2]
    why = {}
    for line in out.splitlines():
        m = subgoals.MSG.match(line)
        if not m or m.group(3) != "error":
            continue
        at = int(m.group(1))
        for i in range(len(stmts)):
            if bounds[i] <= at < bounds[i + 1]:
                why.setdefault(i, m.group(4).replace("AUDIT_FAIL ", ""))
    if "timeout after" in out:
        return [{"i": i + 1, "ok": False, "why": out.strip()} for i in range(len(stmts))]
    clean = [i for i in range(len(stmts)) if i not in why]
    if out.count("AUDIT_OK") < len(clean):
        for i in clean:
            why[i] = "no AUDIT_OK from Lean for this statement"
    return [{"i": i + 1, "ok": i not in why, "why": why.get(i)} for i in range(len(stmts))]


def split_signature(prefix):
    """(binders, conclusion) of the declaration, whitespace collapsed. goal_closer.conclusion gives the tail alone
    with spaces removed, for comparing goals; the duplicate filter needs both halves as Lean source."""
    header = prefix[subgoals.DECL.search(prefix).start():]
    sig = re.sub(r":=\s*by\s*$", "", header.strip())
    sig = re.sub(r"^(?:theorem|lemma)\s+\S+", "", sig, count=1)
    depth, last = 0, None
    for i, c in enumerate(sig):
        if c in "([{⟨":
            depth += 1
        elif c in ")]}⟩":
            depth -= 1
        elif c == ":" and depth == 0 and sig[i + 1:i + 2] != "=":
            last = i
    squash = lambda t: re.sub(r"\s+", " ", t).strip()
    return (squash(sig[:last]), squash(sig[last + 1:])) if last is not None else ("", squash(sig))


def duplicate_text(prefix, stmts):
    """One file: for each statement an example proving the target from it and one proving it from the target, both
    by FINAL. Returns (text, [(name f<i>|r<i>, start line)]) for goal_closer.recipes_passing."""
    imports, rest, _ = _parts(prefix)
    binders, concl = split_signature(prefix)
    text, starts = imports + "\n" + rest, []
    for i, s in enumerate(stmts, 1):
        for name, hyp, goal in ((f"f{i}", f"(bp_dup : {s})", concl), (f"r{i}", f"(bp_tgt : {concl})", s)):
            starts.append((name, text.count("\n") + 1))
            text += f"example {binders} {hyp} : {goal} := by\n  {FINAL}\n\n"
    return text, starts


def duplicates(prefix, stmts, run_lean):
    """0-based indexes of statements equivalent to the target by Lean's automation, both ways. Limited: a miss or a
    timeout certifies nothing and drops nothing."""
    text, starts = duplicate_text(prefix, stmts)
    out, _ = run_lean(text)
    passed = {starts[k][0] for k in goal_closer.recipes_passing(out, starts, text.count("\n") + 1)}
    return {i for i in range(len(stmts)) if f"f{i + 1}" in passed and f"r{i + 1}" in passed}


def gate(prefix, stmts, run_lean, judge_text):
    n = len(stmts)
    if not MIN_STEPS <= n <= MAX_STEPS:
        return {"ok": False, "why": [f"{n} statements: a blueprint has {MIN_STEPS} to {MAX_STEPS}"], "sketch": None}
    a = audit(prefix, stmts, run_lean)
    bad = [x for x in a if not x["ok"]]
    if bad:
        return {"ok": False, "why": [f"statement {x['i']}: {x['why']}" for x in bad], "sketch": None, "audit": a}
    dup = sorted(duplicates(prefix, stmts, run_lean))
    if dup:
        return {"ok": False, "why": [f"statement {i + 1} is equivalent to the target by Lean's automation: no decomposition"
                                     for i in dup], "sketch": None, "audit": a, "duplicates": dup}
    sk = sketch(prefix, stmts)
    j = judge_text(sk)
    v = j.get("verdict")
    if v == "wellformed":
        return {"ok": True, "why": [], "sketch": sk, "audit": a, "duplicates": [], "judge": v}
    why = ("the statements alone close the target: nothing left for a small lane" if v == "accept" else
           f"statements do not imply the target by automation: {(j.get('reason') or '')[:300]}")
    return {"ok": False, "why": [why], "sketch": sk, "audit": a, "duplicates": [], "judge": v}


MAX_ASKS_PILOT = 12


def lemma_text(prefix, stmts, i):
    """Hole i (0-based) as a lemma of its own: the target's binders, the earlier statements as hypotheses bp_j, named
    sb_goal as subgoals.prove_goal expects. The queue's extract_goal clears hypotheses the goal does not mention, which
    for a blueprint is the earlier steps themselves (hole 5 of the first blueprint lost bp_1..bp_4, 2026-11-09)."""
    binders, _ = split_signature(prefix)
    earlier = "".join(f" (bp_{j + 1} : {stmts[j]})" for j in range(i))
    return f"theorem sb_goal {binders}{earlier} : {stmts[i]} := by"


def fill(prefix, stmts, judge_text, asks=(), max_asks=MAX_ASKS_PILOT, on_try=None):
    """Prove the holes: Lean's closers (FINAL) on each hole's lemma first, then the asks in turn (two tries each,
    subgoals.prove_goal). Every hole is attempted while the budget lasts, so `failed` (asked, not proved) and
    `unattempted` (the budget ran out first) stay apart (Codex 20261109T204513251417Z f6). closed_by maps a 1-based
    hole to "lean" or the index of the ask that proved it. When every hole closes the bodies are spliced under their
    `have` and the whole file is judged: `final` is that verdict, `accepted` the text on accept."""
    sk = sketch(prefix, stmts)
    top = prefix.count("\n") + 1
    hole_lines = subgoals.holes(sk, top)
    budget, plan = {"asks": 0, "max": max_asks}, {}
    log = {"holes": len(stmts), "closed_by": {}, "failed": [], "unattempted": [], "tries": [], "answered": 0}
    for i, s in enumerate(stmts):
        n, stmt = i + 1, lemma_text(prefix, stmts, i)
        r = judge_text(subgoals.lemma_file(prefix, stmt, "  " + FINAL))
        if r["verdict"] == "accept":
            plan[i], log["closed_by"][n] = [FINAL], "lean"
            continue
        said, asked_here = r.get("output") or "", 0
        for who, ask in enumerate(asks):
            body, tries = subgoals.prove_goal(prefix, stmt, sk, said, ask, judge_text, budget)
            asked_here += len(tries)
            for t in tries:
                log["tries"].append({"hole": n, "by": who, "verdict": t["verdict"], "reason": (t.get("reason") or "")[:200]})
                if on_try:
                    on_try(n, who, stmt, t)
            if body:
                plan[i], log["closed_by"][n] = body, who
                break
        log["answered"] += asked_here
        if i not in plan:
            log["failed" if asked_here or not asks else "unattempted"].append(n)
    # asked = budget consumed (prove_goal counts an ask before the lane answers); unanswered = asks a parked or capped
    # lane, or the call cap, swallowed with no reply (Codex 20261109T213007122693Z f3)
    log["asked"] = budget["asks"]
    log["unanswered"] = budget["asks"] - log["answered"]
    if len(plan) == len(stmts):
        final = subgoals._with_tactics(sk, {hole_lines[i]: plan[i] for i in plan})
        j = judge_text(final)
        log["final"] = j["verdict"]
        if j["verdict"] == "accept":
            log["accepted"] = final
    return log


def guide_prompt(target_text, misses=()):
    """The ask: propositions only. A guide's tactics are never read (statements() takes the JSON list and nothing else)."""
    near = "".join(f"- {m}\n" for m in misses)
    return (f"You are the guide for a Lean 4 (Mathlib) theorem the free models have not proved. Reply with ONE JSON list "
            f"of {MIN_STEPS} to {MAX_STEPS} Lean propositions (strings), in order, such that a proof of each, in the "
            "theorem's context, lets `first | assumption | omega | linarith | nlinarith | positivity | decide | norm_num | "
            "simp | aesop | grind | exact?` close the theorem from them. Rules: a proposition may name the theorem's "
            "variables and hypotheses and earlier statements as bp_1, bp_2...; it must not contain any proof term, tactic "
            "block, `by`, `sorry`, or a restatement of the theorem itself; make each step small enough that a 3B model or "
            "Lean's automation could prove it. Write nothing else: any text outside the JSON list is ignored.\n\n"
            f"```lean\n{target_text.strip()}\n```\n"
            + (f"\nWhat the free models' closest misses said first:\n{near}" if near else ""))


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--prompt", metavar="SET/TARGET", help="print the guide's ask for this problem")
    ap.add_argument("--gate", metavar="SET/TARGET", help="run the gate on a guide's reply (--reply) and store the result")
    ap.add_argument("--reply", help="file holding the guide's reply")
    ap.add_argument("--guide", default="codex", help="who wrote the reply (recorded, e.g. codex, claude)")
    args = ap.parse_args(argv)
    from proof_text import PROOF_SEP
    key = args.prompt or args.gate
    if not key:
        ap.error("--prompt or --gate")
    tset, name = key.rsplit("/", 1)
    target_text = (ROOT / "targets" / tset / f"{name}.lean").read_text()
    prefix = target_text[:PROOF_SEP.search(target_text).end()]
    if args.prompt:
        import relay
        d = relay.fetch_dossier(tset, name)
        misses = [f"{m.get('backend')}: {m.get('failure_kind')}" for m in (d.get("near_misses") or [])[:3] if m.get("failure_kind")]
        print(guide_prompt(target_text, misses))
        return 0
    import lean_tools
    stmts = statements(Path(args.reply).read_text())
    g = gate(prefix, stmts, lean_tools.run_lean, lean_tools.judge_text)
    ts = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    BLUEPRINTS.mkdir(parents=True, exist_ok=True)
    out = BLUEPRINTS / f"{name}-{ts}.json"
    out.write_text(json.dumps({"ts": ts, "target_set": tset, "target": name, "guide": args.guide, "statements": stmts,
                               **g}, indent=1, ensure_ascii=False) + "\n")
    print(("PASS" if g["ok"] else "REJECT") + f" {key}: {len(stmts)} statements; " + ("; ".join(g["why"]) or "wellformed")
          + f"\n  {out.relative_to(ROOT)}")
    return 0 if g["ok"] else 1


if __name__ == "__main__":
    sys.exit(main())
