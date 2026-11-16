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
import hashlib
import json
import re
import sys
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT), str(ROOT / "tools")]
import check
import goal_closer
import replay
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


STEM = "bp"              # the statements are bp_1, bp_2..; a blueprint of a hole whose lemma already has those takes the next


def stem_of(doc):
    return doc.get("stem") or STEM


def next_stem(stem):
    """bp, bq, br..: a hole's lemma carries the earlier statements as hypotheses under the parent's names, so the
    hole's own blueprint names its statements apart (a second bp_1 would hide the first from every later statement)."""
    return stem[0] + chr(ord(stem[1]) + 1)


def subs_of(node):
    """The blueprints given to holes of this node (a manifest's problem, a held file's problem, or one of their
    nodes): `subs`, a list; the first form (2026-11-16) was `sub`, one node."""
    return list(node.get("subs") or ([node["sub"]] if node.get("sub") else []))


def sketch(prefix, stmts, final=None, stem=STEM):
    """`final` is the blueprint's own closing line when the gate had to pick one (its `final`), else FINAL."""
    body = "".join(f"  have {stem}_{i} : {s} := by\n    sorry\n" for i, s in enumerate(stmts, 1))
    return prefix + "\n" + body + f"  {final or FINAL}\n"


def _parts(prefix):
    """(imports and the rest of the preamble split after the last import line, the declaration header)."""
    at = subgoals.DECL.search(prefix).start()
    pre, header = prefix[:at], prefix[at:]
    lines = pre.split("\n")
    last = max((i for i, l in enumerate(lines) if l.startswith("import ")), default=-1)
    return "\n".join(lines[:last + 1]), "\n".join(lines[last + 1:]), header


def audit_text(prefix, stmts, stem=STEM):
    """(the audit file, the 1-based line of each statement's audit_prop). One `example` per statement in the target's
    binders, the earlier statements as hypotheses bp_j, so one failure stops nothing else (in one tactic block the first
    AUDIT_FAIL ended the block and the rest went unaudited, 2026-11-09) and a statement may name bp_1."""
    imports, rest, _ = _parts(prefix)
    binders, _ = split_signature(prefix)
    text, lines = imports + "\n" + AUDIT + rest, []
    for i, s in enumerate(stmts, 1):
        earlier = "".join(f" ({stem}_{j} : {stmts[j - 1]})" for j in range(1, i))
        text += f"example {binders}{earlier} : True := by\n"
        lines.append(text.count("\n") + 1)
        text += f"  audit_prop ({s})\n  trivial\n\n"
    return text, lines


def audit(prefix, stmts, run_lean, stem=STEM):
    """[{i, ok, why}] per statement, 1-based: an error Lean places in a statement's example is that statement's; fewer
    AUDIT_OK lines than clean statements means Lean did not get to them (no pass by silence)."""
    text, lines = audit_text(prefix, stmts, stem)
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
    if check.unfinished(out):
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
    depth, last = 0, None                        # the first top-level colon: binders are bracketed, a conclusion's
    for i, c in enumerate(sig):                  # `∀ m : ℕ,` is not (the last one split hole 1's lemma there, 2026-11-16)
        if c in "([{⟨":
            depth += 1
        elif c in ")]}⟩":
            depth -= 1
        elif c == ":" and depth == 0 and sig[i + 1:i + 2] != "=":
            last = i
            break
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


def gate(prefix, stmts, run_lean, judge_text, stem=STEM):
    n = len(stmts)
    if not MIN_STEPS <= n <= MAX_STEPS:
        return {"ok": False, "why": [f"{n} statements: a blueprint has {MIN_STEPS} to {MAX_STEPS}"], "sketch": None}
    a = audit(prefix, stmts, run_lean, stem)
    bad = [x for x in a if not x["ok"]]
    if bad:
        return {"ok": False, "why": [f"statement {x['i']}: {x['why']}" for x in bad], "sketch": None, "audit": a}
    dup = sorted(duplicates(prefix, stmts, run_lean))
    if dup:
        return {"ok": False, "why": [f"statement {i + 1} is equivalent to the target by Lean's automation: no decomposition"
                                     for i in dup], "sketch": None, "audit": a, "duplicates": dup}
    sk = sketch(prefix, stmts, stem=stem)
    j = judge_text(sk)
    v = j.get("verdict")
    if v == "wellformed":
        return {"ok": True, "why": [], "sketch": sk, "audit": a, "duplicates": [], "judge": v}
    if v != "accept":
        # `first | a | b` does not catch a closer that runs out of heartbeats, so one slow alternative fails the line
        # (2026-11-16: aesop timed out before grind, which closes hole 1's sub-blueprint alone in 13 s). Each closer
        # apart, in FINAL's order; the first that leaves only the holes is recorded and is the line assembled later.
        for alt in FINAL[len("first | "):].split(" | "):
            ska = sketch(prefix, stmts, alt, stem)
            if judge_text(ska).get("verdict") == "wellformed":
                return {"ok": True, "why": [], "sketch": ska, "final": alt, "audit": a, "duplicates": [], "judge": "wellformed",
                        "note": f"the one-line closer failed ({(j.get('reason') or '')[:200]}); `{alt}` alone closes it"}
    why = ("the statements alone close the target: nothing left for a small lane" if v == "accept" else
           f"statements do not imply the target by automation: {(j.get('reason') or '')[:300]}")
    return {"ok": False, "why": [why], "sketch": sk, "audit": a, "duplicates": [], "judge": v}


MAX_ASKS_PILOT = 12


def lemma_text(prefix, stmts, i, stem=STEM):
    """Hole i (0-based) as a lemma of its own: the target's binders, the earlier statements as hypotheses bp_j, named
    sb_goal as subgoals.prove_goal expects. The queue's extract_goal clears hypotheses the goal does not mention, which
    for a blueprint is the earlier steps themselves (hole 5 of the first blueprint lost bp_1..bp_4, 2026-11-09)."""
    binders, _ = split_signature(prefix)
    earlier = "".join(f" ({stem}_{j + 1} : {stmts[j]})" for j in range(i))
    return f"theorem sb_goal {binders}{earlier} : {stmts[i]} := by"


def hole_target(target_text, stmts, hole, stem=STEM):
    """Hole `hole` (1-based) as a target of its own, `sorry` for its proof: what a sub-blueprint decomposes. Hole 1 of
    the first blueprint is a theorem in itself (a number with four divisors is p^3 or p*q, with both divisor sums);
    8 prover samples left 3 with a sorry and 5 rejected (2026-11-16)."""
    prefix = goal_closer.prefix_of(target_text)
    return subgoals.lemma_file(prefix, lemma_text(prefix, stmts, hole - 1, stem), "  sorry\n")


PASSES = (1, 2)          # breadth first: every open hole gets one try from each lane before any gets a second


def lean_tier(lemma_prefix, judge_text, run_lean=None):
    """The closer Lean alone finds for one hole, or None. With run_lean, the no-model baseline's 30 recipes one at a
    time in halving batches (replay.baseline_one): a single `first | ... | grind | exact?` line closed 0 of the first
    blueprint's 6 holes while the recipes run apart closed 2 by grind (2026-11-09; an earlier closer ate the judge's
    time). Without run_lean, the FINAL line judged once (the unit tests' path)."""
    if run_lean:
        return replay.baseline_one(lemma_prefix + "\n  sorry", run_lean, judge_text).get("closer")
    return FINAL if judge_text(lemma_prefix + "\n  " + FINAL)["verdict"] == "accept" else None


def fill(prefix, stmts, judge_text, asks=(), max_asks=MAX_ASKS_PILOT, on_try=None, repair=None, passes=PASSES,
         run_lean=None, closer=None, final=None):
    """Prove the holes: Lean's closers on each hole's lemma first (`closer(lemma_prefix)` or lean_tier); then the lanes, breadth first: pass 1 gives
    every open hole one try from each ask in turn, pass 2 two tries (the second carrying Lean's error), so the easy
    holes are reached before the hard ones eat the budget (run 42705124685: holes 1-3 took 12 asks, 4-6 were never
    asked). `repair` is subgoals.prove_goal's hook, the free chain on a rejected lemma proof. `failed` (asked, not
    proved) and `unattempted` (the budget ran out first) stay apart (Codex 20261109T204513251417Z f6). closed_by maps
    a 1-based hole to "lean" or the index of the ask that proved it. When every hole closes the bodies are spliced
    under their `have` and the whole file is judged: `final` is that verdict, `accepted` the text on accept."""
    sk = sketch(prefix, stmts, final)
    top = prefix.count("\n") + 1
    hole_lines = subgoals.holes(sk, top)
    budget, plan = {"asks": 0, "max": max_asks}, {}
    log = {"holes": len(stmts), "closed_by": {}, "failed": [], "unattempted": [], "tries": [], "answered": 0}
    said, asked_here = {}, {}
    # the hook gets the lemma file's own prefix (header + statement, ending `:= by`), what toolscore.run_chain needs
    rep = (lambda body, stmt, out: repair(body, subgoals.lemma_file(prefix, stmt, "").rstrip("\n"), out)) if repair else None
    find = closer or (lambda lp: lean_tier(lp, judge_text, run_lean))
    for i, s in enumerate(stmts):
        n, stmt = i + 1, lemma_text(prefix, stmts, i)
        got = find(subgoals.lemma_file(prefix, stmt, "").rstrip("\n"))
        if got:
            plan[i], log["closed_by"][n] = [got], "lean"
        else:
            said[i], asked_here[i] = "", 0            # no single failing output to show a lane: the recipes ran apart
    # breadth first with rotation (Codex 20261109T220030181138Z f1: hole by hole, lane by lane spent three asks on hole 1
    # before hole 2): round r gives each open hole one try from lane (hole + r) mod lanes, every hole before any repeat
    for tries_max in passes:
        for r in range(len(asks)):
            for i in sorted(said):
                if i in plan:
                    continue
                n, stmt, who = i + 1, lemma_text(prefix, stmts, i), (i + r) % len(asks)
                body, tries = subgoals.prove_goal(prefix, stmt, sk, said[i], asks[who], judge_text, budget,
                                                  tries_max=tries_max, repair=rep)
                asked_here[i] += len(tries)
                for t in tries:
                    log["tries"].append({"hole": n, "by": who, "verdict": t["verdict"], "repaired": bool(t.get("repaired")),
                                         "reason": (t.get("reason") or "")[:200]})
                    if on_try:
                        on_try(n, who, stmt, t)
                if body:
                    plan[i], log["closed_by"][n] = body, who
    for i in sorted(said):
        log["answered"] += asked_here[i]
        if i not in plan:
            log["failed" if asked_here[i] or not asks else "unattempted"].append(i + 1)
    # asked = budget consumed (prove_goal counts an ask before the lane answers); unanswered = asks a parked or capped
    # lane, or the call cap, swallowed with no reply (Codex 20261109T213007122693Z f3)
    log["asked"] = budget["asks"]
    log["unanswered"] = budget["asks"] - log["answered"]
    return _assemble(log, sk, hole_lines, plan, len(stmts), judge_text)


def _assemble(log, sk, hole_lines, plan, n, judge_text):
    """Every hole closed: the bodies under their `have`, and the whole file judged. `final` is that verdict and is
    absent while a hole is open: not checked, never a kernel reject."""
    if len(plan) == n:
        final = subgoals._with_tactics(sk, {hole_lines[i]: plan[i] for i in plan})
        j = judge_text(final)
        log["final"], log["final_reason"] = j["verdict"], (j.get("reason") or "")[:300]
        if j["verdict"] == "accept":
            log["accepted"] = final
    return log


BLUEPRINTS = ROOT / "ledger" / "stall" / "blueprints"


def latest_gated(name, root=BLUEPRINTS, mark="", parent_sha=None):
    """The newest blueprint of a problem that passed the gate, or None. `mark` (".bp1", ".bp1_2") names a hole's own
    blueprint, which counts only when gated against `parent_sha`."""
    docs = [(p, json.loads(p.read_text())) for p in sorted(Path(root).glob(f"{name}{mark}-*.json"))]
    gated = [p for p, d in docs if d.get("ok") and (not mark or d.get("parent_sha") == parent_sha)]
    return gated[-1] if gated else None


def kaggle_work(man, n, read, find=latest_gated, rel=lambda path: str(path.relative_to(ROOT)), at=lambda r: ROOT / r):
    """A manifest's holes as prover-batch problems (prover.build's `problems`): every hole of each problem's latest
    gated blueprint as a file of its own, earlier statements as hypotheses, `n` samples each. All holes go, the ones
    Lean will close too: the workflow's push step runs no Lean, and the discarded samples are counted as cost at judge
    time. `guided` comes back on every answer (never `goal` or `arm`, which are the public paths) and pins what was
    exported: the blueprint and the target by hash, the hole, the samples planned. A manifest that continues an earlier
    batch lists the holes still open in `holes` (1-based): only those are exported, and every answer says which
    (`exported`), so the judge plans no samples for the rest.
    `subs` gives holes blueprints of their own (hole_target's lemma, decomposed by the guide and gated), and a hole
    of such a blueprint may have one in turn: each one's holes are exported too, marked with their `path` (the hole
    numbers from the problem's blueprint down), each with the lemma's binders and the earlier statements as
    hypotheses. A hole with a blueprint is never also sampled whole, and a blueprint whose statements would be named
    like its lemma's hypotheses is refused (next_stem)."""
    out, only = [], man.get("holes")
    for key in man["problems"]:
        tset, name = key.rsplit("/", 1)
        bp = find(name)
        if not bp:
            continue
        raw, text = bp.read_bytes(), read(tset, name)
        got = {"blueprint": hashlib.sha256(raw).hexdigest(), "target": hashlib.sha256(text.encode()).hexdigest()}
        want = {"blueprint": (man.get("blueprint") or {}).get("sha256"), "target": (man.get("target_sha256") or {}).get(key)}
        drift = [k for k in got if want[k] and want[k] != got[k]]
        if drift:                                   # a newer blueprint or an edited target is another experiment
            raise SystemExit(f"{man['id']}: {key}'s {' and '.join(drift)} is not what the manifest froze: nothing exported")
        stmts, prefix = json.loads(raw)["statements"], goal_closer.prefix_of(text)
        base = {"manifest": man["id"], "n": n, "blueprint": rel(bp), "blueprint_sha": got["blueprint"],
                "target_sha": got["target"], **({"exported": sorted(only)} if only is not None else {})}
        for i in range(len(stmts)):
            if only is not None and i + 1 not in only:
                continue
            out.append({"target_set": tset, "target": name, "n": n,
                        "statement": subgoals.lemma_file(prefix, lemma_text(prefix, stmts, i), "  sorry\n"),
                        "guided": {**base, "hole": i + 1, "holes": len(stmts)}})
        nodes = subs_of({"subs": (man.get("subs") or {}).get(key), "sub": (man.get("sub") or {}).get(key)})
        _export_subs(out, man, key, base, n, text, stmts, got["blueprint"], only, nodes, [], set(), STEM, at)
    return out


def _export_subs(out, man, key, base, n, text, stmts, sha, only, nodes, path, taken, stem, at):
    """kaggle_work's walk: `text` is the lemma this blueprint (`stmts`, hash `sha`, names `stem`) decomposes, `only` the
    holes of it sampled whole, `taken` the stems that already name a hypothesis of `text`."""
    tset, name = key.rsplit("/", 1)
    for sub in nodes:
        here = path + [sub["hole"]]
        sraw = at(sub["blueprint"]).read_bytes()
        sdoc = json.loads(sraw)
        hyps = taken | ({stem} if sub["hole"] > 1 else set())
        why = ("the manifest's `holes` still samples that hole whole" if only is None or sub["hole"] in only else
               "it is not the bytes the manifest froze" if hashlib.sha256(sraw).hexdigest() != sub["sha256"] else
               "it did not pass the gate" if not sdoc.get("ok") else
               "it was gated against another blueprint or hole" if (sdoc.get("parent_sha"), sdoc.get("hole")) != (sha, sub["hole"]) else
               f"its statements are named {stem_of(sdoc)}_1.. like its lemma's hypotheses" if stem_of(sdoc) in hyps
               else None)
        if why:
            raise SystemExit(f"{man['id']}: {key}'s blueprint for hole {'.'.join(map(str, here))}: {why}: nothing exported")
        sstmts, sstem = sdoc["statements"], stem_of(sdoc)
        stext = hole_target(text, stmts, sub["hole"], stem)
        sprefix, sonly = goal_closer.prefix_of(stext), sub.get("holes")
        for i in range(len(sstmts)):
            if sonly is not None and i + 1 not in sonly:
                continue
            out.append({"target_set": tset, "target": name, "n": n,
                        "statement": subgoals.lemma_file(sprefix, lemma_text(sprefix, sstmts, i, sstem), "  sorry\n"),
                        "guided": {**base, "hole": i + 1, "holes": len(sstmts), "path": here,
                                   "sub_blueprint": sub["blueprint"], "sub_blueprint_sha": sub["sha256"],
                                   **({"sub_exported": sorted(sonly)} if sonly is not None else {})}})
        _export_subs(out, man, key, base, n, stext, sstmts, sub["sha256"], sonly, subs_of(sub), here, hyps, sstem, at)


def fill_samples(prefix, stmts, samples, judge_text, *, proof_of, planned, repair=None, run_lean=None, closer=None,
                 carried=None, exported=None, final=None, stem=STEM):
    """fill for a prover batch: `samples` maps a 1-based hole to its answers' texts in sample order. Lean's closers on
    every hole first; then each sample of an open hole in order, through subgoals.try_body (the judge, then the free
    chain), the first accept closing the hole. asked = every sample generated; answered = samples read that held a
    complete proof; no_proof = read, none; unread = never needed (Lean closed the hole, or an earlier sample did).
    A hole with no samples is unattempted, and a hole short of `planned` makes the read `truncated`: the kernel stops
    at its GPU budget and still ends as complete (Codex 20261115T235234646209Z f2). A hole left open with a sample
    Lean did not finish judging (check.unfinished: our timeout, the memory limit) is `judge_unfinished`, not failed,
    and `judging_complete` is false for it or for an unfinished whole-proof check: neither is a finished read, and
    neither is generation cut short (Codex 20261116T000117894936Z f3).
    `carried` maps a 1-based hole to the tactic lines an earlier batch closed it with (2026-11-16: the first batch's
    two closed holes lived nowhere a second batch could reach). A carried body is never trusted: after Lean's own
    closers it is judged again on the hole's lemma, with no repair, and closes the hole (closed_by "carried") only on
    an accept; one that no longer judges is listed in `carry_failed` and the hole goes on to its samples. `exported`
    is the holes this batch sampled (None: all): the others have 0 planned. `bodies` holds every closed hole's lines
    with the sample that wrote them; it is for the caller's held file, never a ledger row."""
    carried, exported = carried or {}, set(exported) if exported is not None else None
    sk = sketch(prefix, stmts, final, stem)
    hole_lines = subgoals.holes(sk, prefix.count("\n") + 1)
    rep = (lambda body, stmt, out: repair(body, subgoals.lemma_file(prefix, stmt, "").rstrip("\n"), out)) if repair else None
    close = closer or (lambda lp: lean_tier(lp, judge_text, run_lean))
    plan = {}
    log = {"holes": len(stmts), "closed_by": {}, "failed": [], "unattempted": [], "tries": [], "answered": 0, "no_proof": 0,
           "planned": {}, "generated": {}, "judge_unfinished": [], "carry_failed": [], "bodies": {}}
    read = 0
    for i in range(len(stmts)):
        n, stmt, texts = i + 1, lemma_text(prefix, stmts, i, stem), samples.get(i + 1, [])
        log["planned"][n] = planned if exported is None or n in exported else 0
        log["generated"][n] = len(texts)
        got = close(subgoals.lemma_file(prefix, stmt, "").rstrip("\n"))
        if got:
            plan[i], log["closed_by"][n] = [got], "lean"
            log["bodies"][n] = {"lines": [got]}
            continue
        cut = False
        if n in carried:
            body = "".join(("  " + l if l.strip() else "") + "\n" for l in carried[n])
            lines, _, r = subgoals.try_body(prefix, stmt, body, judge_text, None)
            if lines:
                plan[i], log["closed_by"][n] = lines, "carried"
                log["bodies"][n] = {"lines": lines}
                continue
            cut = check.unfinished(str(r.get("reason") or ""))
            log["carry_failed"].append(n)
        for k, text in enumerate(texts):
            read += 1
            body = proof_of(text)
            if not body:
                log["no_proof"] += 1
                log["tries"].append({"hole": n, "sample": k, "verdict": "reject", "repaired": False,
                                     "reason": "no complete proof of the goal in the answer"})
                continue
            log["answered"] += 1
            lines, _, r = subgoals.try_body(prefix, stmt, body, judge_text, rep)
            cut = cut or (not lines and check.unfinished(str(r.get("reason") or "")))
            log["tries"].append({"hole": n, "sample": k, "verdict": r["verdict"], "repaired": bool(r.get("repaired")),
                                 "reason": (r.get("reason") or "")[:200]})
            if lines:
                plan[i], log["closed_by"][n] = lines, "sample"
                log["bodies"][n] = {"lines": lines, "sample": k, "repaired": bool(r.get("repaired"))}
                break
        if i not in plan:
            log["judge_unfinished" if cut else "failed" if texts else "unattempted"].append(n)
    log["asked"] = sum(log["generated"].values())
    log["unread"] = log["asked"] - read
    log["truncated"] = any(log["generated"][n] < log["planned"][n] for n in log["generated"])
    _assemble(log, sk, hole_lines, plan, len(stmts), judge_text)
    log["judging_complete"] = not log["judge_unfinished"] and not check.unfinished(log.get("final_reason", ""))
    return log


def guide_prompt(target_text, misses=(), stem=STEM):
    """The ask: propositions only. A guide's tactics are never read (statements() takes the JSON list and nothing else)."""
    near = "".join(f"- {m}\n" for m in misses)
    return (f"You are the guide for a Lean 4 (Mathlib) theorem the free models have not proved. Reply with ONE JSON list "
            f"of {MIN_STEPS} to {MAX_STEPS} Lean propositions (strings), in order, such that a proof of each, in the "
            "theorem's context, lets `first | assumption | omega | linarith | nlinarith | positivity | decide | norm_num | "
            "simp | aesop | grind | exact?` close the theorem from them. Rules: a proposition may name the theorem's "
            "variables and hypotheses and earlier statements as " + f"{stem}_1, {stem}_2" + "...; it must not contain any proof term, tactic "
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
    ap.add_argument("--hole", default="", help="the target is this hole (1-based) of the problem's latest gated blueprint; "
                    "1.2 is hole 2 of the latest gated blueprint of hole 1")
    args = ap.parse_args(argv)
    from proof_text import PROOF_SEP
    key = args.prompt or args.gate
    if not key:
        ap.error("--prompt or --gate")
    tset, name = key.rsplit("/", 1)
    target_text = (ROOT / "targets" / tset / f"{name}.lean").read_text()
    parent, stem = {}, STEM
    if args.hole:
        path = [int(h) for h in args.hole.split(".")]
        bp, taken = latest_gated(name), set()
        for d, hole in enumerate(path):
            raw = bp.read_bytes()
            doc = json.loads(raw)
            target_text = hole_target(target_text, doc["statements"], hole, stem_of(doc))
            taken |= {stem_of(doc)} if hole > 1 else set()
            parent = {"parent": str(bp.relative_to(ROOT)), "parent_sha": hashlib.sha256(raw).hexdigest(), "hole": hole,
                      "path": path[:d + 1]}
            if d + 1 < len(path):
                bp = latest_gated(name, mark=f".bp{'_'.join(map(str, path[:d + 1]))}", parent_sha=parent["parent_sha"])
                if not bp:
                    ap.error(f"no gated blueprint of hole {'.'.join(map(str, path[:d + 1]))} against the latest one above it")
        stem = stem_of(doc)
        while stem in taken:
            stem = next_stem(stem)
        parent["stem"] = stem
    prefix = target_text[:PROOF_SEP.search(target_text).end()]
    if args.prompt:
        import relay
        d = relay.fetch_dossier(tset, name)
        misses = [f"{m.get('backend')}: {m.get('failure_kind')}" for m in (d.get("near_misses") or [])[:3] if m.get("failure_kind")]
        print(guide_prompt(target_text, misses, stem))
        return 0
    import lean_tools
    stmts = statements(Path(args.reply).read_text())
    g = gate(prefix, stmts, lean_tools.run_lean, lean_tools.judge_text, stem)
    ts = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    BLUEPRINTS.mkdir(parents=True, exist_ok=True)
    out = BLUEPRINTS / (f"{name}.bp{args.hole.replace('.', '_')}-{ts}.json" if args.hole else f"{name}-{ts}.json")
    out.write_text(json.dumps({"ts": ts, "target_set": tset, "target": name, **parent, "guide": args.guide, "statements": stmts,
                               **g}, indent=1, ensure_ascii=False) + "\n")
    print(("PASS" if g["ok"] else "REJECT") + f" {key}: {len(stmts)} statements; " + ("; ".join(g["why"]) or "wellformed")
          + f"\n  {out.relative_to(ROOT)}")
    return 0 if g["ok"] else 1


if __name__ == "__main__":
    sys.exit(main())
