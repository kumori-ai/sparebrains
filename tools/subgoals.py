"""A rejected proof, taken apart the way APOLLO does it (arXiv 2505.05758), and only what is still open
goes back to the model that wrote it (DECISIONS.md 2026-10-08, "the loop, not the hole filler").

    0. fix       the form first (tools/fixer.py: a doubled `by`, layout, Lean 3, invented names)
    1. sorrify   every step Lean rejected becomes `sorry`; the steps it accepted stay
    2. automate  each hole gets Lean's own closers (omega, linarith, ..., exact?) in one run
    3. goals     each hole still open is printed by `extract_goal` as a standalone lemma
    4. ask       the same model proves that lemma, with what Lean said; one retry with the new error
    5. splice    a proved lemma's tactics go into its hole; the whole file is judged again

Lean stays the only judge: nothing here counts until check.judge accepts the final file. Every Lean
and model call goes through callables the caller passes in (`run_lean`, `judge_text`, `ask`), so the
relay keeps its sandbox, its call cap and its ledger, and the tests need neither Lean nor a model.

Measured in the literature, not here yet: the loop (a model re-trying with Lean's error, per subgoal)
took general-purpose models (o3-mini, o4-mini) from 3-7% to over 40% on miniF2F under APOLLO (its abstract); hole filling alone added 0.4 to 6
points. Each try's `tools.subgoals` row in the ledger is how this repo measures its own number.
"""
import re

from proof_text import extract_proof

# Every alternative closes the goal or fails, so a hole Lean could not close always errors on its own line.
# `aesop` alone does not: it warns "failed to prove the goal" and leaves the goal open (2026-10-08).
AUTO_TACTICS = ["omega", "linarith", "nlinarith", "positivity", "decide", "(norm_num; done)", "(simp; done)",
                "(aesop; done)", "exact?"]
AUTO = "first | " + " | ".join(AUTO_TACTICS)
MAX_ROUNDS = 4                    # sorrify passes before giving up on a proof's shape
MAX_HOLES = 3                     # open holes worth asking about; more and the proof was not close
MAX_ASKS = 4                      # model calls per repair, across holes
MSG = re.compile(r"^[^\s:]+\.lean:(\d+):(\d+): (error|warning|info)[^:]*: ?(.*)$")
HOLE = re.compile(r"^(\s*)(· |all_goals )?sorry\s*$")     # `all_goals sorry`: several cases left at once
NEVER_RUN = "this tactic is never executed"
TRY_THIS = re.compile(r"Try this:[ \t]*\n?[ \t]*(?:\[\w+\][ \t]*)?([^\n]+)")
DECL = re.compile(r"^(?:theorem|lemma)\s", re.M)
UNKNOWN = re.compile(r"[Uu]nknown (?:identifier|constant) [`']([^`'\s]+)[`']")
SUBGOAL = ("A proof of a Lean 4 theorem is almost done. Lean accepted every other step; this one is still "
           "open, and Lean's automation (omega, linarith, nlinarith, positivity, decide, norm_num, simp, "
           "aesop, exact?) could not close it. Prove it as a standalone lemma.\n\n"
           "Reply with the whole lemma in one ```lean block: exactly the statement below, then `:= by` and "
           "tactics. No `sorry`, no other declarations. Lean 4 and current mathlib names only.\n\n")


def indent(line):
    return len(line) - len(line.lstrip())


def messages(out):
    """[(line, col, kind, text)] from Lean's output; a message runs until the next positioned one."""
    found = []
    for raw in (out or "").splitlines():
        m = MSG.match(raw)
        if m:
            found.append([int(m.group(1)), int(m.group(2)), m.group(3), m.group(4)])
        elif found:
            found[-1][3] += "\n" + raw
    return [tuple(f) for f in found]


def errors(out):
    return [(l, c, t) for l, c, k, t in messages(out) if k == "error"]


def _block_end(lines, i, rest=False):
    """Index past line i's block: the lines after it indented deeper (blank lines included). With
    `rest`, its later siblings too: in a tactic sequence nothing after a failed step can be trusted."""
    j = i + 1
    while j < len(lines) and (not lines[j].strip() or indent(lines[j]) > indent(lines[i])
                              or (rest and indent(lines[j]) == indent(lines[i]))):
        j += 1
    return j


def sorrify(text, errs, top_line):
    """The text with every failing step replaced by `sorry`, or None when nothing changed. `top_line` is
    the 1-based line of the theorem's `:= by`; an error there (goals left at the end) appends a hole."""
    lines = text.split("\n")
    changed = False
    for line_no, col, msg in sorted(set(errs), key=lambda e: -e[0]):
        i = line_no - 1
        if line_no <= top_line:
            body = [l for l in lines[top_line:] if l.strip()]
            if body and not HOLE.match(body[-1]):
                base = " " * indent(body[0])
                while lines and not lines[-1].strip():
                    lines.pop()
                many = msg.count("\ncase ") > 1         # `interval_cases k <;> ...` left four cases (435, 2026-10-08)
                lines.append(base + ("all_goals sorry" if many else "sorry"))
                changed = True
            continue
        if i >= len(lines):
            continue
        if msg.lower().startswith("no goals"):           # the goal closed earlier: this step and every later
            del lines[i:_block_end(lines, i, rest=True)]  # sibling go (Lean names only the first; 293, 2026-10-08)
            changed = True
            continue
        if HOLE.match(lines[i]):
            continue
        line, ind = lines[i], " " * indent(lines[i])
        bullet = "· " if line.strip().startswith("·") else ""
        end = _block_end(lines, i, rest=not bullet)
        by = line.rstrip().endswith(" by") or line.rstrip() == "by"
        at_by = line.rfind(" by") if " by" in line else -1
        if by and col >= at_by:                          # `have h : X := by` whose proof failed: keep the claim
            new = [line, ind + "  sorry"]
            end = _block_end(lines, i)
        elif at_by > 0 and col > at_by and not by:       # `_ = x := by ring`: Lean points at the `by` or a tactic
            new = [line[:at_by + 3] + "\n" + ind + "  sorry"]
            end = _block_end(lines, i)
        else:
            new = [ind + bullet + "sorry"]
        if lines[i:end] != new:
            lines[i:end] = "\n".join(new).split("\n")
            changed = True
    return "\n".join(lines) if changed else None


def normalize_holes(text, top_line):
    """A model's own inline holes on their own lines: `... := by sorry` and `... := sorry` become a
    `by` block holding one `sorry`, so every hole is a line `ind sorry` (or `ind · sorry`)."""
    lines = text.split("\n")
    out = lines[:top_line]
    for line in lines[top_line:]:
        m = re.match(r"^(.*\S)\s*:=\s*(?:by\s+)?sorry\s*$", line)
        if m and not HOLE.match(line):
            out += [m.group(1) + " := by", " " * (indent(line) + 2) + "sorry"]
        else:
            out.append(re.sub(r"\bby\s+sorry\s*$", "by\n" + " " * (indent(line) + 2) + "sorry", line)
                       if re.search(r"\bby\s+sorry\s*$", line) else line)
    return "\n".join(out)


def holes(text, top_line):
    """Line indexes (0-based) of the hole lines in the proof. None when a `sorry` sits anywhere else."""
    lines = text.split("\n")
    found = [i for i in range(top_line, len(lines)) if HOLE.match(lines[i])]
    stray = sum(len(re.findall(r"\bsorry\b", l)) for l in lines[top_line:]) - len(found)
    return None if stray else found


def kept_steps(text, top_line):
    """How many proof lines are real steps, not holes: 0 means the proof was thrown away whole."""
    return sum(1 for l in text.split("\n")[top_line:] if l.strip() and not HOLE.match(l))


def _with_tactics(text, plan):
    """The text with each hole line i replaced by the tactic lines plan[i] (indented to the hole)."""
    lines = text.split("\n")
    for i in sorted(plan, reverse=True):
        m = HOLE.match(lines[i])
        ind, bullet = m.group(1), m.group(2) or ""
        body = plan[i]
        if bullet == "all_goals ":                       # one line, every case: all_goals (a; b; c)
            lines[i] = ind + "all_goals (" + "; ".join(body) + ")"
            continue
        head = ind + bullet + body[0]
        inner = ind + ("  " if bullet else "")
        lines[i:i + 1] = [head] + [inner + b for b in body[1:]]
    return "\n".join(lines)


def _segments(out):
    """Lean's output split at the `sb_auto N` / `sb_hole N` trace markers: {(kind, N): text after it}."""
    segs, key = {}, None
    for raw in (out or "").splitlines():
        m = re.match(r"^(sb_auto|sb_hole) (\d+)\s*$", raw.strip())
        if m:
            key = (m.group(1), int(m.group(2)))
            segs[key] = ""
        elif key:
            segs[key] += raw + "\n"
    return segs


def _executed(line_text, line_no, msgs):
    """Which AUTO alternative ran on this line: the last one Lean did not call never-executed."""
    never = {c for l, c, k, t in msgs if l == line_no and NEVER_RUN in t}
    if not never:
        return None
    start, ran = line_text.index("first | ") + len("first | "), None
    for tac in AUTO_TACTICS:
        col = line_text.index(tac, start)
        if col not in never:
            ran = tac
        start = col + len(tac)
    return ran


def automate_and_goals(text, top_line, run_lean):
    """Two Lean runs. The first gives every hole AUTO and learns which ones it closes; the second keeps
    AUTO on those (to learn which closer ran, so the proof is concrete) and prints the rest with
    `extract_goal`. Returns (text with closed holes filled, {hole line: lemma statement}, log)."""
    hs = holes(text, top_line)
    trial = _with_tactics(text, {i: [AUTO] for i in hs})
    out1, _ = run_lean(trial)
    failed_lines = {l for l, _, _ in errors(out1)}
    # a hole's AUTO line keeps its line number in `trial`, because AUTO is one line
    closed = [i for i in hs if (i + 1) not in failed_lines]
    still = [i for i in hs if i not in closed]
    plan, n = {}, 0
    for i in hs:
        n += 1
        if i in closed:
            plan[i] = [f'trace "sb_auto {n}"', AUTO]
        else:
            plan[i] = [f'trace "sb_hole {n}"', "extract_goal", "sorry"]
    probe = _with_tactics(text, plan)
    out2, _ = run_lean(probe)
    segs, msgs = _segments(out2), messages(out2)
    probe_lines = probe.split("\n")
    fill, goals, n = {}, {}, 0
    for i in hs:
        n += 1
        if HOLE.match(text.split("\n")[i]).group(2) == "all_goals ":
            if i in closed:                              # each case may need a different closer: keep `first`
                fill[i] = [AUTO]
            continue                                     # an open one stays `all_goals sorry`; never asked
        if i in closed:
            seg = segs.get(("sb_auto", n), "")
            tt = TRY_THIS.search(seg)
            line_no = next((k + 1 for k, l in enumerate(probe_lines) if l.strip().endswith(AUTO)
                            and probe_lines[k - 1].strip().endswith(f'trace "sb_auto {n}"')), None)
            ran = tt.group(1).strip() if tt else (_executed(probe_lines[line_no - 1], line_no, msgs) if line_no else None)
            if ran and ran.startswith("(") and ran.endswith("; done)"):
                ran = ran[1:-len("; done)")]
            fill[i] = [ran if ran and ran != "exact?" else AUTO]
        else:
            stmt = segs.get(("sb_hole", n), "")
            m = re.search(r"^theorem\s+\S+(.*?):=\s*sorry", stmt, re.S | re.M)
            if m:
                goals[i] = "theorem sb_goal" + m.group(1).rstrip() + " := by"
    log = {"holes": len(hs), "closed_by_lean": len(closed), "closers": [fill[i][0] for i in closed], "open": len(still)}
    return _with_tactics(text, fill), goals, log


def lemma_file(prefix, statement, body):
    header = prefix[:DECL.search(prefix).start()]
    return header + statement + "\n" + body


def real_names(said, names):
    """Lines naming real mathlib lemmas for each library-style name Lean did not know, or ''."""
    if not names:
        return ""
    out = []
    for u in dict.fromkeys(UNKNOWN.findall(said or "")):
        if "." in u and u[0].isupper():
            try:
                close = [n for n in names(u) if n != u][:4]
            except Exception:
                close = []
            out.append(f"- `{u}` does not exist" + (": real names close to it: " + ", ".join(f"`{n}`" for n in close)
                                                    if close else "; nothing close in mathlib"))
    return ("\nNames Lean did not know, and real mathlib names close to them:\n" + "\n".join(out) + "\n") if out else ""


def prove_goal(prefix, statement, sketch, lean_said, ask, judge_text, budget, names=None):
    """(tactic lines or None, [tries]). The same model, up to two asks: the second carries Lean's error and
    real names for any it invented (the first live ask, 2026-10-08: `Nat.coprime_pow_eq_pow_iff`)."""
    tries, last = [], None
    for _ in range(2):
        if budget["asks"] >= budget.get("max", MAX_ASKS):
            break
        prompt = (SUBGOAL + "```lean\n" + statement + "\n```\n\nWhere it sits (the open step is `sorry`):\n```lean\n"
                  + sketch[-3000:] + "\n```\n\nWhat Lean said about the step that was there:\n```\n" + lean_said[-1500:] + "\n```\n")
        prompt += real_names(lean_said, names) if not last else ""
        if last:
            prompt += ("\nYour previous proof of this lemma:\n```lean\n" + last[0][-2500:] + "\n```\nLean said:\n```\n"
                       + last[1][-1500:] + "\n```\n" + real_names(last[1], names) + "Fix it.\n")
        budget["asks"] += 1
        reply = ask(prompt)
        if reply is None:                                # the call cap, a parked lane, an error: stop asking
            break
        body = extract_proof(re.sub(r"\blemma\s+sb_goal\b", "theorem sb_goal", reply), "sb_goal")
        if not body:
            tries.append({"prompt": prompt, "reply": reply, "proof": None, "verdict": "reject",
                          "reason": "no proof extracted from reply", "lean_output": ""})
            last = (reply, "no proof could be read from the reply")
            continue
        r = judge_text(lemma_file(prefix, statement, body))
        tries.append({"prompt": prompt, "reply": reply, "proof": body, **r})
        if r["verdict"] == "accept":
            lines = [l for l in body.rstrip("\n").split("\n")]
            base = min(indent(l) for l in lines if l.strip())
            return [l[base:] if l.strip() else "" for l in lines], tries
        last = (body, r.get("output") or r.get("reason") or "")
    return None, tries


def repair(candidate, prefix, lean_out, *, ask, run_lean, judge_text, on_lemma=None, fix=None, names=None):
    """APOLLO's loop on one rejected candidate. Returns a summary dict; `accepted` holds the final file
    when the kernel accepted it. `on_lemma(statement, try)` is called for every lemma ask, for the ledger.
    `fix(proof, lean_output)` -> (proof, [passes]) repairs form first; a parse error leaves Lean nothing
    to take apart (the first replay on real near misses, 2026-10-08: a doubled `by` hid a whole proof)."""
    top = prefix.count("\n") + 1
    said = lean_out or ""
    text, log = candidate, {"rounds": 0, "asked": 0, "lemmas_proved": 0}
    if fix:
        fixed, applied = fix(candidate[len(prefix):].lstrip("\n"), said)
        if applied:
            text = prefix + "\n" + fixed
            r = judge_text(text)
            said, log["fixes"] = r.get("output") or "", applied
            if r["verdict"] == "accept":
                return {**log, "accepted": text, "lean_output": said, "final": "accept"}
    text = normalize_holes(text, top)
    for _ in range(MAX_ROUNDS):
        errs = errors(said)
        if not errs:
            break
        nxt = sorrify(text, errs, top)
        log["rounds"] += 1
        if nxt is None:
            log["stopped"] = "Lean's errors could not be turned into holes"
            return log
        text = nxt
        r = judge_text(text)
        said = r.get("output") or ""
        if r["verdict"] == "wellformed":
            break
        if r["verdict"] == "accept":                    # cannot happen with a hole, but never throw away an accept
            return {**log, "accepted": text}
    else:
        log["stopped"] = f"still errors after {MAX_ROUNDS} rounds of holes"
        return log
    hs = holes(text, top)
    if hs is None:
        log["stopped"] = "a `sorry` in the middle of a line"
        return log
    if not hs:
        log["stopped"] = "Lean reported no failing step"
        return log
    if not kept_steps(text, top):
        log["stopped"] = "no step of the proof survived"
        return log
    if len(hs) > 2 * MAX_HOLES:
        log["stopped"] = f"{len(hs)} failing steps: not close"
        return log
    text, goals, auto_log = automate_and_goals(text, top, run_lean)
    log.update(auto_log)
    if ask is None and goals:                           # the fixer's pass: no model, so open steps stay open
        log["stopped"] = f"{len(goals)} step(s) left for a model"
        log["sketch"], log["goals"] = text, list(goals.values())
        return log
    return prove_open(text, goals, prefix, [ask], judge_text, on_lemma=on_lemma, names=names, said=lean_out, log=log)


def prove_sketch(sketch, prefix, *, asks, run_lean, judge_text, on_lemma=None, names=None, said="", max_asks=18):
    """The lemma queue (DECISIONS.md 2026-10-08): a stored sketch's open steps, each tried by every ask in
    `asks` in turn (the strongest live lanes first) until one proves it; then splice and judge."""
    top = prefix.count("\n") + 1
    hs = holes(sketch, top)
    if not hs:
        return {"stopped": "no hole in the sketch"}
    text, goals, log = automate_and_goals(sketch, top, run_lean)
    log.update(rounds=0, asked=0, lemmas_proved=0)
    return prove_open(text, goals, prefix, asks, judge_text, on_lemma=on_lemma, names=names, said=said, log=log,
                      max_asks=max_asks)


def prove_open(text, goals, prefix, asks, judge_text, *, on_lemma=None, names=None, said="", log=None, max_asks=MAX_ASKS):
    """Each open step to the asks in turn, a proved one spliced into its hole, the whole file judged."""
    log = log if log is not None else {}
    top = prefix.count("\n") + 1
    if len(goals) > MAX_HOLES:
        log["stopped"] = f"{len(goals)} steps still open after Lean's automation"
        log["sketch"] = text
        return log
    budget, plan, provers = {"asks": 0, "max": max_asks}, {}, []
    for i, statement in goals.items():
        for who, ask in enumerate(asks):
            body, tries = prove_goal(prefix, statement, text, said or "", ask, judge_text, budget, names)
            for t in tries:
                if on_lemma:
                    on_lemma(statement, {**t, "by": who})
            if body:
                plan[i] = body
                provers.append(who)
                break
        if i not in plan:                                # one unproved step leaves the proof open: stop spending
            break
    log["asked"] = budget["asks"]
    log["provers"] = provers
    log["lemmas_proved"] = len(plan)
    log["goals"] = list(goals.values())
    open_holes = holes(text, top) or []
    if len(plan) < len(open_holes):
        log["stopped"] = f"{len(open_holes) - len(plan)} of {len(open_holes)} open steps unproved"
        log["sketch"] = _with_tactics(text, plan)
        return log
    final = _with_tactics(text, plan)
    r = judge_text(final)
    log["final"] = r["verdict"]
    if r["verdict"] == "accept":
        log["accepted"] = final
        log["lean_output"] = r.get("output") or ""
    else:
        log["stopped"] = "the spliced proof did not check: " + (r.get("reason") or "")[:200]
        log["sketch"] = final
    return log
