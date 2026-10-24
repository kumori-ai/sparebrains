"""What part of a model's reply is handed to Lean: the proof after `:= by`, recovered from a fenced
file, a fenced tactic block, or a bare `by ...` reply, with its layout made consistent. Lean stays
the only judge; this only decides which text it is shown."""
import re

PROOF_SEP = re.compile(r":=\s*by\b")
FENCE = re.compile(r"```(?:lean4?)?\s*\n(.*?)```", re.S)
BARE_BY = re.compile(r"^by\b(.*)$", re.S)
LEAN3_BEGIN = re.compile(r":=\s*begin\b")
MAX_RECOVER_LINES = 200          # a Lean 3 body longer than this is cut there and treated as truncated
REPEAT_RUN = 3                   # this many identical tactic lines in a row are kept once
OPENS_BLOCK = re.compile(r"(:=\s*by|\bby|:=|=>|\bwith|\bdo|·|\bfrom|<;>|\bthen|\belse)\s*$")


def align_tactics(lines):
    """A reply that puts its first tactic at one indent and every later one deeper ("intro h" then
    "  have ...") is a layout slip: Lean reads the deeper lines as a continuation and stops with
    "unexpected token". Three of mil_c05_s01_ex03's five closest misses had it (2026-10-06). Pull the
    rest back to the first line's indent, unless the first line opens a block the rest belongs to."""
    body = [l for l in lines if l.strip()]
    if len(body) < 2:
        return lines
    first = len(body[0]) - len(body[0].lstrip())
    rest = min(len(l) - len(l.lstrip()) for l in body[1:])
    if rest <= first or OPENS_BLOCK.search(body[0].rstrip()):
        return lines
    cut, start = rest - first, lines.index(body[0])
    return lines[:start + 1] + [l[cut:] if l.strip() and l[:cut].strip() == "" else l for l in lines[start + 1:]]


def extract_proof(reply, name):
    blocks = FENCE.findall(reply)
    text = max(blocks, key=len) if blocks else reply
    i = text.find(f"theorem {name}")
    if i >= 0:
        sep = PROOF_SEP.search(text, i)
        if not sep:
            return None
        proof = text[sep.end():]
    elif not blocks or "theorem " in text or "import " in text:
        # A common otherwise-valid answer is a bare `by ...` tactic block without a Markdown
        # fence. It is safe to recover this narrow shape: Lean still receives the exact original
        # statement and remains the only judge. Do not try to mine a `by` from prose.
        bare = BARE_BY.match(text.strip())
        if not bare:
            return None                              # prose, a different theorem, or an echoed preamble
        proof = bare.group(1)
    else:
        # A fenced bare tactic block. If it opens with its own `by`, drop it: the target already ends
        # in `:= by`, and a second one made Lean stop at "unexpected token 'by'" before reading any
        # math (74 rejects on 50 problems to 2026-10-08, the closest misses on #7 and #10 among them).
        bare = BARE_BY.match(text.strip())
        proof = bare.group(1) if bare else text
    lines = align_tactics(proof.strip("\n").splitlines())
    if not any(l.strip() for l in lines):
        return None
    indent = min(len(l) - len(l.lstrip()) for l in lines if l.strip())
    if indent == 0:
        lines = ["  " + l if l.strip() else l for l in lines]
    return "\n".join(lines).rstrip() + "\n"


def _braces(line):
    code = line.split("--")[0]
    return code.count("{") - code.count("}")


def recover_lean3(reply, name):
    """(body, transformations) for a Lean 3 proof of `name` (`theorem name ... := begin ... end`), which
    extract_proof cannot read because it looks for `:= by`; None when the reply holds no such proof. groq-allam wrote
    510 of its 829 unextracted replies this way (2026-10-24), many cut off mid-loop by the output cap. Recorded, never
    silent: lean3_begin (always), repetition_cut (a run of REPEAT_RUN+ identical tactic lines kept once),
    cut_at_max_lines, truncated_closed (no closing `end`: the last line dropped if it is broken, the block closed),
    unclosed_braces (`{` blocks left open before a closing `end`). The body keeps begin/end so the fixer's lean3 pass
    converts it; Lean stays the only judge."""
    blocks = [b for b in FENCE.findall(reply) if f"theorem {name}" in b]
    text = max(blocks, key=len) if blocks else reply
    i = text.find(f"theorem {name}")
    if i < 0:
        return None
    m = LEAN3_BEGIN.search(text, i)
    if not m or PROOF_SEP.search(text, i, m.start()) or "theorem " in text[i + 8:m.start()]:
        return None
    how, body, depth, closed = ["lean3_begin"], [], 0, False
    for line in text[m.end():].splitlines():
        s = line.strip()
        if s.startswith("```"):
            break
        if s in ("end", "end,"):
            if depth == 0:
                closed = True
                break
            depth -= 1
        elif s and line == line.lstrip() and not s.startswith(("--", "{", "}", "·")):
            break                                          # prose after the proof, unindented
        if re.search(r"\bbegin\b", s):
            depth += 1
        body.append(line)
    while body and not body[0].strip():
        body.pop(0)
    kept, i = [], 0
    while i < len(body):                                   # a run of identical tactic lines is a loop, not a proof
        j = i
        while j + 1 < len(body) and body[j + 1].strip() == body[i].strip():
            j += 1
        tactic = body[i].strip() and not body[i].strip().startswith("--")
        if tactic and j - i + 1 >= REPEAT_RUN:
            kept.append(body[i])
            if "repetition_cut" not in how:
                how.append("repetition_cut")
        else:
            kept += body[i:j + 1]
        i = j + 1
    if len(kept) > MAX_RECOVER_LINES:
        kept, closed = kept[:MAX_RECOVER_LINES], False
        how.append("cut_at_max_lines")
    if not closed:
        while kept and not kept[-1].strip():
            kept.pop()
        last = kept[-1].strip() if kept else ""
        if kept and (_braces(last) > 0 or "[" in last and "]" not in last
                     or not last.endswith((",", "}", "},", "end"))):
            kept.pop()                                     # cut off mid-tactic by the output cap
        how.append("truncated_closed")
    open_ = sum(_braces(l) for l in kept)
    if open_ > 0:
        kept += ["  }"] * open_
        if closed:
            how.append("unclosed_braces")
    if not any(l.strip() for l in kept):
        return None
    return "begin\n" + "\n".join(kept) + "\nend\n", how
