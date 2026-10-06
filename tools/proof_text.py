"""What part of a model's reply is handed to Lean: the proof after `:= by`, recovered from a fenced
file, a fenced tactic block, or a bare `by ...` reply, with its layout made consistent. Lean stays
the only judge; this only decides which text it is shown."""
import re

PROOF_SEP = re.compile(r":=\s*by\b")
FENCE = re.compile(r"```(?:lean4?)?\s*\n(.*?)```", re.S)
BARE_BY = re.compile(r"^by\b(.*)$", re.S)
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
        proof = text                                 # a fenced bare tactic block
    lines = align_tactics(proof.strip("\n").splitlines())
    if not any(l.strip() for l in lines):
        return None
    indent = min(len(l) - len(l.lstrip()) for l in lines if l.strip())
    if indent == 0:
        lines = ["  " + l if l.strip() else l for l in lines]
    return "\n".join(lines).rstrip() + "\n"
