"""The fixer (issue #3): repairs a failed proof's form, with no model, and leaves the mathematics alone.
The kernel then judges the repaired proof like any other; nothing here decides what is true.

Three passes, each recorded by name when it changes something:
  layout  - the first tactic shallower than the rest (proof_text.align_tactics)
  lean3   - Lean 3 syntax a model wrote from old training data: begin/end, commas between tactics,
            `λ x,`, `assume`, `cases h with a b`, lowercase namespaces (nat.succ -> Nat.succ)
  names   - each name Lean called unknown, swapped for the closest REAL mathlib name, from an index
            built out of mathlib's own sources on the runner (nothing is guessed without the index)
61% of rejects on unsolved problems failed on form, not mathematics (2026-10-06).
"""
import difflib, re
from collections import defaultdict
from pathlib import Path

from proof_text import align_tactics

UNKNOWN = re.compile(r"[Uu]nknown (?:identifier|constant) [`']([^`'\s]+)[`']")
_NAMESPACES = ("nat", "int", "real", "rat", "complex", "finset", "set", "list", "polynomial", "zmod", "multiset")
_LOWER_NS = re.compile(r"\b(" + "|".join(_NAMESPACES) + r")\.(?=[a-z_])")
_DECL = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:(?:protected|private|noncomputable|nonrec)\s+)*"
                   r"(?:theorem|lemma|def|abbrev)\s+([^\s:({\[]+)", re.M)
_NS_OPEN = re.compile(r"^\s*namespace\s+(\S+)", re.M)


def _open_brackets(line):
    return sum(line.count(c) for c in "([{⟨") - sum(line.count(c) for c in ")]}⟩")


def looks_lean3(lines):
    """Lean 3, not Lean 4 with an odd token: wrapped in begin/end, or most tactic lines end in a comma.
    A Lean 4 proof legitimately ends lines in commas inside lists (`simp only [a,` / `b]`), and the
    failure label lean3_syntax also catches Lean 4 with a stray `...` (2026-10-07 preview)."""
    code = [l.strip() for l in lines if l.strip() and not l.strip().startswith("--")]
    if not code:
        return False
    if code[0] == "begin" and code[-1] == "end":
        return True
    return sum(c.endswith(",") for c in code) >= 0.5 * len(code)


def lean3_to_4(proof):
    lines = proof.rstrip("\n").splitlines()
    if not looks_lean3(lines):                                           # names may still need fixing
        return _LOWER_NS.sub(lambda m: m.group(1).capitalize() + ".", proof.rstrip("\n")) + "\n"
    body = [l for l in lines if l.strip()]
    if body and body[0].strip() == "begin" and body[-1].strip() == "end":
        first, last = lines.index(body[0]), len(lines) - 1 - lines[::-1].index(body[-1])
        lines = lines[first + 1:last]
    out = []
    for l in lines:
        if _open_brackets(l) <= 0:                                       # a separator, not a list's comma
            l = re.sub(r",\s*$", "", l)
        l = re.sub(r"λ\s*([^,=>]+?)\s*,", r"fun \1 =>", l)
        l = re.sub(r"\bassume\b", "intro", l)
        m = re.match(r"^(\s*)cases\s+(\S+)\s+with\s+(.+?)\s*$", l)
        if m:
            l = f"{m.group(1)}obtain ⟨{', '.join(m.group(3).split())}⟩ := {m.group(2)}"
        l = _LOWER_NS.sub(lambda m: m.group(1).capitalize() + ".", l)
        out.append(l)
    return "\n".join(out) + "\n"


def mathlib_index(root):
    """Every theorem/lemma/def name in mathlib's sources under `root`, qualified by its namespace when
    the file opens one (a single namespace per declaration line; nested ones are approximated)."""
    names = set()
    for f in Path(root).glob("**/*.lean"):
        text = f.read_text(errors="ignore")
        ns = _NS_OPEN.findall(text)
        for d in _DECL.findall(text):
            names.add(d)
            for n in ns[:3]:
                names.add(f"{n}.{d}")
    return names


def closest_name(unknown, index, by_last=None):
    """A real name for `unknown`, or None: the same final component under another namespace first,
    then a close spelling within the same top namespace."""
    by_last = by_last or _by_last(index)
    last = unknown.split(".")[-1]
    same = sorted(n for n in by_last.get(last, ()) if n != unknown)
    if same:
        root = unknown.split(".")[0]
        same.sort(key=lambda n: (n.split(".")[0] != root, len(n)))
        return same[0]
    root = unknown.split(".")[0] + "."
    pool = [n for n in index if n.startswith(root)] if "." in unknown else []
    got = difflib.get_close_matches(unknown, pool, n=1, cutoff=0.85)
    return got[0] if got else None


def _by_last(index):
    d = defaultdict(set)
    for n in index:
        d[n.split(".")[-1]].add(n)
    return d


def fix(proof, lean_output="", index=None, by_last=None):
    """(repaired proof, [pass names that changed it]). Unchanged proof and [] when nothing applies."""
    applied, p = [], proof.rstrip("\n") + "\n"
    q = "\n".join(align_tactics(p.rstrip("\n").splitlines())) + "\n"
    if q != p:
        applied.append("layout")
        p = q
    q = lean3_to_4(p)
    if q != p:
        applied.append("lean3")
        p = q
    if index:
        swaps = {}
        for u in dict.fromkeys(UNKNOWN.findall(lean_output or "")):
            if "." in u and u[0].isupper():                              # library-style names only
                real = closest_name(u, index, by_last)
                if real:
                    swaps[u] = real
        q = p
        for u, real in swaps.items():
            q = re.sub(r"(?<![\w.])" + re.escape(u) + r"(?![\w'])", real, q)
        if q != p:
            applied.append("names")
            p = q
    return p, applied
