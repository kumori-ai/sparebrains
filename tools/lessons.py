"""The lessons station (DECISIONS.md 2026-10-28; Andy's school: the lanes that solved a problem teach the ones that
have not, with nothing trained). A lane asked to prove a theorem is shown the k nearest solved theorems by statement
and their kernel-accepted proofs, read from verified/. Retrieval is the one known lift for a small prover that needs
no weights: ReProver, arXiv 2306.15626 (2023), 47.6% to 51.2% with premise retrieval. Never the problem's own proof,
never a proof of the same theorem (by a name-free declaration sha), so a solved problem in a head-to-head is taught only by others.

    python3 tools/lessons.py minif2f/test/aime_1983_p1 --k 3      # print the block a lane would see
"""
import argparse, hashlib, math, re, sys
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT / "tools")]
from proof_text import PROOF_SEP

K, PROOF_CAP = 3, 2500
TOKEN = re.compile(r"[A-Za-z_][A-Za-z0-9_'.₀-₉]*|[∀∃∑∏√∣≤≥≠∈∉⊆∧∨¬→↔ℕℤℚℝℂ%^*/+\-]")
STOP = {"theorem", "lemma", "by", "import", "Mathlib", "open", "scoped", "Nat", "Real", "sorry"}


def statement_of(text):
    m = PROOF_SEP.search(text)
    return text[:m.end()] if m else text


def declaration(statement):
    """The theorem without its name or docstring, whitespace normalized: what makes two targets the same theorem
    (Codex f3, 2026-10-28: a renamed copy of a solved theorem is the problem, not a lesson)."""
    s = re.sub(r"/--.*?-/", " ", statement, flags=re.S)
    s = s[s.find("theorem"):] if "theorem" in s else s
    s = re.sub(r"^(theorem|lemma)\s+\S+", "theorem _", s, count=1)
    return re.sub(r"\s+", " ", s).strip()


def tokens(statement):
    return [t for t in TOKEN.findall(declaration(statement)) if t not in STOP and t != "_" and not re.fullmatch(r"h[₀-₉0-9']*", t)]


def index(targets=ROOT / "targets", verified=ROOT / "verified"):
    """[{key, sha, tokens, statement, proof}] for every target with a kernel-accepted proof: the shortest proof wins
    (a shorter lesson is a clearer one). A target dir is any dir under verified/ holding .lean files, keyed by its
    path (primer/<t>, minif2f/test/<t>); its statement is the same path under targets/."""
    out = []
    verified, targets = Path(verified), Path(targets)
    for tdir in sorted({p.parent for p in verified.rglob("*.lean")}):
        rel = tdir.relative_to(verified)
        tfile = targets / rel.with_suffix(".lean")
        if not tfile.exists():
            continue
        statement = statement_of(tfile.read_text())
        best = None
        for p in sorted(tdir.glob("*.lean")):
            text = p.read_text()
            m = PROOF_SEP.search(text)
            body = text[m.end():].lstrip("\n") if m else ""
            if body.strip() and "sorry" not in body and (best is None or len(body) < len(best)):
                best = body
        if best:
            out.append({"key": str(rel), "sha": hashlib.sha256(declaration(statement).encode()).hexdigest(),
                        "tokens": tokens(statement), "statement": statement, "proof": best})
    return out


def nearest(ix, target_text, k=K, exclude=None):
    """The k closest solved theorems by TF-IDF cosine over statement tokens, never `exclude` or its statement."""
    statement = statement_of(target_text)
    sha = hashlib.sha256(declaration(statement).encode()).hexdigest()     # name-free: a renamed copy is the same theorem
    pool = [e for e in ix if e["key"] != exclude and e["sha"] != sha]
    if not pool:
        return []
    df = Counter(t for e in pool for t in set(e["tokens"]))
    n = len(pool)
    idf = lambda t: math.log((n + 1) / (df.get(t, 0) + 1)) + 1
    def vec(toks):
        c = Counter(toks)
        return {t: c[t] * idf(t) for t in c}
    q = vec(tokens(statement))
    qn = math.sqrt(sum(v * v for v in q.values())) or 1.0
    scored = []
    for e in pool:
        v = vec(e["tokens"])
        dot = sum(q[t] * v[t] for t in q if t in v)
        vn = math.sqrt(sum(x * x for x in v.values())) or 1.0
        scored.append((dot / (qn * vn), e))
    scored.sort(key=lambda x: (-x[0], x[1]["key"]))
    return [e for s, e in scored[:k] if s > 0]


def block(ix, target_text, k=K, exclude=None):
    near = nearest(ix, target_text, k, exclude)
    if not near:
        return ""
    parts = [f"## Lessons: {len(near)} solved theorem{'s' if len(near) != 1 else ''} close to this one, each with a "
             "proof the Lean kernel accepted (read them; do not copy a statement)\n"]
    for i, e in enumerate(near, 1):
        decl = e["statement"][e["statement"].find("theorem"):].rstrip()
        proof = e["proof"] if len(e["proof"]) <= PROOF_CAP else e["proof"][:PROOF_CAP] + "\n  -- (cut)\n"
        parts.append(f"### Lesson {i}\n```lean4\n{decl}\n{proof.rstrip()}\n```\n")
    return "\n".join(parts) + "\n"


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("target", help="<set>/<target>, e.g. minif2f/test/aime_1983_p1")
    ap.add_argument("--k", type=int, default=K)
    a = ap.parse_args(argv)
    tset, name = a.target.rsplit("/", 1)
    text = (ROOT / "targets" / tset / f"{name}.lean").read_text()
    ix = index()
    print(f"index: {len(ix)} solved targets", file=sys.stderr)
    print(block(ix, text, a.k, exclude=a.target) or "(no lesson close enough)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
