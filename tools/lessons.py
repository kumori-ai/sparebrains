"""The lessons station (DECISIONS.md 2026-10-28; Andy's school: the lanes that solved a problem teach the ones that
have not, with nothing trained). A lane asked to prove a theorem is shown the k nearest solved theorems by statement
and their kernel-accepted proofs, read from verified/. Retrieval is the one known lift for a small prover that needs
no weights: ReProver, arXiv 2306.15626 (2023), 47.6% to 51.2% with premise retrieval. Never the problem's own proof,
never a proof of the same theorem (by a name-free declaration sha), so a solved problem in a head-to-head is taught only by others.

Two retrievals (kumori #574, 2026-10-29). `statement`: TF-IDF over the whole declaration, the 2026-10-28 pilot
(no lift on Leanstral, 6 vs 6 of 30). `conclusion`: over what must be proved, the text after the signature's last
top-level colon, so a theorem is taught by proofs of its shape (`% 2 = 1`, `IsGreatest`, `∑`) rather than by ones
that share its variables and hypotheses; where the loop left the problem one-step goals (ledger/goal-queue.json),
those goals are shown first and the lessons are the proofs nearest to them.

    python3 tools/lessons.py minif2f/test/aime_1983_p1 --k 3 [--by conclusion]   # print the block a lane would see
"""
import argparse, hashlib, json, math, re, sys
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT / "tools")]
from proof_text import PROOF_SEP
from goal_closer import NUM_ASCRIPTION

K, PROOF_CAP = 3, 2500
TOKEN = re.compile(r"[A-Za-z_][A-Za-z0-9_'.₀-₉]*|[∀∃∑∏√∣≤≥≠∈∉⊆∧∨¬→↔ℕℤℚℝℂ%^*/+\-]")          # the 10-28 pilot's, unchanged
SHAPE_TOKEN = re.compile(r"[A-Za-z_][A-Za-z0-9_'.₀-₉]*|[∀∃∑∏√∣≤≥≠∈∉⊆∧∨¬→↔ℕℤℚℝℂ%^*/+\-=<>!]")    # + equality and order
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


def conclusion(statement):
    """What must be proved: the declaration after its last top-level colon, before `:= by`, spacing kept (unlike
    goal_closer.conclusion, which strips spaces to compare goals; here the text is tokenized)."""
    sig = re.sub(r":=\s*by\s*$", "", declaration(statement_of(statement)).strip())
    depth, last = 0, None
    for i, c in enumerate(sig):
        if c in "([{⟨":
            depth += 1
        elif c in ")]}⟩":
            depth -= 1
        elif c == ":" and depth == 0 and sig[i + 1:i + 2] != "=":
            last = i
    return (sig[last + 1:] if last is not None else sig).strip()


def ctokens(statement):
    """The conclusion's shape: its operators, types and Mathlib names (gcd, IsLeast, sqrt, Prime), with bound
    variables dropped and dot notation reduced to its last segment (`a.gcd` and `Nat.gcd` are one shape). Measured
    2026-10-29 on the 332-target index: a, b, x and n were the four commonest conclusion tokens and `a.gcd` never
    matched `Nat.gcd`, so the goal `IsLeast {.. a.gcd b = 6 .. a.lcm b = x}` ranked `20 + 20 = 40` first."""
    out = []
    for t in SHAPE_TOKEN.findall(NUM_ASCRIPTION.sub(r"\1", conclusion(statement))):   # `(3 : ℕ)` is 3: Lean prints one per literal
        t = t.rsplit(".", 1)[-1] if "." in t else t
        if t in STOP or t == "_" or re.fullmatch(r"[a-z][a-z0-9'₀-₉]?", t) or re.fullmatch(r"h[₀-₉0-9']*", t):
            continue                                     # a, b, x₀, n', hn: the variables, not the shape
        out.append(t)
    return out


BY = ("statement", "conclusion")
GOALS_CAP = 2                    # one-step goals shown per problem (the queue is sorted: real steps, most sketches first)
QUEUE = ROOT / "ledger" / "goal-queue.json"


def goals_for(key, queue=QUEUE, cap=GOALS_CAP):
    """The problem's stored one-step goals a lane could be taught toward: readable, and not the theorem restated."""
    try:
        rows = json.loads(Path(queue).read_text())
    except (OSError, ValueError):
        return []
    return [g["goal"] for g in rows if f"{g['target_set']}/{g['target']}" == key and g.get("file_ok")
            and not g.get("restates")][:cap]


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
                        "tokens": tokens(statement), "ctokens": ctokens(statement), "statement": statement, "proof": best})
    return out


def nearest(ix, target_text, k=K, exclude=None, by="statement", query=None):
    """The k closest solved theorems by TF-IDF cosine, never `exclude` or its statement. `by` picks the tokens
    (statement: the whole declaration; conclusion: what must be proved); `query` is a goal to search from instead
    of the problem's own statement (the problem is still the one excluded)."""
    statement = statement_of(target_text)
    sha = hashlib.sha256(declaration(statement).encode()).hexdigest()     # name-free: a renamed copy is the same theorem
    pool = [e for e in ix if e["key"] != exclude and e["sha"] != sha]
    if not pool:
        return []
    field, tok = ("ctokens", ctokens) if by == "conclusion" else ("tokens", tokens)
    df = Counter(t for e in pool for t in set(e[field]))
    n = len(pool)
    idf = lambda t: math.log((n + 1) / (df.get(t, 0) + 1)) + 1
    def vec(toks):                                   # shape is presence: binary weights for the conclusion
        c = Counter(toks)
        return {t: (1 if by == "conclusion" else c[t]) * idf(t) for t in c}
    q = vec(tok(statement_of(query) if query else statement))
    qn = math.sqrt(sum(v * v for v in q.values())) or 1.0
    scored = []
    for e in pool:
        v = vec(e[field])
        dot = sum(q[t] * v[t] for t in q if t in v)
        vn = math.sqrt(sum(x * x for x in v.values())) or 1.0
        scored.append((dot / (qn * vn), e))
    scored.sort(key=lambda x: (-x[0], x[1]["key"]))
    return [e for s, e in scored[:k] if s > 0]


def block(ix, target_text, k=K, exclude=None, by="statement", goals=()):
    """The text put before the prompt. With `goals` (the loop's one-step goals for this problem), they are shown
    first and the lessons are the k proofs nearest to them, by `by`; else the k nearest to the statement."""
    if goals:
        near, seen = [], set()
        for g in goals:
            for e in nearest(ix, target_text, k, exclude, by, query=g):
                if e["key"] not in seen:
                    seen.add(e["key"]); near.append(e)
        near = near[:k]
    else:
        near = nearest(ix, target_text, k, exclude, by)
    if not near:
        return ""
    parts = []
    if goals:
        parts.append(f"## Where the loop stopped: {len(goals)} one-step goal{'s' if len(goals) != 1 else ''} left open "
                     "by a proof of this theorem (close one and the sketch goes through; or prove the theorem your way)\n")
        parts += [f"```lean4\n{g.strip()}\n```\n" for g in goals]
    parts.append(f"## Lessons: {len(near)} solved theorem{'s' if len(near) != 1 else ''} close to "
                 f"{'those goals' if goals else 'this one'}, each with a proof the Lean kernel accepted (read them; do not copy a statement)\n")
    for i, e in enumerate(near, 1):
        decl = e["statement"][e["statement"].find("theorem"):].rstrip()
        proof = e["proof"] if len(e["proof"]) <= PROOF_CAP else e["proof"][:PROOF_CAP] + "\n  -- (cut)\n"
        parts.append(f"### Lesson {i}\n```lean4\n{decl}\n{proof.rstrip()}\n```\n")
    return "\n".join(parts) + "\n"


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("target", help="<set>/<target>, e.g. minif2f/test/aime_1983_p1")
    ap.add_argument("--k", type=int, default=K)
    ap.add_argument("--by", choices=BY, default="statement")
    a = ap.parse_args(argv)
    tset, name = a.target.rsplit("/", 1)
    text = (ROOT / "targets" / tset / f"{name}.lean").read_text()
    ix = index()
    goals = goals_for(a.target) if a.by == "conclusion" else []
    print(f"index: {len(ix)} solved targets; {len(goals)} stored goals", file=sys.stderr)
    print(block(ix, text, a.k, exclude=a.target, by=a.by, goals=goals) or "(no lesson close enough)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
