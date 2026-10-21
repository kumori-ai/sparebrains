"""Which miniF2F test problems a published prover has proved, statement for statement (DECISIONS.md 2026-10-20,
task #534). DeepSeek-Prover-V2-671B and Kimina-Prover publish their miniF2F solutions; a proof counts only when its
theorem states what our target states, up to notation (`∑ k in` for `∑ k ∈`, parentheses, spacing). Many of theirs
prove an older, weaker or leaked statement (a one-sided bound for an IsLeast, a hypothesis giving the answer away),
and those do not count. The open problems with a match are the ones a strong prover is known to reach: the lanes'
first targets.

    python3 tools/reachable.py --work /tmp/reach --out ledger/reachable.json

The archives are fetched at pinned commits and only read as text; nothing in them runs.
"""
import argparse, io, json, re, subprocess, sys, urllib.request, zipfile
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SOURCES = {   # name: (repo, commit, archive, folder inside it holding the test split, or "" for all)
    "DeepSeek-Prover-V2": ("deepseek-ai/DeepSeek-Prover-V2", "e598a57ea3284997d4a2a168a069fdd5064afbc8",
                           "minif2f-solutions.zip", "test/"),
    "Kimina-Prover": ("MoonshotAI/Kimina-Prover-Preview", "7abd61a5d9861bf5c15b195c216c1bb233ac32e4",
                      "minif2f_test_solved.zip", ""),
}
THEOREM = r"^\s*theorem\s+([A-Za-z0-9_']+)"


def statement(text, name):
    """The theorem's binders and type, whitespace collapsed; None if the text does not state it."""
    m = re.search(r"\btheorem\s+" + re.escape(name) + r"\b(.*?):=", text, re.S)
    return re.sub(r"\s+", " ", m.group(1)).strip() if m else None


def match(ours, theirs):
    """'exact', 'notation', or None when the statements differ in substance (or theirs is missing)."""
    if not theirs:
        return None
    if ours == theirs:
        return "exact"
    norm = lambda s: re.sub(r"[\s()]", "", s.replace(" in ", " ∈ "))
    return "notation" if norm(ours) == norm(theirs) else None


def compare(ours, published):
    """target -> {source: 'exact' | 'notation' | None} for every target some source proved."""
    out = {}
    for src, proofs in published.items():
        for name, text in proofs.items():
            if name in ours:
                out.setdefault(name, {})[src] = match(statement(ours[name], name), statement(text, name))
    return out


def fetch(repo, sha, archive, folder):
    """theorem name -> the file that proves it, from a published archive."""
    url = subprocess.run(["gh", "api", f"repos/{repo}/contents/{archive}?ref={sha}", "-q", ".download_url"],
                         capture_output=True, text=True, check=True).stdout.strip()
    with urllib.request.urlopen(url) as r:
        z = zipfile.ZipFile(io.BytesIO(r.read()))
    out = {}
    for n in z.namelist():
        if n.endswith(".lean") and (not folder or f"/{folder}" in f"/{n}"):
            text = z.read(n).decode(errors="replace")
            for name in re.findall(THEOREM, text, re.M):
                out.setdefault(name, text)
    return out


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--out", default=str(ROOT / "ledger" / "reachable.json"))
    a = ap.parse_args()
    targets = ROOT / "targets" / "minif2f" / "test"
    ours = {p.stem: p.read_text() for p in sorted(targets.glob("*.lean"))}
    published = {src: fetch(*s) for src, s in SOURCES.items()}
    found = compare(ours, published)
    rows = [{"target_set": "minif2f/test", "target": n, "proved_by": {s: m for s, m in by.items() if m}}
            for n, by in sorted(found.items()) if any(by.values())]
    differs = sorted(n for n, by in found.items() if not any(by.values()))
    doc = {"as_of": datetime.now(timezone.utc).date().isoformat(),
           "sources": {s: {"repo": r, "commit": c, "archive": z} for s, (r, c, z, _) in SOURCES.items()},
           "targets": len(ours), "reachable": rows,
           "proved_other_statement": differs}
    Path(a.out).write_text(json.dumps(doc, indent=1, ensure_ascii=False) + "\n")
    print(f"reachable: {len(rows)} of {len(ours)} minif2f/test targets have a published proof of the same statement; "
          f"{len(differs)} were proved only as a different statement")
    return 0


if __name__ == "__main__":
    sys.exit(main())
