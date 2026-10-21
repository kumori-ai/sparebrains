"""The automation sweep on google-deepmind/formal-conjectures (task #478, roadmap row 9): every `textbook` and `test`
declaration still at `sorry` gets our loop's closers (subgoals.AUTO_TACTICS) in one `first | ...`, checked in their
own build (Lean v4.33.1, their pinned Mathlib) with `#print axioms`, the check their PROOFS.md asks for. A pass is
no error inside the declaration and only the standard axioms; the tactic that closed it is then found alone. No
model, $0. Nothing is sent to their repository: a pass is a candidate for a PR that Andy approves.

    python3 tools/fc_sweep.py --fc path/to/formal-conjectures --out ledger/fc/sweep-RUN.jsonl
"""
import argparse, hashlib, json, os, re, subprocess, sys, time
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT), str(ROOT / "tools")]
from subgoals import AUTO_TACTICS
from proof_text import extract_proof

FC_COMMIT = "90d18f666eb98adec4eee4d12f1d37e30b4eb204"
CATEGORIES = ("textbook", "test")
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
TIMEOUT_S = 300


def declarations(text):
    """[{category, name, start, end}] for each `@[category ...]` theorem; lines start..end-1, ending at the next
    unindented line (Lean continues a declaration on indented lines)."""
    lines, out = text.split("\n"), []
    for i, line in enumerate(lines):
        m = re.match(r"@\[category ([a-z]+(?: [a-z]+)?)", line)
        if not m:
            continue
        j = next((j for j in range(i + 1, min(i + 4, len(lines))) if re.match(r"\s*(theorem|lemma)\s", lines[j])), None)
        if j is None:
            continue
        k = j + 1
        while k < len(lines) and (lines[k].startswith((" ", "\t")) or
                                  (lines[k] == "" and k + 1 < len(lines) and lines[k + 1].startswith((" ", "\t")))):
            k += 1
        out.append({"category": m.group(1), "name": re.match(r"\s*(?:theorem|lemma)\s+(\S+)", lines[j]).group(1),
                    "start": j, "end": k})
    return out


def targets(text):
    lines = text.split("\n")
    return [d for d in declarations(text) if d["category"] in CATEGORIES
            and re.search(r":=\s*(by\s*)?\n?\s*sorry$", "\n".join(lines[d["start"]:d["end"]]).rstrip())]


def candidate(text, d, tactics):
    """The file with this declaration's `sorry` replaced by the tactics and `#print axioms` right after it."""
    return _splice(text, d, "  first | " + " | ".join(f"({t})" for t in tactics))


def with_proof(text, d, reply):
    """A prover's proof body under their statement, unchanged (any restatement in the reply is dropped), or None."""
    body = extract_proof(reply or "", d["name"])
    return _splice(text, d, body.rstrip("\n")) if body else None


def prompt(text, d):
    """The file up to and including the target (its definitions are the context), and what to reply."""
    context = "\n".join(text.split("\n")[:d["end"]]).rstrip()[-12000:]
    return (f"Complete the following Lean 4 code (Lean v4.33.1, Mathlib and this file's own definitions): prove "
            f"`{d['name']}`, keeping its statement exactly. Reply with the whole theorem in one ```lean4 block."
            f"\n\n```lean4\n{context}\n```")


def _splice(text, d, tac):
    lines = text.split("\n")
    body = lines[d["start"]:d["end"]]
    while body and not body[-1].strip():
        body.pop()
    last = body[-1]
    if last.strip() == "sorry":                                   # `:= by` then `sorry` on its own line
        body[-1] = tac
    else:                                                         # `:= sorry` or `:= by sorry` on one line
        body[-1] = re.sub(r"(:=\s*)(by\s+)?sorry$", r"\1by", last.rstrip())
        body.append(tac)
    body.append(f"#print axioms {d['name']}")
    return "\n".join(lines[:d["start"]] + body + lines[d["start"] + len(body) - 1 - (last.strip() != "sorry"):])


def region(text, name):
    """1-based (first, last) line of the declaration in a candidate file: its theorem line to its axioms line."""
    lines = text.split("\n")
    first = next(i for i, l in enumerate(lines) if re.match(r"\s*(theorem|lemma)\s+" + re.escape(name) + r"\b", l))
    last = next(i for i, l in enumerate(lines) if l == f"#print axioms {name}")
    return first + 1, last + 1


def proved(output, name, span):
    """No error inside the declaration's lines, and an axioms line for it with only the standard axioms."""
    for m in re.finditer(r"^[^\n:]*:(\d+):\d+: error", output, re.M):
        if span[0] <= int(m.group(1)) <= span[1]:
            return False
    m = re.search(r"'(?:[^'\s]*\.)?" + re.escape(name) + r"' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",
                  output)
    if not m:
        return False
    axioms = {a.strip() for a in (m.group(1) or "").split(",") if a.strip()}
    return axioms <= STANDARD_AXIOMS


def lean_cmd(file, user, path):
    """Lean on one file; as the sandbox user with an emptied environment when there is one (tools/judge_sandbox.sh),
    because a prover's proof is untrusted code (#eval runs IO while Lean elaborates)."""
    cmd = ["lake", "env", "lean", str(file)]
    return ["sudo", "-n", "-u", user, "env", "-i", f"PATH={path}", f"HOME=/tmp/{user}", *cmd] if user else cmd


def run_lean(fc, text, tag):
    f = (Path(fc) / ".sweep" / f"{tag}.lean").resolve()   # absolute: Lean runs inside their checkout (cwd=fc)
    f.parent.mkdir(exist_ok=True)
    f.write_text(text)
    f.chmod(0o644)
    t = time.time()
    try:
        r = subprocess.run(lean_cmd(f, os.environ.get("SB_JUDGE_USER"), os.environ.get("PATH", "")), cwd=fc,
                           capture_output=True, text=True, timeout=TIMEOUT_S)
        out = r.stdout + r.stderr
    except subprocess.TimeoutExpired:
        out = "timeout"
    return out, round(time.time() - t, 1)


def sweep_one(fc, rel, text, d):
    tag = hashlib.sha1(f"{rel}:{d['name']}".encode()).hexdigest()[:12]
    cand = candidate(text, d, AUTO_TACTICS)
    out, secs = run_lean(fc, cand, tag)
    row = {"file": rel, "name": d["name"], "category": d["category"], "seconds": secs,
           "statement_sha": hashlib.sha256("\n".join(text.split("\n")[d["start"]:d["end"]]).encode()).hexdigest()}
    if not proved(out, d["name"], region(cand, d["name"])):
        return {**row, "verdict": "open", "timeout": out == "timeout"}
    for t in AUTO_TACTICS:                                        # which one closed it, alone
        alone = candidate(text, d, [t])
        o, _ = run_lean(fc, alone, tag)
        if proved(o, d["name"], region(alone, d["name"])):
            return {**row, "verdict": "proved", "tactic": t, "proof": t}
    return {**row, "verdict": "proved", "tactic": "first | ...", "proof": " | ".join(AUTO_TACTICS)}


def leanstral_cap():
    import leanstral
    return leanstral.MAX_TOKENS


def _capped(r):
    return r.get("verdict") == "no_proof" and r.get("finish") == "length" and (r.get("tokens") or 0) >= leanstral_cap()


def effort(w, rows):
    """'none' for a declaration whose answers so far all ran out at today's cap (probe 2026-10-21: 6 of 8)."""
    mine = [r for r in rows if (r["file"], r["name"]) == (w[0], w[2]["name"])]
    return "none" if mine and all(_capped(r) for r in mine) else None


def owed(work, rows, limit):
    """Cut-off declarations once more, without long reasoning, first; then the ones with no row yet, so runs resume
    where the last one stopped. A declaration asked both ways, or answered in full, is done."""
    by = {}
    for r in rows:
        by.setdefault((r["file"], r["name"]), []).append(r)
    retry = [w for w in work if (k := (w[0], w[2]["name"])) in by and all(_capped(r) for r in by[k])
             and not any(r.get("effort") == "none" for r in by[k])]
    fresh = [w for w in work if (w[0], w[2]["name"]) not in by]
    return (retry + fresh)[:limit]


def generate(fc, work, out, rows=()):
    """Leanstral's answers for these declarations; holds the key, runs no Lean."""
    import leanstral
    key, pacer = leanstral.key_from_env(), leanstral.Pacer(leanstral.MIN_GAP_S)

    def one(w):
        rel, text, d = w
        e = effort(w, rows)
        try:
            r = leanstral.call_prompt(key, prompt(text, d), pacer, e)
            return {"file": rel, "name": d["name"], "category": d["category"], "effort": e or "high", **r}
        except Exception as e:
            return {"file": rel, "name": d["name"], "category": d["category"], "error": str(e)[:300]}
    with ThreadPoolExecutor(leanstral.WORKERS) as ex:
        answers = list(ex.map(one, work))
    Path(out).write_text("".join(json.dumps(a) + "\n" for a in answers))
    print(f"fc leanstral: {len(work)} asked, {sum('error' not in a for a in answers)} answered", flush=True)


def judge(fc, answers, texts, out):
    """Each answer's proof under their statement, checked in their build as the sandbox user."""
    import leanstral

    def one(a):
        text = texts[a["file"]]
        d = next(x for x in targets(text) if x["name"] == a["name"])
        row = {"file": a["file"], "name": a["name"], "category": a["category"], "lane": leanstral.LANE["backend"],
               "effort": a.get("effort", "high"),
               "model": leanstral.MODEL, "finish": a.get("finish"), "tokens": a.get("tokens"),
               "statement_sha": hashlib.sha256("\n".join(text.split("\n")[d["start"]:d["end"]]).encode()).hexdigest()}
        if "error" in a:
            return {**row, "verdict": "error", "reason": a["error"]}
        cand = with_proof(text, d, a.get("text"))
        if cand is None:
            return {**row, "verdict": "no_proof"}
        o, secs = run_lean(fc, cand, hashlib.sha1(f"{a['file']}:{a['name']}:lp".encode()).hexdigest()[:12])
        if proved(o, d["name"], region(cand, d["name"])):
            return {**row, "verdict": "proved", "seconds": secs, "proof": extract_proof(a["text"], d["name"])}
        err = re.search(r"error: (.*)", o)
        return {**row, "verdict": "reject", "seconds": secs, "reason": (err.group(1) if err else o[-200:])[:300]}
    stamp = datetime.now(timezone.utc).isoformat(timespec="seconds")
    with ThreadPoolExecutor(4) as ex, open(out, "w") as fh:
        for row in ex.map(one, answers):
            fh.write(json.dumps({"at": stamp, "fc_commit": FC_COMMIT, **row}) + "\n")
            if row["verdict"] == "proved":
                print(f"proved {row['file']}:{row['name']} (leanstral)", flush=True)
    rows = [json.loads(l) for l in open(out)]
    print(f"fc leanstral judged: {sum(r['verdict'] == 'proved' for r in rows)} of {len(rows)} proved", flush=True)


CANARY = "module\n\npublic import FormalConjecturesUtil\n\n@[category test, AMS 11]\ntheorem sweep_canary : {claim} := by\n  sorry\n"


def canaries_ok(fc):
    """In their environment, before any real target: a true claim must be proved and a false one must stay open,
    or every 'open' below would be meaningless."""
    verdicts = []
    for claim in ("(2 : ℕ) + 2 = 4", "(2 : ℕ) + 2 = 5"):
        text = CANARY.format(claim=claim)
        d = targets(text)[0]
        cand = candidate(text, d, AUTO_TACTICS)
        out, _ = run_lean(fc, cand, "canary")
        verdicts.append(proved(out, d["name"], region(cand, d["name"])))
        print(f"canary {claim}: {'proved' if verdicts[-1] else 'open'}" + ("" if verdicts[-1] or "5" in claim else f"\n{out[-1500:]}"),
              flush=True)
    return verdicts == [True, False]


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("cmd", nargs="?", default="sweep", choices=["sweep", "generate", "judge"])
    ap.add_argument("--fc", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--answers", help="judge: the generate step's answers")
    ap.add_argument("--workers", type=int, default=4)
    ap.add_argument("--limit", type=int)
    a = ap.parse_args()
    fc = Path(a.fc)
    if a.cmd in ("generate", "judge"):
        files = {str(p.relative_to(fc)): p.read_text(errors="replace") for p in sorted((fc / "FormalConjectures").rglob("*.lean"))}
        if a.cmd == "generate":
            prior = [json.loads(l) for f in sorted((ROOT / "ledger" / "fc").glob("leanstral-*.jsonl")) for l in open(f)]
            work = owed([(rel, t, d) for rel, t in files.items() for d in targets(t)], prior, a.limit or 40)
            generate(fc, work, a.out, prior)
        else:
            if not canaries_ok(fc):          # as the sandbox user now: it must be able to read their build
                sys.exit("canaries failed under the sandbox user: no proof can be judged here")
            judge(fc, [json.loads(l) for l in open(a.answers)], files, a.out)
        return 0
    if not canaries_ok(fc):
        sys.exit("canaries failed: the sweep cannot tell a proof from a miss here, so it does not run")
    work = [(str(p.relative_to(fc)), t, d) for p in sorted((fc / "FormalConjectures").rglob("*.lean"))
            for t in [p.read_text(errors="replace")] for d in targets(t)][:a.limit]
    print(f"fc sweep: {len(work)} declarations at sorry ({', '.join(CATEGORIES)}), commit {FC_COMMIT[:12]}", flush=True)
    stamp = datetime.now(timezone.utc).isoformat(timespec="seconds")
    Path(a.out).parent.mkdir(parents=True, exist_ok=True)
    with ThreadPoolExecutor(a.workers) as ex, open(a.out, "w") as fh:
        for row in ex.map(lambda w: sweep_one(fc, *w), work):
            fh.write(json.dumps({"at": stamp, "fc_commit": FC_COMMIT, **row}) + "\n")
            fh.flush()
            if row["verdict"] == "proved":
                print(f"proved {row['file']}:{row['name']} by {row['tactic']}", flush=True)
    rows = [json.loads(l) for l in open(a.out)]
    print(f"fc sweep: {sum(r['verdict'] == 'proved' for r in rows)} of {len(rows)} closed by automation", flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
