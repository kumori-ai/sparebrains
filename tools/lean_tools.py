"""The Lean tools: the same four commands for a free model's relay, a volunteer's agent, and the hosted
check bench, so none of them drifts from the others (DECISIONS.md 2026-10-08).

    python3 tools/lean_tools.py check   proof.lean                  the judge (tools/check.py), unchanged
    python3 tools/lean_tools.py names   Nat.Prime.dvd_pow           real mathlib names closest to a guess
    python3 tools/lean_tools.py suggest proof.lean                  every `sorry` tried with exact? / apply?
    python3 tools/lean_tools.py auto    mil/mil_c05_s01_ex03        Lean's own automation on a target, no model
    python3 tools/lean_tools.py bench   --event E --reply R         the hosted check bench (.github/workflows/bench.yml)

Every run of Lean goes through check.lean_cmd: as the sandbox user in Actions, with no key in its
environment. `names` reads mathlib's sources (.lake/packages/mathlib), nothing else. A proof found by
`auto` or `suggest` still counts only when `check` accepts it.
"""
import argparse, difflib, json, re, sys, tempfile, time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT / "tools")]
import check                                             # the judge and its sandboxed Lean command
import fixer                                             # mathlib's name index
from proof_text import PROOF_SEP

MATHLIB = ROOT / ".lake" / "packages" / "mathlib" / "Mathlib"
CLOSERS = ["exact?", "aesop?", "omega", "decide", "norm_num", "simp", "linarith", "positivity", "nlinarith"]
# Lean 4.33 prints "Try this:" then, on the next line, "  [apply] exact Nat.lt_of_succ_le h" (2026-10-08)
TRY_THIS = re.compile(r"Try this:[ \t]*\n?[ \t]*(?:\[\w+\][ \t]*)?([^\n]+)")
_INDEX = {}


def index():
    if "names" not in _INDEX:
        _INDEX["names"] = fixer.mathlib_index(MATHLIB)
        _INDEX["by_last"] = fixer._by_last(_INDEX["names"])
    return _INDEX["names"], _INDEX["by_last"]


def names(guess, k=6):
    """Real names for a guessed one, best first: the same last part under another namespace, then close
    spellings under the same top namespace, then close spellings anywhere. [] when nothing is close."""
    idx, by_last = index()
    if guess in idx:
        return [guess]
    last, root = guess.split(".")[-1], guess.split(".")[0]
    out = sorted(by_last.get(last, ()), key=lambda n: (n.split(".")[0] != root, len(n)))
    pool = [n for n in idx if n.startswith(root + ".")] if "." in guess else list(idx)
    out += [n for n in difflib.get_close_matches(guess, pool, n=k, cutoff=0.75) if n not in out]
    return out[:k]


def run_lean(text, timeout=180):
    """(output, seconds) of Lean on `text`, sandboxed exactly as the judge runs it."""
    import subprocess
    with tempfile.NamedTemporaryFile("w", suffix=".lean", dir=ROOT, delete=False) as f:
        f.write(text)
    cmd, env = check.lean_cmd(f.name)
    t0 = time.monotonic()
    try:
        run = subprocess.run(cmd, env=env, capture_output=True, text=True, timeout=timeout, cwd=ROOT)
        out = run.stdout + run.stderr
    except subprocess.TimeoutExpired:
        out = f"timeout after {timeout}s"
    finally:
        Path(f.name).unlink(missing_ok=True)
    return out.replace(f.name, "proof.lean"), time.monotonic() - t0


def judge_text(text, timeout=300):
    with tempfile.NamedTemporaryFile("w", suffix=".lean", dir=ROOT, delete=False) as f:
        f.write(text)
    try:
        verdict, reason, secs, out = check.judge(f.name, timeout)
    finally:
        Path(f.name).unlink(missing_ok=True)
    clean = lambda t: (t or "").replace(f.name, "proof.lean")     # no runner or temp paths in a public reply
    return {"verdict": verdict, "reason": clean(reason), "seconds": round(secs, 1), "output": clean(out)[-4000:]}


def suggest(text, timeout=180):
    """Every `sorry` in a file tried with `exact?`, then `apply?`: what Lean proposes for each hole."""
    holes = len(re.findall(r"\bsorry\b", text))
    if not holes:
        return {"holes": 0, "suggestions": [], "note": "no `sorry` in the file: put one where you are stuck"}
    found = []
    for tactic in ("exact?", "apply?"):
        out, secs = run_lean(re.sub(r"\bsorry\b", tactic, text), timeout)
        tries = [t.strip() for t in TRY_THIS.findall(out)]
        found.append({"tactic": tactic, "seconds": round(secs, 1), "try_this": tries[:8],
                      "lean": out.strip()[-1500:] if not tries else ""})
        if tries:
            break
    return {"holes": holes, "suggestions": found}


def auto(target_text, timeout=120):
    """Lean's own closers on a target's statement, one at a time. The first that `check` accepts is a
    proof (a `Try this` from exact?/aesop? is spliced in and judged again, so the proof is concrete)."""
    prefix = target_text[:PROOF_SEP.search(target_text).end()]
    tried = []
    for tactic in CLOSERS:
        r = judge_text(prefix + "\n  " + tactic + "\n", timeout)
        concrete = None
        if tactic.endswith("?") and r["verdict"] == "accept":
            tt = TRY_THIS.findall(r["output"])
            if tt:
                concrete = tt[0].strip()
                r = judge_text(prefix + "\n  " + concrete + "\n", timeout)
        tried.append({"tactic": tactic, "verdict": r["verdict"], "seconds": r["seconds"], "proof": concrete or tactic})
        if r["verdict"] == "accept":
            return {"solved": True, "by": concrete or tactic, "tried": tried}
    return {"solved": False, "tried": tried}


LEAN_BLOCK = re.compile(r"```lean[ \t]*\n(.*?)```", re.S)
MAX_LEAN = 60_000


def bench_reply(text):
    """The check bench's answer to one ```lean block: the verdict, real names for anything Lean did not
    know, and exact?/apply? for every `sorry`. The same commands a volunteer runs locally."""
    r = judge_text(text)
    lines = [f"**{'✅ Accepted' if r['verdict'] == 'accept' else 'Checked: ' + r['verdict']}** · {r['reason']} · {r['seconds']}s"]
    unknown = list(dict.fromkeys(fixer.UNKNOWN.findall(r["output"])))[:6]
    if unknown:
        lines += ["", "**Names Lean did not know, and real ones close to them:**"]
        lines += [f"- `{u}` → " + (", ".join(f"`{n}`" for n in names(u, k=4)) or "nothing close") for u in unknown]
    if re.search(r"\bsorry\b", text):
        sg = suggest(text)
        tries = [t for s_ in sg["suggestions"] for t in s_["try_this"]]
        lines += ["", f"**For the `sorry` holes ({sg['holes']}), Lean suggests:**"]
        lines += [f"- `{t}`" for t in tries[:6]] or ["- nothing found by `exact?` or `apply?`"]
    if r["verdict"] != "accept" and r["output"].strip():
        lines += ["", "<details><summary>What Lean said</summary>", "", "```", r["output"].strip()[-2500:], "```", "</details>"]
    lines += ["", "_Same tools as `python3 tools/lean_tools.py check / names / suggest`. A bench check is for "
              "trying ideas; a proof counts when it is posted as a hand-off on its problem's thread._"]
    return "\n".join(lines)


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    sub = ap.add_subparsers(dest="cmd", required=True)
    for c in ("check", "suggest"):
        sub.add_parser(c).add_argument("file")
    sub.add_parser("names").add_argument("guess")
    sub.add_parser("auto").add_argument("target", help="<set>/<target> or a .lean file")
    b = sub.add_parser("bench")
    b.add_argument("--event", required=True)
    b.add_argument("--reply", required=True)
    a = ap.parse_args()
    if a.cmd == "bench":                                 # comments are data: only the ```lean block is used
        ev = json.loads(Path(a.event).read_text())
        blocks = LEAN_BLOCK.findall(ev["comment"].get("body") or "")
        if not blocks:
            print("no ```lean block; nothing to check")
            return 0
        text = blocks[-1] if len(blocks[-1]) <= MAX_LEAN else None
        reply = bench_reply(text) if text else f"The Lean block is over {MAX_LEAN:,} characters."
        Path(a.reply).write_text(f"@{ev['comment']['user']['login']} " + reply)
        return 0
    if a.cmd == "names":
        out = {"guess": a.guess, "exists": a.guess in index()[0], "real": names(a.guess)}
    elif a.cmd == "check":
        out = judge_text(Path(a.file).read_text())
    elif a.cmd == "suggest":
        out = suggest(Path(a.file).read_text())
    else:
        p = Path(a.target) if a.target.endswith(".lean") else ROOT / "targets" / f"{a.target}.lean"
        out = auto(p.read_text())
    print(json.dumps(out, indent=2, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    sys.exit(main())
