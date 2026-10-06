"""Stage 2, the relay (DECISIONS.md 2026-10-06): the strongest live lanes try an open problem from
its dossier, everything known about it, instead of from nothing.

The dossier is the public page https://sparebrains.kumori.ai/problems/<set>/<target>.json: the
closest rejected proofs with Lean's output, how every try failed, the library names models invented,
and the comments people left on the problem's GitHub thread. It never holds a known proof of the
problem itself (the site leaves near misses out once a problem is solved, and reference proofs
never reach it), and this module refuses a solved one anyway.

Try modes: `relay` (the dossier) and `relay+thread` (the dossier plus at least one comment), each
recorded beside `cold` and `repair` so the clean numbers stay clean.
"""
import hashlib, json, re, urllib.request
from collections import Counter

SITE = "https://sparebrains.kumori.ai"
RELAY_TRIES = 3                    # per (target, lane), like the ladder's three tries per cell
PROMPT_CAP = 24_000                # free-model context windows; the full dossier stays at its URL
NEAR_SHOWN, PROOF_CAP, LEAN_CAP, COMMENT_CAP = 3, 2_000, 1_500, 1_500
RUNNER_PATH = re.compile(r"\S*/\.lake/attempts/\S+?\.lean:")    # keep "line:col: error", drop the runner path

RELAY = ("Other models, and possibly people, have already tried to prove the Lean 4 theorem at the end of this "
         "message, and every attempt so far was rejected by the Lean kernel. Below is what they tried and exactly "
         "why it failed. Learn from it, then write a complete proof.\n\n"
         "Rules: Lean v4.33.1 and mathlib v4.33.1, and `import Mathlib` is already in the file. Replace only the "
         "`sorry`; keep the theorem statement byte-for-byte; no `sorry`, `admit`, or `native_decide`; no new "
         "axioms; Lean 4 syntax, not Lean 3. Answer with the complete file in one ```lean code block.\n\n")


def is_relay(row):
    return str(row.get("try_mode") or "").startswith("relay")


# Cloudflare in front of kumori.ai answers the default "Python-urllib/x.y" agent with error 1010
# (403); run 37520440995's first relay fetch died on it, 2026-10-06. Say who is asking instead.
USER_AGENT = "sparebrains-relay (+https://github.com/kumori-ai/sparebrains)"


def fetch_dossier(target_set, target, timeout=30):
    url = f"{SITE}/problems/{target_set}/{target}.json"
    req = urllib.request.Request(url, headers={"User-Agent": USER_AGENT, "Accept": "application/json"})
    with urllib.request.urlopen(req, timeout=timeout) as r:
        return json.loads(r.read().decode())


def lane_strength(rows, rungs):
    """backend → distinct targets it proved above MATH level 2: the stage-2 lane ranking."""
    hard = set(rungs[rungs.index("math-L2") + 1:])
    seen = {(r.get("backend"), r.get("target_set"), r.get("target"))
            for r in rows if r.get("verdict") == "accept" and r.get("rung") in hard}
    return Counter(b for b, _, _ in seen)


def strongest(live_lanes, strength, k):
    """The k live lanes with the most hard solves; a lane with none never relays."""
    ranked = sorted((l for l in live_lanes if strength.get(l["backend"])),
                    key=lambda l: (-strength[l["backend"]], l["backend"]))
    return ranked[:k]


def _clip(text, cap):
    text = (text or "").rstrip()
    return text if len(text) <= cap else text[:cap] + "\n…"


def relay_prompt(target_text, dossier, this_job=()):
    """(prompt, meta). `this_job` holds this run's own rejected relay tries on the target, newest
    last, so the next lane sees them before the site has caught up."""
    if dossier.get("solved"):
        raise ValueError(f"{dossier.get('target')} is solved: a relay prompt would carry a known proof")
    parts = [RELAY]
    fails = ", ".join(f"{f['kind']} {f['n']} (by {f['lanes']} lanes)" for f in dossier.get("failures", []))
    parts.append(f"## Earlier tries\n{dossier.get('answered', 0)} answered tries by {dossier.get('lanes_tried', 0)} "
                 f"models, all rejected. How they failed: {fails or 'unknown'}.\n\n")
    names = [n for n, _ in dossier.get("unknown_names") or [] if "." in n]   # library names; `h`, `k` are out-of-scope locals
    if names:
        parts.append("## Names that do not exist in this mathlib (models used them anyway)\n"
                     + ", ".join(names) + "\n\n")
    near = [{"backend": b, "failure_kind": k, "proof": p, "lean_output": o, "id": None} for b, k, p, o in this_job][::-1]
    near += dossier.get("near_misses") or []
    if near:
        parts.append("## The closest attempts, best first, each with what Lean said\n")
        for i, m in enumerate(near[:NEAR_SHOWN], 1):
            parts.append(f"### Attempt {i} ({m['failure_kind']})\n```lean\n{_clip(m['proof'], PROOF_CAP)}\n```\n"
                         f"Lean said:\n```\n{_clip(RUNNER_PATH.sub('', m['lean_output'] or ''), LEAN_CAP)}\n```\n\n")
    thread = dossier.get("thread") or []
    if thread:
        parts.append("## What people said on the problem's public thread (ideas, not checked)\n")
        for c in thread:
            parts.append(f"- {c.get('author') or 'someone'}: {_clip(c.get('body'), COMMENT_CAP)}\n")
        parts.append("\n")
    tail = "## The file to complete\n\n" + target_text
    body = "".join(parts)
    if len(body) + len(tail) > PROMPT_CAP:
        body = body[:PROMPT_CAP - len(tail) - 2] + "\n…\n\n"
    shown = [m["id"] for m in near[:NEAR_SHOWN] if m.get("id")]
    meta = {"try_mode": "relay+thread" if thread else "relay",
            "prev_id": shown[0] if shown else None,
            "comment_ids": [c.get("comment_id") for c in thread],
            "dossier_sha": hashlib.sha256(body.encode()).hexdigest()[:16]}
    return body + tail, meta
