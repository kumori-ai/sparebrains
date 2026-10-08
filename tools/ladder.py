"""The ladder: which rung each target sits on, and what kind of failure a reject was.

Rungs are provenance, never our own results (that would be circular):
  primer      Natural Number Game levels restated over ℕ (leanprover-community/NNG4)
  mil         Mathematics in Lean exercises, chapters 2–6 (Avigad & Massot)
  math-L1..L5 miniF2F `mathd_*` items, labelled by the MATH dataset's own Level 1–5
              (Hendrycks et al. 2021; the mapping lives in targets/minif2f/levels.json)
  mathd       a `mathd_*` item the mapping could not label
  amc12, custom, aime, imo   the rest of miniF2F by problem source
"""
import json, re
from collections import defaultdict, deque
from datetime import datetime
from pathlib import Path

import relay                                    # stage-2 rows are counted apart from the ladder's

ROOT = Path(__file__).resolve().parent.parent
RUNGS = ["primer", "mil", "math-L1", "math-L2", "math-L3", "math-L4", "math-L5", "mathd", "amc12", "custom", "aime", "imo"]
RANK = {r: i for i, r in enumerate(RUNGS)}
PRIMER_WORLDS = ["tutorial", "addition", "multiplication", "power", "implication", "algorithm",
                 "advaddition", "lessorequal", "advmultiplication"]          # the game's own order
_levels = None


def _math_levels():
    global _levels
    if _levels is None:
        p = ROOT / "targets" / "minif2f" / "levels.json"
        _levels = json.loads(p.read_text()) if p.exists() else {}
    return _levels


def sort_key(target_set, name):
    """Order inside a rung: the primer follows the game's worlds, everything else its name."""
    if target_set == "primer":
        world = name.split("_")[1] if "_" in name else ""
        return (PRIMER_WORLDS.index(world) if world in PRIMER_WORLDS else 99, name)
    return (0, name)


def rung_of(target_set, name):
    """(rung label, rank) for one target. Unknown sets rank last so they still run."""
    if target_set == "primer":
        return "primer", RANK["primer"]
    if target_set == "mil":
        return "mil", RANK["mil"]
    if name.startswith("mathd_"):
        lv = (_math_levels().get(name) or {}).get("level")
        if lv in (1, 2, 3, 4, 5):
            return f"math-L{lv}", RANK[f"math-L{lv}"]
        return "mathd", RANK["mathd"]
    if name.startswith("amc12"):
        return "amc12", RANK["amc12"]
    if name.startswith("aime"):
        return "aime", RANK["aime"]
    if name.startswith("imo"):
        return "imo", RANK["imo"]
    return "custom", RANK["custom"]


# Why a kernel reject happened, from the first Lean error line. The bottom rungs are
# where this matters: a Lean 3 `begin … end` fails 2 + 2 = 4 exactly the way it fails an
# IMO problem, and the scoreboard must say "syntax", never "cannot add".
_KINDS = [
    ("no_fence",       re.compile(r"no proof extracted")),
    ("lean3_syntax",   re.compile(r"unexpected token|unexpected identifier|expected command|expected '\}'|'begin'|'end'", re.I)),
    ("unknown_name",   re.compile(r"unknown (identifier|constant|tactic|namespace)|unknownIdentifier|unknownConstant", re.I)),
    ("sorry",          re.compile(r"sorry|admit|native_decide|axiom", re.I)),
    ("timeout",        re.compile(r"timeout|timed out|maximum recursion|deterministic", re.I)),
    ("unsolved_goals", re.compile(r"unsolved goals", re.I)),
    ("tactic_failed",  re.compile(r"failed|could not|made no progress|no goals", re.I)),
    ("type_mismatch",  re.compile(r"type mismatch", re.I)),
]


# Who failed? A 'lane' error says something about this lane on this target: it was asked and
# did not answer in time, or answered with nothing. A 'router' error says nothing about the lane's
# ability at all: the router did not know the lane, gated it, fell over during a deploy, or was
# unreachable. Only lane errors may close a (target, lane) cell. 2026-09-20: one run sent 1,702
# calls at a lane whose upstream had died (458 x 502, then 1,244 x 404 once the router demoted
# it), and the three-error rule closed 250 cells the lane had never been asked about. Anything
# unrecognised is 'router': an unknown failure must never cost a target its try.
_LANE_ERRORS = re.compile(r"HTTP 504|did not respond in time|returned no text|Read timed out|ReadTimeout", re.I)
ALIVE_WINDOW_S = 30 * 60      # a lane error only counts if the same lane answered something this close to it


def error_scope(reason):
    """'lane' or 'router' for an attempt whose verdict is 'error'."""
    return "lane" if _LANE_ERRORS.search(reason or "") else "router"


def lane_is_gone(reason):
    """The router does not route this lane right now (demoted, paused or removed). Stop asking this run."""
    return bool(re.search(r"HTTP 404|unknown backend", reason or "", re.I))


def failure_kind(verdict, reason):
    if verdict == "accept":
        return None
    if verdict == "error":
        return "lane_error"
    for kind, rx in _KINDS:
        if rx.search(reason or ""):
            return kind
    return "other"


def _epoch(ts):
    try:
        return datetime.fromisoformat((ts or "").replace("Z", "+00:00")).timestamp()
    except ValueError:
        return None


def owed_history(ledger_root=None, relay_rows=False):
    """(set, target, backend) → {'answered': n, 'errors': n, 'router_errors': n} across every ledger
    ever committed. 'errors' is what may close a cell, so it counts a lane error only when the same
    lane answered SOMETHING within ALIVE_WINDOW_S of it: a lane that was dead at the time proved
    nothing about this target. Everything else lands in 'router_errors', kept for the record and
    never held against the cell. The ledger itself is not rewritten; this is only how it is read.
    Stage-2 relay rows are a separate count (relay_rows=True), so a relay try never closes a ladder cell."""
    import bisect
    hist = defaultdict(lambda: {"answered": 0, "errors": 0, "router_errors": 0})
    answered_at, lane_errors = defaultdict(list), []
    for f in Path(ledger_root or ROOT / "ledger").glob("**/*.jsonl"):
        for line in f.read_text().splitlines():
            try:
                r = json.loads(line)
            except ValueError:
                continue
            if str(r.get("try_mode") or "").startswith("fixer") or relay.is_relay(r) != relay_rows:
                continue                                 # a fixer row re-judges an old answer; it is nobody's try
            key = (r.get("target_set"), r.get("target"), r.get("backend"))
            if r.get("verdict") in ("accept", "reject"):
                hist[key]["answered"] += 1
                t = _epoch(r.get("ts"))
                if t is not None:
                    answered_at[r.get("backend")].append(t)
            elif r.get("verdict") == "error":
                if error_scope(r.get("reason")) == "lane":
                    lane_errors.append((key, _epoch(r.get("ts"))))
                else:
                    hist[key]["router_errors"] += 1
    for times in answered_at.values():
        times.sort()
    for key, t in lane_errors:
        times = answered_at.get(key[2], [])
        i = bisect.bisect_left(times, t - ALIVE_WINDOW_S) if t is not None else len(times)
        alive = t is not None and i < len(times) and times[i] <= t + ALIVE_WINDOW_S
        hist[key]["errors" if alive else "router_errors"] += 1
    return hist


def build_ladder_queue(sets, lanes_strongest_first, attempts, hist):
    """Every (set, target, lane, attempt_no) still owed, ordered so the whole ladder gets its
    first try before any cell gets a second: (attempt_no, rung, target) then lanes strongest
    first, interleaved across providers. A cell is done once it has attempt_no answers, or
    three lane errors (a lane that cannot answer this target is not asked forever). Only the
    lane's own errors count, and only from a time the lane was answering others: see
    owed_history. A router failure never closes a cell."""
    lanes_rr = interleave_by_provider(lanes_strongest_first)
    targets = sorted(((rung_of(s, n) + (s, n, d)) for s, d, names in sets for n in names),
                     key=lambda t: (t[1], sort_key(t[2], t[3])))        # rank, then the rung's own order
    work = deque()
    for a in range(1, attempts + 1):
        for rung, rank, tset, name, tdir in targets:
            for lane in lanes_rr:
                h = hist[(tset, name, lane["backend"])]
                if h["answered"] < a and h["errors"] < 3:
                    work.append((tset, tdir, name, rung, rank, lane, a))
    return work


def interleave_by_provider(lanes_in_order):
    """Round-robin across providers so consecutive calls never hammer one account.
    Twenty-eight Mistral lanes share one free-tier rate limit; walking them back to back is
    what benched half of sweep 1. Tier order is kept within each provider's queue."""
    queues = defaultdict(deque)
    for l in lanes_in_order:
        queues[l["provider"]].append(l)
    out = []
    while queues:
        for prov in list(queues):
            out.append(queues[prov].popleft())
            if not queues[prov]:
                del queues[prov]
    return out
