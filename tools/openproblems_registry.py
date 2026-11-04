"""C2 R5 (DECISIONS 2026-11-04, kumori #477): the registered pairs of an openproblems tool A/B, and who may run when.

One experiment lives in ledger/openproblems/experiments/<name>/ on main:
  manifest.json    6 pairs, each with its own frozen seed row and which arm goes first (3 and 3 by a fixed seed); the
                   lane, the evaluator commit, and the ledger snapshot (commit + digest) both arms read their inputs from
  dispatches.jsonl one line per arm run, pushed to main by the arm's job before it makes any ask (gate)
  selection.json   which run of each pair counts, decided from terminal rows alone before any outcome job (freeze)

    python3 tools/openproblems_registry.py manifest --experiment c2-r1 --lane L --seed-upto T --order-seed S --evaluator SHA
    python3 tools/openproblems_registry.py gate --registry DIR --pair p1 --arm on --attempt 1 --run-id N --write FILE
    python3 tools/openproblems_registry.py freeze --registry DIR
    python3 tools/openproblems_registry.py read --registry DIR

Codex reviewed the design: 20261104T085109300085Z DISAGREE (qualify could preview an arm's held-out folds; the
archive's inputs were not frozen), 20261104T085501122406Z AGREE.
"""
import argparse, hashlib, json, random, subprocess, sys
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
ARMS = {"on": {"parents": "archive", "repairs": 2}, "off": {"parents": "single", "repairs": -1}}
PAIRS, ATTEMPTS = 6, 2          # R5: 6 pair ids, a pair rerun at most once
COMMON = {"max_asks": 24, "rounds": 12, "feedback": "off"}


def rows_of(f):
    return [json.loads(l) for l in Path(f).read_text().splitlines() if l.strip()] if Path(f).exists() else []


def prior_rows(ledger_root, seed_upto):
    """The rows an experiment arm's prior and archive are built from (openproblems.py evolve, experiment mode)."""
    d = Path(ledger_root) / "openproblems"
    rows = [json.loads(l) for f in sorted(d.glob("evolve-*.jsonl")) for l in f.read_text().splitlines()]
    return [r for r in rows if r.get("at", "") < seed_upto]


def inputs_digest(rows):
    return hashlib.sha256("\n".join(sorted(json.dumps(r, sort_keys=True) for r in rows)).encode()).hexdigest()


def terminal_complete(rows):
    """C2 R4: exactly one terminal row, the last, with final complete."""
    ends = [r for r in rows if r.get("terminal")]
    return len(ends) == 1 and bool(rows) and rows[-1] is ends[0] and ends[0]["terminal"].get("final") == "complete"


def shakedown_ok(exp_dir, lane):
    """R6: some shakedown arm on this lane completed."""
    for f in sorted(Path(exp_dir).glob("evolve-*.jsonl")):
        rows = rows_of(f)
        if (rows and str(rows[0].get("experiment", "")).startswith("shakedown-")
                and (rows[0].get("frozen") or {}).get("lane") == lane and terminal_complete(rows)):
            return str(f.name)
    return None


def seed_pool(ledger_root, seed_upto):
    """Main-ledger rows that pass the bar against their own reference, one per distinct code, each resolvable by
    seed_source exactly as an arm will resolve it. Sorted by (file, round)."""
    import openproblems as op
    d = Path(ledger_root) / "openproblems"
    seen, out = set(), []
    for f in sorted(d.glob("evolve-*.jsonl")):
        for r in rows_of(f):
            if r.get("rescore") or not r.get("code") or r.get("round") is None or r.get("at", "") >= seed_upto:
                continue
            ref = (r.get("reference") or {}).get(op.METHOD)
            if not ref or not op.passes_bar(r, ref):
                continue
            h = op.code_sha(r["code"])
            if h in seen:
                continue
            try:
                _, sf = op.seed_source(ledger_root, f"ledger/openproblems/{f.name}:{r['round']}")
            except SystemExit:
                continue
            if sf["code_sha"] == h:
                seen.add(h)
                out.append(sf)
    return sorted(out, key=lambda s: (s["file"], s["round"]))


def make_manifest(ledger_root, experiment, lane, seed_upto, order_seed, evaluator, ledger_commit):
    exp_dir = Path(ledger_root) / "openproblems" / "experiments"
    shake = shakedown_ok(exp_dir, lane)
    if not shake:
        sys.exit(f"R6: no completed shakedown arm on {lane} under {exp_dir}")
    pool = seed_pool(ledger_root, seed_upto)
    if len(pool) < PAIRS:
        sys.exit(f"only {len(pool)} distinct bar-passing seed rows before {seed_upto}")
    seeds = random.Random(order_seed).sample(pool, PAIRS)
    first = ["on"] * 3 + ["off"] * 3
    random.Random(order_seed).shuffle(first)
    return {"experiment": experiment, "written": datetime.now(timezone.utc).isoformat(timespec="seconds"),
            "rule": "DECISIONS 2026-11-04 C2 amendment R5; read: DECISIONS 2026-11-03 C2", "lane": lane,
            "lane_shakedown": shake, "evaluator": evaluator, "ledger_commit": ledger_commit, "seed_upto": seed_upto,
            "inputs_digest": inputs_digest(prior_rows(ledger_root, seed_upto)), "order_seed": order_seed,
            "pool": len(pool), **COMMON, "arms": ARMS,
            "pairs": [{"id": f"p{i + 1}", "seed_from": s, "first": f} for i, (s, f) in enumerate(zip(seeds, first))]}


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def load(reg):
    reg = Path(reg)
    if not (reg / "manifest.json").exists():
        sys.exit(f"no manifest under {reg}")
    return json.loads((reg / "manifest.json").read_text()), rows_of(reg / "dispatches.jsonl")


def arm_file(reg, run_id):
    """An arm's rows: experiments/evolve-<run>.jsonl, the registry's parent folder."""
    return Path(reg).parent / f"evolve-{run_id}.jsonl"


def attempt_state(reg, disp, pair, attempt):
    """'none' | 'partial' (one arm dispatched) | 'complete' | 'invalid'. Called only while no arm job is live (the
    gate and freeze run in the serialized openproblems-exp group), so a dispatched arm without its file is dead."""
    got = {d["arm"]: d for d in disp if d["pair"] == pair and d["attempt"] == attempt}
    if not got:
        return "none"
    if len(got) < 2:
        return "partial"
    return "complete" if all(terminal_complete(rows_of(arm_file(reg, got[a]["run_id"]))) for a in ARMS) else "invalid"


def why_not(reg, pair, arm, attempt):
    """None when this arm may run now, else the reason (R5's order, one rerun, no run after the freeze)."""
    man, disp = load(reg)
    p = next((x for x in man["pairs"] if x["id"] == pair), None)
    if p is None or arm not in ARMS or attempt not in range(1, ATTEMPTS + 1):
        return f"not a registered arm: pair {pair}, arm {arm}, attempt {attempt}"
    if (Path(reg) / "selection.json").exists():
        return "the pairs are frozen (selection.json): no more arm runs"
    if any((d["pair"], d["arm"], d["attempt"]) == (pair, arm, attempt) for d in disp):
        return f"{pair} {arm} attempt {attempt} was already dispatched; a run is never repeated"
    other = next(a for a in ARMS if a != arm)
    if arm != p["first"] and not any((d["pair"], d["arm"], d["attempt"]) == (pair, other, attempt) for d in disp):
        return f"{pair} runs {p['first']} first: {other} attempt {attempt} has not been dispatched"
    if attempt == 2 and attempt_state(reg, disp, pair, 1) != "invalid":
        return f"{pair} attempt 2 needs attempt 1 INVALID, not {attempt_state(reg, disp, pair, 1)}"
    return None


def gate(reg, pair, arm, attempt, run_id, write):
    """Refuse, or write the dispatch line to `write` (the file publish.py appends to main's dispatches.jsonl)."""
    why = why_not(reg, pair, arm, attempt)
    if why:
        sys.exit(f"R5 gate: {why}")
    man, _ = load(reg)
    rec = {"pair": pair, "arm": arm, "attempt": attempt, "run_id": str(run_id), "manifest_sha": sha(Path(reg) / "manifest.json"),
           "at": datetime.now(timezone.utc).isoformat(timespec="seconds")}
    Path(write).parent.mkdir(parents=True, exist_ok=True)
    with open(write, "a") as fh:
        fh.write(json.dumps(rec) + "\n")
    return man, rec


def check_dispatch(reg, pair, arm, attempt, run_id):
    """evolve's check before any ask: main records this run for this arm, under this manifest. Returns the arm's
    settings: experiment, lane, seed_from spec and the frozen values."""
    man, disp = load(reg)
    mine = [d for d in disp if (d["pair"], d["arm"], d["attempt"]) == (pair, arm, attempt)]
    if len(mine) != 1 or mine[0]["run_id"] != str(run_id):
        sys.exit(f"R5: main has {len(mine)} dispatch records for {pair} {arm} attempt {attempt}, none for run {run_id}")
    if mine[0]["manifest_sha"] != sha(Path(reg) / "manifest.json"):
        sys.exit("R5: the manifest changed after this arm was dispatched")
    p = next(x for x in man["pairs"] if x["id"] == pair)
    return {"manifest": man, "seed_from": f"{p['seed_from']['file']}:{p['seed_from']['round']}", "pair": p,
            "settings": {"lane": man["lane"], "seed_upto": man["seed_upto"], "max_asks": man["max_asks"],
                         "rounds": man["rounds"], **ARMS[arm]}}


def freeze(reg):
    """R5: which run of each pair the read uses, from terminal rows only, written once before any outcome."""
    out = Path(reg) / "selection.json"
    if out.exists():
        sys.exit("selection.json exists: the selection is made once")
    man, disp = load(reg)
    sel = []
    for p in man["pairs"]:
        s1, s2 = attempt_state(reg, disp, p["id"], 1), attempt_state(reg, disp, p["id"], 2)
        if s1 == "complete":
            pick = 1
        elif s1 == "invalid" and s2 == "complete":
            pick = 2
        elif s1 == "invalid" and s2 == "invalid":
            pick = None
        else:
            sys.exit(f"{p['id']} is not settled (attempt 1 {s1}, attempt 2 {s2}): run its arms before the freeze")
        runs = {d["arm"]: d["run_id"] for d in disp if d["pair"] == p["id"] and d["attempt"] == pick} if pick else {}
        sel.append({"pair": p["id"], "attempt": pick, "status": "valid" if pick else "FAILED",
                    "files": {a: str(arm_file(reg, r).relative_to(Path(reg).parents[3])) for a, r in runs.items()}})
    rec = {"experiment": man["experiment"], "manifest_sha": sha(Path(reg) / "manifest.json"),
           "at": datetime.now(timezone.utc).isoformat(timespec="seconds"), "pairs": sel}
    out.write_text(json.dumps(rec, indent=1) + "\n")
    return rec


def selected_files(reg):
    """{evolve_file: (pair, arm)} for the selected runs; exits when nothing is frozen yet."""
    f = Path(reg) / "selection.json"
    if not f.exists():
        sys.exit(f"R5: no selection.json under {reg}: outcomes wait for the freeze")
    return {path: (p["pair"], arm) for p in json.loads(f.read_text())["pairs"] for arm, path in p["files"].items()}


def read(reg, receipts):
    """The registered read: each selected pair's outcome receipts through pair_read; a FAILED pair is a non-win
    (no invented delta) and any FAILED pair means no claim."""
    import openproblems as op
    sel = json.loads((Path(reg) / "selection.json").read_text())
    files = selected_files(reg)
    by_file = {}
    for r in receipts:
        if r.get("evolve_file") in files:
            by_file.setdefault(r["evolve_file"], []).append(r)
    chosen, missing = [], []
    for f in files:
        rs = by_file.get(f, [])
        if not rs or len({r["outcome"] for r in rs}) != 1:
            missing.append(f"{f}: {len(rs)} receipts" + (" that disagree" if rs else ""))
        elif rs[0].get("arm") != ARMS[files[f][1]]["parents"]:
            missing.append(f"{f}: receipt arm {rs[0].get('arm')}, selected as {files[f][1]}")
        else:
            chosen.append(rs[0])
    failed = [p["pair"] for p in sel["pairs"] if p["status"] == "FAILED"]
    if missing:
        return {"read": "INCOMPLETE: every selected arm needs its outcome", "missing": missing, "failed": failed}
    out = op.pair_read(chosen)
    if out.get("invalid"):
        return {**out, "failed": failed}
    pairs = out["pairs"]
    wins, ties = sum(d > 0 for d in pairs), sum(d == 0 for d in pairs)
    n = len(pairs) - ties + len(failed)
    from math import comb
    p = sum(comb(n, k) for k in range(wins, n + 1)) / 2 ** n if n else 1.0
    total = len(pairs) + len(failed)
    read_ = ("INVALID: the registered read needs exactly %d pairs, not %d" % (PAIRS, total) if total != PAIRS
             else "tools lift" if wins == PAIRS and p <= 0.05 else "no claim")
    return {"pairs": pairs, "failed": failed, "wins": wins, "ties": ties, "n": n, "p": round(p, 4), "read": read_}


def git_head(path):
    r = subprocess.run(["git", "-C", str(path), "rev-parse", "HEAD"], capture_output=True, text=True)
    return r.stdout.strip() if r.returncode == 0 else None


def main():
    sys.path.insert(0, str(Path(__file__).parent))
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("cmd", choices=["manifest", "gate", "freeze", "read"])
    ap.add_argument("--registry", help="ledger/openproblems/experiments/<experiment> in a checkout of main")
    ap.add_argument("--experiment")
    ap.add_argument("--lane")
    ap.add_argument("--seed-upto")
    ap.add_argument("--order-seed")
    ap.add_argument("--evaluator", help="the full commit SHA every arm and outcome runs on")
    ap.add_argument("--ledger-root", default=str(ROOT / "ledger"))
    ap.add_argument("--pair")
    ap.add_argument("--arm", choices=list(ARMS))
    ap.add_argument("--attempt", type=int)
    ap.add_argument("--run-id")
    ap.add_argument("--write", help="gate: the dispatches.jsonl to append the record to")
    a = ap.parse_args()
    if a.cmd == "manifest":
        if not (a.evaluator and len(a.evaluator) == 40):
            sys.exit("--evaluator: a full 40-hex commit")
        reg = Path(a.ledger_root) / "openproblems" / "experiments" / a.experiment
        if (reg / "manifest.json").exists():
            sys.exit(f"{reg}/manifest.json exists: a manifest is written once")
        man = make_manifest(a.ledger_root, a.experiment, a.lane, a.seed_upto, a.order_seed, a.evaluator,
                            git_head(Path(a.ledger_root).parent))
        reg.mkdir(parents=True)
        (reg / "manifest.json").write_text(json.dumps(man, indent=1) + "\n")
        print(json.dumps({k: man[k] for k in ("experiment", "lane", "ledger_commit", "pool")}
                         | {"pairs": [(p["id"], p["first"], p["seed_from"]["file"], p["seed_from"]["round"]) for p in man["pairs"]]}))
    elif a.cmd == "gate":
        man, rec = gate(a.registry, a.pair, a.arm, a.attempt, a.run_id, a.write)
        print(json.dumps({"ledger_commit": man["ledger_commit"], "lane": man["lane"], **rec}))
    elif a.cmd == "freeze":
        print(json.dumps(freeze(a.registry)))
    elif a.cmd == "read":
        exp = Path(a.registry).parent
        print(json.dumps(read(a.registry, [json.loads(f.read_text()) for f in sorted(exp.glob("outcome-*.json"))]), indent=1))
    return 0


if __name__ == "__main__":
    sys.exit(main())
