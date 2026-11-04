"""The 4B prover pilot (kumori #480, design reviewed 2026-11-04): does the Lean-only chain lift a small prover?

Pythagoras-Prover-4B answers a frozen set of miniF2F-test problems, 8 samples each, on Kaggle's free T4 x2 under its
own kernel (kumoriai/sparebrains-prover-pilot), so the production lane's scheduled runs never read these answers as
Goedel-8B's. Every answer is judged, none skipped after a success: raw is the kernel's verdict on the answer as
written; chain is tools/toolscore.py's full Lean-only chain on each raw reject (raw accepts kept, as the loop runs).

The read, frozen before any answer (DECISIONS 2026-11-04; Codex 20261104 rounds 1-2 on #480):
- population: the five strata math-L3, math-L4, math-L5, amc12, aime+imo of miniF2F-test (160 of 244 targets),
  equally weighted, 6 problems each by a fixed seed, chosen without reading any verdict;
- rescues R = problems solved by the chain and not raw. Regressions cannot happen (raw accepts are kept), so no
  sign-test p-value is claimed: R >= 5 is a practical pilot bar, reported with R/30 as the absolute lift;
- complete only when all 30 problems have 8 judged answers; otherwise "inconclusive", and the missing sample slots
  run in the next batch;
- cost per answer recorded (tokens, generation seconds, Lean and chain seconds); conclusions are about success at 8
  attempts, not efficiency.

    python3 tools/prover_pilot.py manifest                     # freeze the set (refuses to overwrite)
    python3 tools/prover_pilot.py build --dir K --hours 5      # the kernel for the missing slots
    python3 tools/prover_pilot.py judge --answers A            # judge every answer, append rows
    python3 tools/prover_pilot.py read                         # the frozen read
"""
import argparse, gzip, hashlib, json, sys, time
from collections import defaultdict
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))
from ladder import rung_of
from proof_text import PROOF_SEP

DIR = ROOT / "ledger" / "experiments" / "prover-4b-pilot"
MANIFEST, ROWS = DIR / "manifest.json", DIR / "judged.jsonl"
answers_file = lambda batch: DIR / f"answers-{batch}.jsonl.gz"     # Kaggle's raw answers, kept with the rows (Codex f2)
PUSHES = DIR / "pushes.jsonl"     # every pilot push, on main before its kernel goes out: the accounting's own evidence
MODEL = "Pythagoras-LM/Pythagoras-Prover-4B"
KERNEL_ID = "kumoriai/sparebrains-prover-pilot"
SEED = "prover-4b-pilot-2026-11-04"
STRATA = {"math-L3": ("math-L3",), "math-L4": ("math-L4",), "math-L5": ("math-L5",), "amc12": ("amc12",),
          "aime+imo": ("aime", "imo")}
PER_STRATUM, N, BAR = 6, 8, 5
PROMPT_NOTE = ("the kernel's PROMPT, Goedel's model-card proof-plan prompt; the Pythagoras-Prover-4B card's instruction "
               "is the same wording with different whitespace (Codex read the card, 2026-11-04); the model's own chat "
               "template is applied by the kernel")


def pick(names_by_stratum, seed=SEED, k=PER_STRATUM):
    """k per stratum, ordered by a hash of the seed and the name: no verdict is read."""
    key = lambda n: hashlib.sha256(f"{seed}:{n}".encode()).hexdigest()
    return {s: sorted(names, key=key)[:k] for s, names in sorted(names_by_stratum.items())}


def manifest(targets=ROOT / "targets" / "minif2f" / "test", out=MANIFEST):
    if Path(out).exists():
        sys.exit(f"{out} exists: the set is frozen")
    by = defaultdict(list)
    for f in sorted(Path(targets).glob("*.lean")):
        rung = rung_of("minif2f/test", f.stem)[0]
        for s, rungs in STRATA.items():
            if rung in rungs:
                by[s].append(f.stem)
    chosen = pick(by)
    probs = []
    for s, names in chosen.items():
        for n in names:
            text = (Path(targets) / f"{n}.lean").read_text()
            probs.append({"target_set": "minif2f/test", "target": n, "stratum": s, "rung": rung_of("minif2f/test", n)[0],
                          "statement_sha": hashlib.sha256(text.encode()).hexdigest()})
    rec = {"frozen_at": datetime.now(timezone.utc).isoformat(timespec="seconds"), "seed": SEED, "model": MODEL,
           "n": N, "sampling": {"max_tokens": 16000, "temperature": 1.0, "top_p": 0.95}, "prompt": PROMPT_NOTE,
           "population": {s: len(by[s]) for s in STRATA}, "per_stratum": PER_STRATUM, "bar": BAR, "problems": probs}
    Path(out).parent.mkdir(parents=True, exist_ok=True)
    Path(out).write_text(json.dumps(rec, indent=1) + "\n")
    return rec


def rows(path=ROWS):
    return [json.loads(l) for l in Path(path).read_text().splitlines() if l.strip()] if Path(path).exists() else []


def missing(man, done):
    """{(target_set, target): samples still owed}: N less the distinct judged answer ids per problem."""
    have = defaultdict(set)
    for r in done:
        have[(r["target_set"], r["target"])].add((r["batch"], r["sample"]))
    return {(p["target_set"], p["target"]): N - len(have[(p["target_set"], p["target"])]) for p in man["problems"]
            if N - len(have[(p["target_set"], p["target"])]) > 0}


def build(kernel_dir, man, done, batch, budget_h):
    """The pilot kernel: prover_kernel.py for the missing sample slots, under its own Kaggle id."""
    import prover
    owed = missing(man, done)
    probs = [{"target_set": ts, "target": t, "n": n, "statement": (ROOT / "targets" / ts / f"{t}.lean").read_text()}
             for (ts, t), n in sorted(owed.items())]
    if not probs:
        sys.exit("nothing owed: every problem has its 8 judged answers")
    prover.build(kernel_dir, None, batch, budget_h=budget_h, problems=probs, model=MODEL)
    meta = Path(kernel_dir) / "kernel-metadata.json"
    m = json.loads(meta.read_text())
    m.update(id=KERNEL_ID, title="sparebrains-prover-pilot")
    meta.write_text(json.dumps(m, indent=1))
    return len(probs), sum(p["n"] for p in probs)


def judge(answers, man, done, judge_text, chain, out=ROWS, deadline=None):
    """Every answer of a manifest problem judged, none skipped after a success: raw, then the chain on a raw reject.
    An answer id (batch, target, sample) already judged is skipped, so a rerun resumes. Each row is appended as it is
    judged; past `deadline` (time.monotonic()) nothing new starts, so the job publishes what it has (Codex f1)."""
    import prover
    keys = {(p["target_set"], p["target"]): p for p in man["problems"]}
    seen = {(r["batch"], r["target"], r["sample"]) for r in done}
    written = []
    for a in answers:
        k = (a["target_set"], a["target"])
        if k not in keys or (a["batch"], a["target"], a["sample"]) in seen:
            continue
        if deadline and time.monotonic() > deadline:
            break
        text = (ROOT / "targets" / k[0] / f"{k[1]}.lean").read_text()
        if hashlib.sha256(text.encode()).hexdigest() != keys[k]["statement_sha"]:
            sys.exit(f"{k[1]}: the statement changed since the manifest froze")
        prefix = text[:PROOF_SEP.search(text).end()]
        proof = prover.final_proof(a.get("text"), k[1])
        row = {"batch": a["batch"], "target_set": k[0], "target": k[1], "sample": a["sample"], "model": (a.get("config") or {}).get("model"),
               "tokens": a.get("tokens"), "finish": a.get("finish"), "gen_seconds": a.get("seconds"),
               "raw": "reject", "chain": "reject", "lean_seconds": 0.0, "chain_seconds": 0.0, "proof": proof is not None,
               "proof_text": proof}
        if proof:
            t = time.monotonic()
            r = judge_text(prefix + "\n" + proof)
            row["lean_seconds"] = round(time.monotonic() - t, 1)
            row["raw"] = "accept" if r["verdict"] == "accept" else "reject"
            if row["raw"] == "accept":
                row["chain"] = "accept"
            else:
                t = time.monotonic()
                c = chain(proof, prefix, r.get("output") or "")
                row["chain_seconds"] = round(time.monotonic() - t, 1)
                row["chain"] = c["c_verdict"]
                row["chain_final"] = c.get("final") if c["c_verdict"] == "accept" else None
        with open(out, "a") as f:
            f.write(json.dumps(row) + "\n")
        seen.add((a["batch"], a["target"], a["sample"]))
        written.append(row)
    return written


def accounted(pushes, done, store=answers_file):
    """None when a new pilot batch may be pushed, else why not. The evidence is the ledger's own record of every
    push (PUSHES, on main before the kernel went out), never Kaggle's reply, which cannot tell a missing kernel from
    a denied one (Codex 2026-11-04, three rounds). Each recorded batch must be void (its push failed and said so) or
    have its raw answers stored and every one of them judged."""
    void = {p["batch"] for p in pushes if p.get("void")}
    have = {(r["batch"], r["target"], r["sample"]) for r in done}
    for p in pushes:
        b = p["batch"]
        if p.get("void") or b in void:
            continue
        f = store(b)
        if not f.exists():
            return f"batch {b}: its answers are not in the ledger ({f.name}); run phase=judge first"
        owed = [a for a in (json.loads(l) for l in gzip.open(f, "rt") if l.strip())
                if (a["batch"], a["target"], a["sample"]) not in have]
        if owed:
            return f"batch {b}: {len(owed)} answers not judged yet; run phase=judge first"
    return None


def record_push(batch, void=None, path=None):
    """A push record, or a void record for a push a person confirmed never reached Kaggle. A batch id is recorded as
    pushed once: a reused id is refused, so one void can never clear two pushes (Codex f1); a void must name a pushed
    batch that is not void yet."""
    path = Path(path or PUSHES)
    prior = rows(path)
    pushed = {p["batch"] for p in prior if not p.get("void")}
    voided = {p["batch"] for p in prior if p.get("void")}
    if not void and (batch in pushed or batch in voided):
        sys.exit(f"batch id {batch} was already recorded: a push needs a new id")
    if void and (batch not in pushed or batch in voided):
        sys.exit(f"batch id {batch}: nothing pushed to void, or already void")
    path.parent.mkdir(parents=True, exist_ok=True)
    with open(path, "a") as f:
        f.write(json.dumps({"batch": batch, "at": datetime.now(timezone.utc).isoformat(timespec="seconds"),
                            **({"void": void} if void else {})}) + "\n")


def read(man, done):
    """The frozen read: per problem solved raw / by the chain over its first N judged answer ids, R, and the verdict."""
    by, ids, conflicts = defaultdict(list), {}, []
    for r in done:                           # one record per answer id; two that disagree make the read inconclusive (f3)
        i = (r["batch"], r["target_set"], r["target"], r["sample"])
        if i in ids:
            if (ids[i]["raw"], ids[i]["chain"]) != (r["raw"], r["chain"]):
                conflicts.append(list(i))
            continue
        ids[i] = r
        by[(r["target_set"], r["target"])].append(r)
    per = {}
    for p in man["problems"]:
        rs = sorted(by[(p["target_set"], p["target"])], key=lambda r: (r["batch"], r["sample"]))[:N]
        per[p["target"]] = {"stratum": p["stratum"], "answers": len(rs), "raw": any(r["raw"] == "accept" for r in rs),
                            "chain": any(r["chain"] == "accept" for r in rs)}
    complete = all(v["answers"] == N for v in per.values())
    rescues = sorted(t for t, v in per.items() if v["chain"] and not v["raw"])
    out = {"complete": complete, "problems": len(per), "solved_raw": sum(v["raw"] for v in per.values()),
           "solved_chain": sum(v["chain"] for v in per.values()), "rescues": rescues, "R": len(rescues),
           "absolute_lift": round(len(rescues) / len(per), 4) if per else None,
           "answers": sum(v["answers"] for v in per.values()),
           # costs over distinct answer ids, never their copies (Codex f4)
           "gen_seconds": round(sum(r.get("gen_seconds") or 0 for r in ids.values()), 1),
           "lean_seconds": round(sum(r.get("lean_seconds") or 0 for r in ids.values()), 1),
           "chain_seconds": round(sum(r.get("chain_seconds") or 0 for r in ids.values()), 1)}
    out["conflicts"] = conflicts
    out["read"] = ("inconclusive: conflicting records for one answer id" if conflicts else
                   "inconclusive: not every problem has 8 judged answers" if not complete else
                   f"the chain lifts the 4B at the pilot bar (R = {len(rescues)} >= {BAR})" if len(rescues) >= BAR else
                   f"under the pilot bar (R = {len(rescues)} < {BAR}): no claim")
    return out


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("cmd", choices=["manifest", "build", "judge", "read", "accounted", "record-push"])
    ap.add_argument("--max-minutes", type=float, default=230, help="judge: start nothing new after this")
    ap.add_argument("--void", help="record-push: why this batch's push failed (it never ran)")
    ap.add_argument("--dir")
    ap.add_argument("--answers")
    ap.add_argument("--hours", type=float)
    ap.add_argument("--batch", default=f"pilot4b-{datetime.now(timezone.utc):%Y%m%dT%H%M}")
    a = ap.parse_args(argv)
    if a.cmd == "manifest":
        print(json.dumps(manifest()["population"]))
        return 0
    man = json.loads(MANIFEST.read_text())
    if a.cmd == "accounted":
        why = accounted(rows(PUSHES), rows())
        print(why or "accounted: every recorded pilot batch is judged or void")
        return 1 if why else 0
    if a.cmd == "record-push":
        record_push(a.batch, a.void)
        return 0
    if a.cmd == "build":
        n, samples = build(a.dir, man, rows(), a.batch, a.hours)
        print(f"pilot kernel {a.batch}: {n} problems, {samples} samples owed")
        return 0
    if a.cmd == "judge":
        import lean_tools, toolscore
        names_ix = lean_tools.index()
        answers = [json.loads(l) for l in Path(a.answers).read_text().splitlines() if l.strip()]
        for b in {x["batch"] for x in answers}:          # the raw answers kept first, before any judging (f2)
            if not answers_file(b).exists():
                with gzip.open(answers_file(b), "wt") as f:
                    f.writelines(json.dumps(x) + "\n" for x in answers if x["batch"] == b)
        w = judge(answers, man, rows(), lean_tools.judge_text,
                  lambda proof, prefix, said: toolscore.run_chain(proof, prefix, said, names_ix, lean_tools),
                  deadline=time.monotonic() + 60 * a.max_minutes)
        print(f"judged {len(w)}: raw {sum(r['raw'] == 'accept' for r in w)} accepted, chain {sum(r['chain'] == 'accept' for r in w)}")
        return 0
    print(json.dumps(read(man, rows()), indent=1))
    return 0


if __name__ == "__main__":
    sys.exit(main())
