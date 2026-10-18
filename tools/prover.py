"""Stage 3, the prover lane (DECISIONS.md 2026-10-17): an open-weight Lean prover's answers, written on
Kaggle's free GPUs by tools/prover_kernel.py and judged here by tools/check.py, the same kernel every other
try faces. Recorded as its own try mode (`prover`), so no other number moves.

    python3 tools/prover.py next  --out DIR              # build the next Kaggle batch; prints its id, or nothing
    python3 tools/prover.py pending --answers FILE       # how many downloaded answers are not judged yet
    python3 tools/prover.py judge --answers FILE --max-minutes M

The prover was trained on Lean 4.9's mathlib and the judge pins v4.33.1, so names renamed since then fail;
a rejected answer gets the fixer's name repair and Lean's automation (the loop's free half) before it counts
as a miss, recorded as `fixer+loop` beside the raw `prover` row, as the retro does for cold tries.
"""
import argparse, hashlib, json, re, sys, time
from collections import Counter, defaultdict
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT), str(ROOT / "tools")]
from ladder import failure_kind, rung_of
from proof_text import FENCE, PROOF_SEP, extract_proof

RUNGS = ("amc12", "math-L5", "aime")      # the bar's 50 problems (DECISIONS.md 2026-10-17)
SAMPLES = 32
BACKEND = "kaggle-goedel-prover-v2-8b"
MODEL = "Goedel-LM/Goedel-Prover-V2-8B"
KERNEL_ID = "kumoriai/sparebrains-prover"
LOOP_MAX = 6                               # rejected answers per problem that get the loop's Lean-only pass
GOAL_SAMPLES = 8                           # tries per one-step goal in a goal batch (task #461)
# A lane is who wrote the answers. The judging below is shared: tools/leanstral.py hands its answers to the same
# judge, fixer and loop under its own lane (DECISIONS.md 2026-10-18).
PROVER = {"backend": BACKEND, "provider": "kaggle", "model": MODEL, "mode": "prover", "file": "prover"}


def prover_rows(ledger_root=ROOT / "ledger", lane=PROVER):
    rows = []
    for f in Path(ledger_root).glob("**/*.jsonl"):
        for line in f.open():
            if lane["backend"] in line:
                try:
                    r = json.loads(line)
                except ValueError:
                    continue
                if r.get("backend") == lane["backend"]:
                    rows.append(r)
    return rows


def judged(rows, mode="prover"):
    """(batch, set, target, sample) of every answer already judged, and (set, target) → answers judged."""
    keys = {(r.get("batch"), r["target_set"], r["target"], r.get("sample_no"), r.get("goal")) for r in rows
            if r.get("try_mode") == mode}
    per = Counter((s, t) for _, s, t, _, _ in keys)
    return keys, per


def todo(open_list, rows):
    """The bar's open problems that still owe samples, in the open list's order: [(target, samples owed)]."""
    _, per = judged(rows)
    out = []
    for t in sorted(open_list, key=lambda t: t["order"]):
        owed = SAMPLES - per[(t["target_set"], t["target"])]
        if t.get("rung") in RUNGS and owed > 0:
            out.append((t, owed))
    return out


def build(out_dir, work, batch, goals=False):
    """A Kaggle script kernel: prover_kernel.py with PROBLEMS and BATCH filled in, and its metadata. Public, like
    everything here: its code, log and answers are the generation half of the record (Andy, 2026-10-17)."""
    out = Path(out_dir)
    out.mkdir(parents=True, exist_ok=True)
    problems = [{"target_set": t["target_set"], "target": t["target"], "n": owed, "goal": t["goal"],
                 "statement": t["statement"]} if goals else
                {"target_set": t["target_set"], "target": t["target"], "n": owed,
                 "statement": (ROOT / "targets" / t["target_set"] / f"{t['target']}.lean").read_text()}
                for t, owed in work]
    src = (ROOT / "tools" / "prover_kernel.py").read_text()
    for old, new in (("PROBLEMS = []", "PROBLEMS = " + json.dumps(problems, ensure_ascii=False)),
                     ('BATCH = ""', f"BATCH = {json.dumps(batch)}")):
        assert src.count(old) == 1, old
        src = src.replace(old, new, 1)
    (out / "prover_kernel.py").write_text(src)
    (out / "kernel-metadata.json").write_text(json.dumps({
        "id": KERNEL_ID, "title": "sparebrains-prover", "code_file": "prover_kernel.py", "language": "python",
        "kernel_type": "script", "is_private": "false", "enable_gpu": "true", "enable_internet": "true",
        "machine_shape": "NvidiaTeslaT4", "dataset_sources": [], "model_sources": [], "competition_sources": [],
        "kernel_sources": []}, indent=1))
    return len(problems)


def goal_work(queue, open_keys, rows):
    """Goal-batch problems: queue entries whose problem is still open and whose goal has no tries yet."""
    tried = {r.get("goal") for r in rows if r.get("try_mode") == "goal-closer"}
    return [q for q in queue if (q["target_set"], q["target"]) in open_keys and q["goal"] not in tried]


def build_goals(out_dir, work, batch):
    """The same kernel as a problem batch; each entry's statement is the goal's own file, and `goal` comes back
    on every answer."""
    return build(out_dir, [({**q, "order": 0}, q["n"]) for q in work], batch, goals=True)


def final_proof(text, name):
    """The proof in the answer's last fenced block that states the theorem. The prover writes a plan, then a
    sketch with `sorry`, then the complete proof (canary, 2026-10-17); extract_proof alone takes the longest
    block, which can be the sketch."""
    blocks = [b for b in FENCE.findall(text or "") if f"theorem {name}" in b]
    return extract_proof("```lean\n" + blocks[-1] + "```", name) if blocks else None


def base_row(a, run_id, prefix, lane=PROVER):
    rung, rank = rung_of(a["target_set"], a["target"])
    cfg = a.get("config") or {}
    return {"ts": datetime.now(timezone.utc).isoformat(timespec="seconds"), "run_id": run_id, "batch": a["batch"],
            "target_set": a["target_set"], "target": a["target"], "rung": rung, "rung_rank": rank,
            "statement_sha": hashlib.sha256(prefix.encode()).hexdigest(),
            "backend": lane["backend"], "provider": lane["provider"], "model": cfg.get("model", lane["model"]),
            "quality_tier": "unknown", "tier_rank": -1, "attempt_no": a["sample"] + 1, "sample_no": a["sample"],
            "mode": lane["mode"],
            "request_config": {k: cfg.get(k) for k in ("max_tokens", "temperature", "top_p", "dtype", "gpus")},
            "inference": {"tokens": a.get("tokens"), "finish": a.get("finish")},
            "call_seconds": a.get("seconds"), "response_chars": len(a.get("text") or "")}


def to_judge(answers, rows, still_open=None, mode="prover"):
    """(set, target) → answers still to judge: not judged yet, on a problem the lane has not solved and
    that is still open. A problem stops at its first accept, so its later answers are never owed."""
    done_keys, _ = judged(rows, mode)
    solved = {(r["target_set"], r["target"]) for r in rows if r.get("verdict") == "accept"}
    by_problem = defaultdict(list)
    for a in answers:
        key = (a["target_set"], a["target"])
        if ((a["batch"], *key, a["sample"], a.get("goal")) not in done_keys and key not in solved
                and (still_open is None or key in still_open)):
            by_problem[key].append(a)
    return by_problem


def judge_answers(answers, rows, *, judge_text, fix, repair, record, run_id, deadline=None, still_open=None,
                  lane=PROVER):
    """Judge every answer still owed (to_judge). Stops a problem at its first accept. Returns a summary."""
    solved = set()
    stats = Counter()
    for key, items in to_judge(answers, rows, still_open, lane["mode"]).items():
        tset, name = key
        target_text = (ROOT / "targets" / tset / f"{name}.lean").read_text()
        prefix = target_text[:PROOF_SEP.search(target_text).end()]
        seen, misses = {}, []
        for a in sorted(items, key=lambda a: a["sample"]):
            if deadline and time.time() > deadline:
                stats["left_for_next_job"] += 1
                continue
            row = base_row(a, run_id, prefix, lane)
            row["try_mode"] = lane["mode"]
            proof = final_proof(a.get("text"), name)
            if not proof:
                row.update(verdict="reject", reason="no complete proof of the theorem in the answer", lean_seconds=0.0,
                           proof_sha=None)
                row["failure_kind"] = failure_kind("reject", row["reason"])
                record(row, a.get("text"), None, None, None)
                stats["no_proof"] += 1
                continue
            sha = hashlib.sha256(proof.encode()).hexdigest()
            candidate = prefix + "\n" + proof
            t = time.monotonic()
            if sha in seen:                           # the same proof again: the same verdict, no Lean run
                verdict, reason, out = seen[sha]
            else:
                r = judge_text(candidate)
                verdict, reason, out = r["verdict"], r.get("reason") or "", r.get("output") or ""
                seen[sha] = (verdict, reason, out)
            row.update(verdict=verdict, reason=reason[:300], failure_kind=failure_kind(verdict, reason),
                       lean_seconds=round(time.monotonic() - t, 1), proof_sha=sha)
            record(row, a.get("text"), proof, candidate, out)
            stats[verdict] += 1
            if verdict == "accept":
                solved.add(key)
                stats["solved"] += 1
                record.verified(tset, name, candidate)
                break
            misses.append((a, proof, out))
        if key in solved:
            continue
        for a, proof, out in misses[:LOOP_MAX]:      # the loop's free half: names, form, Lean's automation
            if deadline and time.time() > deadline:
                break
            fixed, fixes = fix(proof, out)
            cand, final = prefix + "\n" + fixed, None
            if fixes:
                r = judge_text(cand)
                final = cand if r["verdict"] == "accept" else None
                out = r.get("output") or out
            rep = {}
            if not final:
                try:
                    rep = repair(cand, prefix, out)
                except Exception as e:
                    rep = {"stopped": f"loop error: {type(e).__name__}"}
                final = rep.get("accepted")
            stats["loop_tried"] += 1
            if final:
                row = {**base_row(a, run_id, prefix, lane), "try_mode": "fixer+loop", "verdict": "accept", "fixes": fixes,
                       "reason": ("kernel accepted after the fixer (" + "+".join(fixes) + ")") if not rep else
                                 f"kernel accepted after Lean's automation closed {rep.get('closed_by_lean', 0)} failing step(s)",
                       "failure_kind": None, "lean_seconds": 0.0, "proof_sha": hashlib.sha256(final.encode()).hexdigest()}
                record(row, None, final[len(prefix):].lstrip("\n"), final, rep.get("lean_output"))
                record.verified(tset, name, final)
                solved.add(key)
                stats["solved_by_loop"] += 1
                break
    return dict(stats)


def judge_goals(answers, rows, goals, *, judge_text, record, run_id, deadline=None, still_open=None, lane=PROVER):
    """Goal-batch answers: each proof of `sb_goal` goes through goal_closer.close (the goal alone, then spliced
    into its sketches, then the whole problem). Try mode `goal-closer`, with the stage it reached. A problem
    stops at its first accept."""
    import goal_closer
    done_keys, _ = judged(rows, "goal-closer")
    solved = {(r["target_set"], r["target"]) for r in rows if r.get("verdict") == "accept"}
    stats = Counter()
    for a in sorted(answers, key=lambda a: (a["target_set"], a["target"], a["goal"], a["sample"])):
        key = (a["target_set"], a["target"])
        if key in solved or (a["batch"], *key, a["sample"], a["goal"]) in done_keys:
            continue
        if still_open is not None and key not in still_open:
            continue
        if deadline and time.time() > deadline:
            stats["left_for_next_job"] += 1
            continue
        g = goals.get(a["goal"])
        target_text = (ROOT / "targets" / key[0] / f"{key[1]}.lean").read_text()
        prefix = target_text[:PROOF_SEP.search(target_text).end()]
        row = {**base_row(a, run_id, prefix, lane), "try_mode": "goal-closer", "goal": a["goal"]}
        body = final_proof(a.get("text"), "sb_goal")
        if not g or not body:
            row.update(verdict="reject", stage="goal", reason="goal unknown to the queue" if not g else
                       "no complete proof of the goal in the answer", lean_seconds=0.0, proof_sha=None)
            row["failure_kind"] = failure_kind("reject", row["reason"])
            record(row, a.get("text"), None, None, None)
            stats["no_proof"] += 1
            continue
        t = time.monotonic()
        r = goal_closer.close(g, target_text, body, judge_text)
        row.update(verdict=r["verdict"], stage=r["stage"], reason=(r.get("output") or "")[:300],
                   failure_kind=failure_kind(r["verdict"], r.get("output") or ""),
                   lean_seconds=round(time.monotonic() - t, 1), proof_sha=hashlib.sha256(body.encode()).hexdigest())
        record(row, a.get("text"), body, r.get("candidate"), r.get("output"))
        stats[f"{r['verdict']}@{r['stage']}"] += 1
        if r["verdict"] == "accept":
            record.verified(*key, r["candidate"])
            solved.add(key)
            stats["solved"] += 1
    return dict(stats)


class Recorder:
    """Ledger rows to ledger/<set>/<lane file>-<batch>.jsonl, accepted proofs to verified/, transcripts to the site."""
    def __init__(self, batch, post=None, lane=PROVER):
        self.batch, self.post, self.lane = batch, post, lane

    def __call__(self, row, response, proof, candidate, lean_out):
        path = ROOT / "ledger" / row["target_set"] / f"{self.lane['file']}-{self.batch}.jsonl"
        path.parent.mkdir(parents=True, exist_ok=True)
        with path.open("a") as fh:
            fh.write(json.dumps(row) + "\n")
        if self.post:
            self.post({**row, "prompt": None, "response": response, "proof": proof, "candidate": candidate,
                       "lean_output": (lean_out or "")[-20000:]})

    def verified(self, tset, name, candidate):
        out = ROOT / "verified" / tset / name / f"{self.lane['backend']}.lean"
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(candidate)


BATCHES = ROOT / "ledger" / "prover-batches.jsonl"


def _iso(dt):
    return dt.isoformat(timespec="seconds") if dt else None


def batch_record(kout, batch, observed_at, answers=()):
    """One line per batch in ledger/prover-batches.jsonl: when it was pushed, when Kaggle gave it GPUs, when it
    finished, minutes queued and running, tokens per second. From the script's own timing.json when it has one
    (exact); otherwise from its log, whose times are seconds since the script started: the run length is exact,
    and the queue is an upper bound up to when this job first saw the batch complete. Written once per batch."""
    if BATCHES.exists() and any(json.loads(l).get("batch") == batch for l in BATCHES.read_text().splitlines() if l.strip()):
        return None
    kout = Path(kout)
    pushed = datetime.strptime(batch, "%Y%m%dT%H%M").replace(tzinfo=timezone.utc)
    rec = {"batch": batch, "pushed_at": _iso(pushed), "answers": len(answers),
           "tokens": sum(a.get("tokens") or 0 for a in answers)}
    t = kout / "timing.json"
    if t.exists():
        tm = json.loads(t.read_text())
        start = datetime.fromisoformat(tm["started_at"])
        end = datetime.fromisoformat(tm["finished_at"]) if tm.get("finished_at") else None
        rec.update(source="timing.json", started_at=tm["started_at"], finished_at=tm.get("finished_at"),
                   load_s=tm.get("load_s"), machine=tm.get("machine"), queued_min=round((start - pushed).total_seconds() / 60, 1),
                   ran_min=round((end - start).total_seconds() / 60, 1) if end else None)
    else:
        ran_s = 0.0
        for log in kout.glob("*.log"):
            for m in re.finditer(r'"time"\s*:\s*([0-9.]+)', log.read_text(errors="ignore")):
                ran_s = max(ran_s, float(m.group(1)))
        rec.update(source="log (run length exact; queue is an upper bound)", ran_min=round(ran_s / 60, 1),
                   observed_complete_at=_iso(observed_at),
                   queued_min_at_most=round(((observed_at - pushed).total_seconds() - ran_s) / 60, 1))
    if rec.get("ran_min") and rec["tokens"]:
        rec["tok_per_s"] = round(rec["tokens"] / (rec["ran_min"] * 60), 1)
    with BATCHES.open("a") as fh:
        fh.write(json.dumps(rec) + "\n")
    return rec


def read_answers(path):
    out = []
    for line in Path(path).read_text().splitlines():
        try:
            out.append(json.loads(line))
        except ValueError:
            pass
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("cmd", choices=["next", "pending", "judge", "batch-record"])
    ap.add_argument("--dir")
    ap.add_argument("--out")
    ap.add_argument("--answers")
    ap.add_argument("--max-minutes", type=float, default=300)
    ap.add_argument("--goals", action="store_true", help="next: a goal batch from ledger/goal-queue.json (task #461)")
    args = ap.parse_args()
    import relay
    if args.cmd == "next" and args.goals:
        import goal_closer
        goals = json.loads(goal_closer.QUEUE.read_text()) if goal_closer.QUEUE.exists() else []
        read = lambda s, t: (ROOT / "targets" / s / f"{t}.lean").read_text()
        open_keys = {(t["target_set"], t["target"]) for t in relay.fetch_json("/targets.json")["open"]}
        work = goal_work(goal_closer.queue(goals, read, GOAL_SAMPLES), open_keys, prover_rows())
        if not work:
            return 0
        batch = "goals-" + datetime.now(timezone.utc).strftime("%Y%m%dT%H%M")
        n = build_goals(args.out, work, batch)
        print(batch)
        print(f"goal batch {batch}: {n} goals, {n * GOAL_SAMPLES} samples", file=sys.stderr)
        return 0
    if args.cmd == "next":
        work = todo(relay.fetch_json("/targets.json")["open"], prover_rows())
        if not work:
            return 0
        batch = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M")
        n = build(args.out, work, batch)
        print(batch)
        print(f"batch {batch}: {n} problems, {sum(o for _, o in work)} samples", file=sys.stderr)
        return 0
    answers = read_answers(args.answers)
    if args.cmd == "batch-record":
        batch = answers[0]["batch"] if answers else None
        rec = batch_record(args.dir, batch, datetime.now(timezone.utc), answers) if batch else None
        print(json.dumps(rec) if rec else "batch already recorded")
        return 0
    open_now = {(t["target_set"], t["target"]) for t in relay.fetch_json("/targets.json")["open"]}
    if args.cmd == "pending":
        rows = prover_rows()
        goal_answers = [a for a in answers if a.get("goal")]
        if goal_answers:                             # a goal batch: owed until judged as goal-closer, or its problem closed
            done, _ = judged(rows, "goal-closer")
            solved = {(r["target_set"], r["target"]) for r in rows if r.get("verdict") == "accept"}
            print(sum(1 for a in goal_answers if (a["target_set"], a["target"]) in open_now
                      and (a["target_set"], a["target"]) not in solved
                      and (a["batch"], a["target_set"], a["target"], a["sample"], a["goal"]) not in done))
            return 0
        print(sum(len(v) for v in to_judge(answers, rows, open_now).values()))
        return 0
    import fixer, lean_tools, subgoals
    from utilities.kumori_api_client import init, sparebrains_attempt
    post = None
    try:
        init()
        post = sparebrains_attempt
    except Exception as e:
        print(f"site recording off ({type(e).__name__}); the ledger still gets every row", flush=True)
    names_ix = lean_tools.index()
    batch = answers[0]["batch"] if answers else "none"
    goal_answers = [a for a in answers if a.get("goal")]
    if goal_answers:                                 # a goal batch (task #461): the goal closer judges it
        import goal_closer
        goals = {g["sha"]: g for g in json.loads(goal_closer.QUEUE.read_text())}
        stats = judge_goals(goal_answers, prover_rows(), goals, judge_text=lean_tools.judge_text, record=Recorder(batch, post),
                            run_id=f"prover-{batch}", deadline=time.time() + 60 * args.max_minutes, still_open=open_now)
        print(json.dumps({"batch": batch, **stats}), flush=True)
        return 0
    stats = judge_answers(
        answers, prover_rows(), judge_text=lean_tools.judge_text,
        fix=lambda proof, out: fixer.fix(proof, out, *names_ix),
        repair=lambda cand, prefix, out: subgoals.repair(cand, prefix, out, ask=None, run_lean=lean_tools.run_lean,
                                                         judge_text=lean_tools.judge_text),
        record=Recorder(batch, post), run_id=f"prover-{batch}", deadline=time.time() + 60 * args.max_minutes,
        still_open=open_now)
    print(json.dumps({"batch": batch, **stats}), flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
