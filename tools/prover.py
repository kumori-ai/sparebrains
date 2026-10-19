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
KERNEL_ID_TPU = "kumoriai/sparebrains-prover-tpu"   # the same prover on Kaggle's TPU hours (task #479)
LOOP_MAX = 6                               # rejected answers per problem that get the loop's Lean-only pass
GOAL_SAMPLES = 8                           # tries per one-step goal in a goal batch (task #461)
# Task #433 (DECISIONS.md 2026-10-19): the prover alone and with a plain-math plan, paired. Power comes from the
# problems, not the tries (exact McNemar counts only the problems the arms disagree on), so every still-open bar
# problem at 4 tries an arm rather than a few problems at 32.
PLANS = ROOT / "ledger" / "plan-arm" / "plans.json"
PLAN_SAMPLES = 4
# The week's GPU hours, used exactly (Andy, 2026-10-19). Kaggle reports them itself (`kaggle quota`, CLI 2.2.4:
# GetAcceleratorQuotaStatistics, the call behind its settings page); the quota resets Saturday 00:00 UTC (Kaggle
# staff, product-feedback 173129) and can float above 30 h, so it is read, never assumed.
SESSION_H = 11.5                           # Kaggle ends a session at 12 h
MARGIN_H = 0.25                            # left unspent so a slow last chunk never meets the quota's end
MIN_BATCH_H = 1.0                          # under this, the model's load and one chunk do not fit: wait for the reset
PRIOR_SEC_PER_SAMPLE = 103.0               # batch 20261017T1830: 659.4 min for 384 answers; replaced once batches log more
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


def batch_hours(total_h, used_h, reserved_h=0.0):
    """Hours the next GPU batch may run: what the week has left, less the margin, at most one session; 0 when
    too little is left for the model to load and finish a chunk."""
    h = min(SESSION_H, total_h - used_h - reserved_h - MARGIN_H)
    return round(h, 2) if h >= MIN_BATCH_H else 0.0


def sec_per_sample():
    """Seconds of GPU session per answer over every GPU batch with a measured run, or the prior before any."""
    secs = n = 0
    if BATCHES.exists():
        for line in BATCHES.read_text().splitlines():
            r = json.loads(line)
            if r.get("ran_min") and r.get("answers") and not str(r.get("batch", "")).startswith("tpu"):
                secs, n = secs + 60 * r["ran_min"], n + r["answers"]
    return round(secs / n, 1) if n else PRIOR_SEC_PER_SAMPLE


def gpu_quota():
    """(total, used, reserved) GPU hours this week, from Kaggle (needs KAGGLE_API_TOKEN and kaggle>=2.2.4)."""
    from kaggle.api.kaggle_api_extended import KaggleApi
    api = KaggleApi()
    api.authenticate()
    q = api.quota_view().gpu_quota
    h = lambda d: d.total_seconds() / 3600 if d else 0.0
    return h(q.total_time_allowed), h(q.time_used), h(getattr(q, "time_reserved", None))


def build(out_dir, work, batch, goals=False, tpu=False, budget_h=None, problems=None):
    """A Kaggle script kernel: prover_kernel.py with PROBLEMS and BATCH filled in, and its metadata. Public, like
    everything here: its code, log and answers are the generation half of the record (Andy, 2026-10-17).
    `problems` passes ready entries (a plan batch's) instead of `work`."""
    out = Path(out_dir)
    out.mkdir(parents=True, exist_ok=True)
    problems = problems or [
        {"target_set": t["target_set"], "target": t["target"], "n": owed, "goal": t["goal"],
         "statement": t["statement"]} if goals else
        {"target_set": t["target_set"], "target": t["target"], "n": owed,
         "statement": (ROOT / "targets" / t["target_set"] / f"{t['target']}.lean").read_text()}
        for t, owed in work]
    src = (ROOT / "tools" / ("prover_kernel_tpu.py" if tpu else "prover_kernel.py")).read_text()
    fills = [("PROBLEMS = []", "PROBLEMS = " + json.dumps(problems, ensure_ascii=False)),
             ('BATCH = ""', f"BATCH = {json.dumps(batch)}")]
    if budget_h is not None and not tpu:          # the GPU kernel's session, sized to the week's hours left
        fills += [("BUDGET_S = 9 * 3600", f"BUDGET_S = {int(budget_h * 3600)}"),
                  ("SEC_PER_SAMPLE = 0.0", f"SEC_PER_SAMPLE = {sec_per_sample()}")]
    for old, new in fills:
        assert src.count(old) == 1, old
        src = src.replace(old, new, 1)
    (out / "prover_kernel.py").write_text(src)
    # machine_shape names the accelerator (Kaggle/kaggle-cli docs/kernels_metadata.md: "TpuV5E8 for TPU v5e-8");
    # enable_tpu alone ran the first TPU smoke on a 4-CPU machine (2026-10-18). No docker_image, and pinning "latest":
    # a pinned CPU/GPU image overrides the TPU VM (Kaggle staff on Kaggle/kaggle-cli#1197, 2026-09-17).
    accel = ({"enable_gpu": "false", "enable_tpu": "true", "machine_shape": "TpuV5E8", "docker_image_pinning_type": "latest"} if tpu else
             {"enable_gpu": "true", "machine_shape": "NvidiaTeslaT4"})
    (out / "kernel-metadata.json").write_text(json.dumps({
        "id": KERNEL_ID_TPU if tpu else KERNEL_ID, "title": "sparebrains-prover-tpu" if tpu else "sparebrains-prover",
        "code_file": "prover_kernel.py", "language": "python", "kernel_type": "script", "is_private": "false",
        "enable_internet": "true", **accel, "dataset_sources": [], "model_sources": [], "competition_sources": [],
        "kernel_sources": []}, indent=1))
    return len(problems)


def goal_work(queue, open_keys, rows):
    """Goal-batch problems: queue entries whose problem is still open and whose goal has no tries yet."""
    tried = {r.get("goal") for r in rows if r.get("try_mode") == "goal-closer"}
    return [q for q in queue if (q["target_set"], q["target"]) in open_keys and q["goal"] not in tried]


def build_goals(out_dir, work, batch, budget_h=None):
    """The same kernel as a problem batch; each entry's statement is the goal's own file, and `goal` comes back
    on every answer."""
    return build(out_dir, [({**q, "order": 0}, q["n"]) for q in work], batch, goals=True, budget_h=budget_h)


def with_plan(statement, plan):
    """The statement with the plan as a Lean comment just above the theorem (its docstring included), so the model
    card's prompt is unchanged and only the file the prover reads differs between the arms."""
    m = re.search(r"^(/--|theorem |lemma )", statement, re.M)
    note = ("/- A plan for this proof, in plain mathematics (drafted with Claude Opus; the idea only, no Lean):\n"
            + plan.strip().replace("-/", "- /") + "\n-/\n")
    return statement[:m.start()] + note + statement[m.start():]


def plan_work(doc, open_keys, read=lambda s, t: (ROOT / "targets" / s / f"{t}.lean").read_text()):
    """A plan batch's entries: for each plan on a still-open problem, the alone arm then the plan arm side by side,
    so the kernel's chunks of 2 and its budget stop always cut both arms of a problem together."""
    out = []
    for p in doc["plans"]:
        if (p["target_set"], p["target"]) not in open_keys:
            continue
        text = read(p["target_set"], p["target"])
        for arm, statement in (("alone", text), ("plan", with_plan(text, p["plan"]))):
            out.append({"target_set": p["target_set"], "target": p["target"], "n": PLAN_SAMPLES, "arm": arm,
                        "statement": statement})
    return out


def plan_owed(ledger_root=ROOT / "ledger"):
    """The plans file, while no plan-arm row carries its id; else None."""
    if not PLANS.exists():
        return None
    doc = json.loads(PLANS.read_text())
    done = any(doc["id"] in f.read_text() for f in (Path(ledger_root) / "plan-arm").glob("rows-*.jsonl"))
    return None if done else doc


def judge_plan(answers, *, judge_text, record, run_id, plans_id, read, out, still_open=None, lane=PROVER):
    """Each arm of each problem judged on its own, raw (no fixer, no loop: the same for both arms), stopping at that
    arm's first accept. Every judged answer is a measurement row (`out`); a first accept is also a try of its mode
    (`prover` or `prover+plan`), recorded and verified like any other. Returns per arm: solved and samples judged."""
    stats = {"alone": Counter(), "plan": Counter()}
    by = defaultdict(list)
    for a in answers:
        by[(a["target_set"], a["target"], a["arm"])].append(a)
    verified = set()
    for (tset, name, arm), items in sorted(by.items(), key=lambda kv: (kv[0][0], kv[0][1], kv[0][2])):
        text = read(tset, name)
        prefix = text[:PROOF_SEP.search(text).end()]
        for a in sorted(items, key=lambda a: a["sample"]):
            proof = final_proof(a.get("text"), name)
            r = judge_text(prefix + "\n" + proof) if proof else {"verdict": "reject", "reason": "no complete proof"}
            row = {**base_row(a, run_id, prefix, lane), "try_mode": "prover+plan" if arm == "plan" else "prover",
                   "arm": arm, "plans_id": plans_id, "verdict": r["verdict"], "reason": (r.get("reason") or "")[:300]}
            out(row)
            stats[arm]["samples"] += 1
            if r["verdict"] == "accept":
                stats[arm]["solved"] += 1
                if still_open is None or (tset, name) in still_open:
                    record(row, a.get("text"), proof, prefix + "\n" + proof, r.get("output"))
                    if (tset, name) not in verified:
                        record.verified(tset, name, prefix + "\n" + proof)
                        verified.add((tset, name))
                break
    return {k: dict(v) for k, v in stats.items()}


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
    pushed = datetime.strptime(batch[-13:], "%Y%m%dT%H%M").replace(tzinfo=timezone.utc)   # goals-, plan- prefixes
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
    ap.add_argument("cmd", choices=["next", "pending", "judge", "batch-record", "smoke-tpu", "hours"])
    ap.add_argument("--n", type=int, default=4, help="smoke-tpu: samples per problem")
    ap.add_argument("--dir")
    ap.add_argument("--out")
    ap.add_argument("--answers")
    ap.add_argument("--max-minutes", type=float, default=300)
    ap.add_argument("--goals", action="store_true", help="next: a goal batch from ledger/goal-queue.json (task #461)")
    ap.add_argument("--hours", type=float, help="next: the session's hours (from `hours`); the kernel stops before them")
    args = ap.parse_args()
    if args.cmd == "hours":                       # the next GPU batch's hours, from Kaggle's own quota; 0 = wait
        total, used, reserved = gpu_quota()
        h = batch_hours(total, used, reserved)
        print(h)
        print(f"GPU quota: {used:.2f} of {total:.2f} h used, {reserved:.2f} h reserved; next batch {h} h at "
              f"{sec_per_sample()} s an answer", file=sys.stderr)
        return 0
    import relay
    if args.cmd == "smoke-tpu":                   # a speed check on SOLVED problems only: no bar, no first solve to take
        solved = relay.fetch_json("/targets.json").get("solved") or []
        pick = [t for t in solved if t.get("rung") in RUNGS][:6]
        work = [({**t, "order": 0}, args.n) for t in pick]
        batch = "tpu-smoke-" + datetime.now(timezone.utc).strftime("%Y%m%dT%H%M")
        build(args.out, work, batch, tpu=True)
        print(batch)
        print(f"tpu smoke {batch}: {len(work)} solved problems x {args.n}", file=sys.stderr)
        return 0
    if args.cmd == "next":                        # a plan batch (task #433) goes before any other kind
        doc = plan_owed()
        work = plan_work(doc, {(t["target_set"], t["target"]) for t in relay.fetch_json("/targets.json")["open"]}) if doc else []
        if work:
            batch = f"plan-{doc['id']}-" + datetime.now(timezone.utc).strftime("%Y%m%dT%H%M")
            build(args.out, None, batch, budget_h=args.hours, problems=work)
            print(batch)
            print(f"plan batch {batch}: {len(work) // 2} problems x 2 arms x {PLAN_SAMPLES}", file=sys.stderr)
            return 0
    if args.cmd == "next" and args.goals:
        import goal_closer
        goals = json.loads(goal_closer.QUEUE.read_text()) if goal_closer.QUEUE.exists() else []
        read = lambda s, t: (ROOT / "targets" / s / f"{t}.lean").read_text()
        open_keys = {(t["target_set"], t["target"]) for t in relay.fetch_json("/targets.json")["open"]}
        work = goal_work(goal_closer.queue(goals, read, GOAL_SAMPLES), open_keys, prover_rows())
        if not work:
            return 0
        batch = "goals-" + datetime.now(timezone.utc).strftime("%Y%m%dT%H%M")
        n = build_goals(args.out, work, batch, budget_h=args.hours)
        print(batch)
        print(f"goal batch {batch}: {n} goals, {n * GOAL_SAMPLES} samples", file=sys.stderr)
        return 0
    if args.cmd == "next":
        work = todo(relay.fetch_json("/targets.json")["open"], prover_rows())
        if not work:
            return 0
        batch = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M")
        n = build(args.out, work, batch, budget_h=args.hours)
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
    plan_answers = [a for a in answers if a.get("arm")]
    plan_rows = ROOT / "ledger" / "plan-arm" / f"rows-{answers[0]['batch']}.jsonl" if plan_answers else None
    if args.cmd == "pending" and plan_answers:      # judged whole in one job: owed until its rows file exists
        print(0 if plan_rows.exists() else len(plan_answers))
        return 0
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
    if plan_answers:                                 # a plan batch (task #433): each arm judged on its own
        import headtohead
        doc = json.loads(PLANS.read_text())
        rows = []
        stats = judge_plan(plan_answers, judge_text=lean_tools.judge_text, record=Recorder(answers[0]["batch"], post),
                           run_id=f"prover-{answers[0]['batch']}", plans_id=doc["id"],
                           read=lambda s, t: (ROOT / "targets" / s / f"{t}.lean").read_text(), out=rows.append,
                           still_open=open_now)
        won = {(r["target"], r["arm"]) for r in rows if r["verdict"] == "accept"}
        names = {r["target"] for r in rows}
        only_plan = sorted(n for n in names if (n, "plan") in won and (n, "alone") not in won)
        only_alone = sorted(n for n in names if (n, "alone") in won and (n, "plan") not in won)
        plan_rows.parent.mkdir(parents=True, exist_ok=True)
        plan_rows.write_text("".join(json.dumps(r) + "\n" for r in rows))
        print(json.dumps({"batch": answers[0]["batch"], "problems": len(names), **stats, "only_plan": only_plan,
                          "only_alone": only_alone, "p": round(headtohead.sign_p(len(only_plan), len(only_alone)), 4)}),
              flush=True)
        return 0
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
