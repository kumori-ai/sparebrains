"""A free lane writes a repair pass (DECISIONS.md 2026-10-28, rules written before it runs): can a Kumori router lane
write python that turns stored rejects of one failure class our chain turns 0 of? The writer sees the class, the
contract `repair(proof, lean_output) -> proof`, our pass for that class as the thing to beat, and examples from the
TUNE half only. Its code runs only in the candidate container (tools/sandbox, gVisor, no network); each repaired
proof is judged by the kernel, and only rows the existing chain already rejected (the replay's `on` arm) count, so
no accept the tools already had is ever the pass's credit (the chain turns 6 of 44 unknown_name tune rejects
itself; the residual 38 is this experiment's whole cohort, Codex f1 2026-10-28). Kept at `keep_at` tune turns; a kept pass runs once on
the report half, and the report half's count with its Wilson interval is all that may be claimed.

    python3 tools/lane_repair.py --class unknown_name --lanes requesty-leanstral-1-5,mistral-codestral-latest --rounds 12   # CI only
    python3 tools/lane_repair.py --class unknown_name --count                                      # what it would score
"""
import argparse, hashlib, json, os, subprocess, sys, tempfile, time
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT), str(ROOT / "tools")]
from proof_text import PROOF_SEP, extract_proof
from toolscore import problem_half, wilson95

OUT = ROOT / "ledger" / "lane-repair"
KEEP_AT, REPAIRS, EXAMPLES, MAX_ASKS = 3, 2, 8, 12
OUR_PASS = {"unknown_name": ("fixer.closest_name + fixer.fix names pass", "closest_name"),
            "lean3_syntax": ("fixer.lean3_to_4", "lean3_to_4"),
            "unsolved_goals": ("subgoals.repair (holes and Lean's automation)", "repair")}
CONTRACT = ("def repair(proof: str, lean_output: str) -> str: the proof body as the model wrote it (after the "
            "theorem's `:= by`), and Lean's error output on it; return the repaired body, or the input unchanged. "
            "Standard library only, no network, no files, under 2 s per proof.")


def proof_of(r):
    return extract_proof(r.get("response") or "", r["target"])


def examples(cohort, cls, half, n=EXAMPLES):
    """Up to n (proof, Lean output) pairs of the class from the TUNE half only, the writer's whole view of the data."""
    out = []
    for r in cohort:
        if r.get("failure_kind") != cls or r.get("verdict") != "reject" or half(r["target_set"], r["target"]) != "tune":
            continue
        p = proof_of(r)
        if p:
            out.append({"id": r["id"], "target": r["target"], "proof": p, "lean_output": r.get("reason") or ""})
        if len(out) == n:
            break
    return out


def items(cohort, cls, still_rejected, half, which="tune"):
    """The rows the pass is scored on: the class's rejects on one half that the existing chain still rejects."""
    out = []
    for r in cohort:
        if (r.get("failure_kind") == cls and r.get("verdict") == "reject" and r["id"] in still_rejected
                and half(r["target_set"], r["target"]) == which):
            p = proof_of(r)
            if p:
                out.append({"id": r["id"], "target_set": r["target_set"], "target": r["target"], "proof": p,
                            "lean_output": r.get("reason") or ""})
    return out


def our_pass_source(cls):
    import fixer, subgoals
    name = OUR_PASS.get(cls, (None, None))[1]
    import inspect
    for mod in (fixer, subgoals):
        if name and hasattr(mod, name):
            return inspect.getsource(getattr(mod, name))
    return "(no pass of ours targets this class yet)"


def brief(cls, exs, ours):
    shown = "\n\n".join(f"Example {i + 1}, Lean said: {e['lean_output'][:300]}\nProof body:\n```lean4\n{e['proof']}```"
                        for i, e in enumerate(exs))
    return (f"You are writing a repair pass for Lean 4 (Mathlib) proofs that a free model wrote and the kernel "
            f"rejected with failure class `{cls}`. Write one python function:\n\n{CONTRACT}\n\n"
            f"The pass we have today for this class, the thing to beat (it turns none of these):\n```python\n{ours}\n```\n\n"
            f"Rejected proofs of this class and what Lean said:\n\n{shown}\n\n"
            "Reply with one ```python block defining repair(). Be specific to what Lean said; a pass that returns the "
            "input unchanged on every example is a miss.")


def extract_code(text):
    import re
    blocks = [b for b in re.findall(r"```python\n(.*?)```", text or "", re.S) if "def repair(" in b]
    return blocks[-1] if blocks else None


def container_runner(code, its, image="sb-candidate", timeout=600):
    """The candidate on `its` in its own container (openproblems.docker_cmd's envelope): JSON lines in, JSON lines
    out, nothing of ours imported there. Raises with the container's stderr tail on a nonzero exit."""
    rt = os.environ.get("SB_RUNTIME")
    with tempfile.TemporaryDirectory() as d:
        cand = Path(d) / "cand.py"
        cand.write_text(code)
        os.chmod(d, 0o755); os.chmod(cand, 0o644)
        entry = ROOT / "tools" / "sandbox" / "repair_entry.py"
        cmd = ["docker", "run", "--rm", "-i", *(["--runtime", rt] if rt else []), "--network", "none", "--read-only",
               "--tmpfs", "/tmp:rw,size=256m,mode=1777", "--memory", "2g", "--memory-swap", "2g", "--cpus", "2",
               "--pids-limit", "128", "--cap-drop", "ALL", "--security-opt", "no-new-privileges", "--log-driver", "none",
               "--user", "65534:65534", "-e", "HOME=/tmp",
               "--mount", f"type=bind,src={cand},dst=/app/cand.py,readonly",
               "--mount", f"type=bind,src={entry},dst=/app/repair_entry.py,readonly",
               image, "python", "-I", "/app/repair_entry.py", "/app/cand.py"]
        feed = "".join(json.dumps({"id": it["id"], "proof": it["proof"], "lean_output": it["lean_output"]}) + "\n" for it in its)
        proc = subprocess.Popen(cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        import threading
        err_tail = {"text": ""}
        def drain_err():
            for line in proc.stderr:
                err_tail["text"] = (err_tail["text"] + line)[-1500:]
        threading.Thread(target=drain_err, daemon=True).start()
        try:
            proc.stdin.write(feed)
            proc.stdin.close()
        except BrokenPipeError:
            pass
        try:
            out = read_bounded(proc.stdout, MAX_OUT_BYTES, deadline=time.time() + timeout)
        except Exception:
            proc.kill()
            proc.wait()
            raise
        rc = proc.wait(timeout=30)
        if rc != 0:
            raise RuntimeError(err_tail["text"] or f"exit {rc}")
        return validate_output(its, parse_output(out))


def read_bounded(stream, cap, deadline=None):
    """Read a candidate's stdout while it streams, never past `cap` bytes or `deadline`: the host's memory is not the
    candidate's to spend (Codex f3, 2026-10-28)."""
    chunks, size = [], 0
    while True:
        if deadline and time.time() > deadline:
            raise RuntimeError("candidate ran past its deadline")
        chunk = stream.read(65536)
        if not chunk:
            return "".join(chunks)
        size += len(chunk)
        if size > cap:
            raise RuntimeError(f"output past {cap:,} bytes")
        chunks.append(chunk)


def parse_output(text):
    got = {}
    for line in text.splitlines():
        if line.strip():
            o = json.loads(line)
            if o["id"] in got:
                raise ValueError(f"id {o['id']} answered twice")
            got[o["id"]] = o["proof"]
    return got


MAX_PROOF_CHARS, MAX_OUT_BYTES = 20_000, 4_000_000


def validate_output(its, got):
    """The trusted side of the protocol: every id answered once, no id we did not send, every proof a bounded string.
    Anything else is the candidate's failure (raised), never silently taken."""
    want = {it["id"] for it in its}
    if set(got) - want:
        raise ValueError(f"output names ids not sent: {sorted(set(got) - want)[:5]}")
    if want - set(got):
        raise ValueError(f"output misses {len(want - set(got))} of {len(want)} ids")
    for i, v in got.items():
        if not isinstance(v, str):
            raise ValueError(f"proof for {i} is {type(v).__name__}, not str")
        if len(v) > MAX_PROOF_CHARS:
            raise ValueError(f"proof for {i} is {len(v):,} chars (cap {MAX_PROOF_CHARS:,})")
    return got


def screen(code, exs, runner):
    """None when the pass runs on the examples and changes at least one; else why (a traceback or 'no change')."""
    try:
        got = runner(code, exs)
    except Exception as e:
        return f"{type(e).__name__}: {e}"[-1500:]
    if all(got.get(e["id"], e["proof"]) == e["proof"] for e in exs):
        return "no change on any example"
    return None


def problems(its):
    return {(it["target_set"], it["target"]) for it in its}


def score(code, its, runner, judge, prefix_of, deadline=None):
    """Rows turned: a repaired proof the kernel accepts under the target's own prefix. Unchanged proofs are not judged
    (the chain already rejected them). Past `deadline` the rest is left unjudged and named (pending, never a miss)."""
    got = validate_output(its, runner(code, its))
    turned, pending = [], []
    for it in its:
        new = got.get(it["id"])
        if not new or new == it["proof"]:
            continue
        if deadline and time.time() > deadline:
            pending.append(it["id"])
            continue
        if judge(prefix_of(it["target_set"], it["target"]) + "\n" + new)["verdict"] == "accept":
            turned.append(it["id"])
    return turned, pending


def half_result(its, turned, pending):
    """Attempt counts are descriptive; the interval is over distinct problems (a problem's repeated attempts are
    one observation, Codex f2 2026-10-28), as tools/replay.py reports."""
    by_id = {it["id"]: (it["target_set"], it["target"]) for it in its}
    probs, hit = problems(its), {by_id[i] for i in turned}
    lo, hi = wilson95(len(hit), len(probs)) if probs else (0.0, 0.0)
    return {"turned": len(turned), "n": len(its), "ids": turned, "pending": pending,
            "problems_turned": len(hit), "problems": len(probs), "wilson95_problems": [lo, hi]}


REFUSED = ("is benched", "rate limit", "spent its share", "is gated", "held_for_others")


def refused(reply):
    return not isinstance(reply, str) and any(w in str(reply.get("error", "")) for w in REFUSED)


def run(cls, writers, cohort, still_rejected, half, runner, judge, prefix_of, rounds=MAX_ASKS, keep_at=KEEP_AT,
        repairs=REPAIRS, log=lambda s: None, max_minutes=None, sink=lambda row: None):
    """`writers`: [(lane, ask)] in preference order; a refused ask (the router benched or gated the lane) moves to the
    next lane without spending a round, and a round where every writer refused is one row and the end of the run.
    Every row goes to `sink` the moment it is complete (Codex f5: a later crash loses nothing earlier)."""
    deadline = time.time() + 60 * max_minutes if max_minutes else None

    def ask_any(prompt):
        for lane, ask in writers:
            reply = ask(prompt)
            if not refused(reply):
                return lane, reply
        return None, reply
    exs = examples(cohort, cls, half)
    tune, report = items(cohort, cls, still_rejected, half, "tune"), items(cohort, cls, still_rejected, half, "report")
    ours = our_pass_source(cls) if cls in OUR_PASS else "(no pass of ours targets this class yet)"
    rows, asks, last = [], 0, None

    def emit(row):
        rows.append(row)
        sink(row)
        log(json.dumps({k: v for k, v in row.items() if k not in ("code", "tune_ids", "report_ids")})[:400])

    while asks < rounds:
        if deadline and time.time() > deadline:
            emit({"at": datetime.now(timezone.utc).isoformat(timespec="seconds"), "class": cls, "writer": None,
                  "round": len(rows), "pending": f"deadline after {asks} asks"})
            break
        prompt = brief(cls, exs, ours)
        if last is not None:
            prompt += ("\n\nYour last attempt " + (f"crashed: {last['error'][-800:]}" if "error" in last
                       else f"turned {last['tune_turned']} of {last['tune_n']} rejects on our side") + ". Do better.")
        t = time.time()
        writer, reply = ask_any(prompt)
        if writer is None:
            emit({"at": datetime.now(timezone.utc).isoformat(timespec="seconds"), "class": cls, "writer": None,
                  "round": len(rows), "refused": f"every writer refused: {reply.get('error')}"[:300]})
            break
        ask = dict(writers)[writer]
        asks += 1
        row = {"at": datetime.now(timezone.utc).isoformat(timespec="seconds"), "class": cls, "writer": writer,
               "round": len(rows), "ask_s": round(time.time() - t, 1), "repair_asks": 0, "screen_errors": []}
        code = extract_code(reply) if isinstance(reply, str) else None
        if code is None:
            row["error"] = "no code in the reply" if isinstance(reply, str) else f"no reply: {reply.get('error')}"
        else:
            while True:
                why = screen(code, exs, runner)
                if why is None or row["repair_asks"] >= repairs or asks >= rounds:
                    break
                row["screen_errors"].append(why[-300:])
                reply = ask(f"Your repair pass failed on the examples: {why[-800:]}\n\nThe code:\n```python\n{code}```\n"
                            "Reply with the fixed ```python block.")
                asks += 1
                row["repair_asks"] += 1
                fixed = extract_code(reply) if isinstance(reply, str) else None
                if fixed is None:
                    break
                code = fixed
            row["pass_sha"] = hashlib.sha256(code.encode()).hexdigest()
            row["code"] = code
            if why is not None:
                row["error"], row["kept"] = "screen: " + why[-300:], False
            else:
                try:
                    turned, pend = score(code, tune, runner, judge, prefix_of, deadline)
                except Exception as e:
                    turned, pend, row["error"] = [], [], f"score: {type(e).__name__}: {e}"[-500:]
                t_res = half_result(tune, turned, pend)
                row.update(tune_turned=t_res["turned"], tune_n=t_res["n"], tune_ids=turned, tune_pending=pend,
                           tune_problems_turned=t_res["problems_turned"], tune_problems=t_res["problems"])
                row["kept"] = len(turned) >= keep_at and not pend       # a cut-off tune run decides nothing
                if row["kept"]:                                          # once, the only claim; every kept pass published
                    try:
                        rep, rpend = score(code, report, runner, judge, prefix_of, deadline)
                        r_res = half_result(report, rep, rpend)
                        row.update(report_turned=r_res["turned"], report_n=r_res["n"], report_ids=rep, report_pending=rpend,
                                   report_problems_turned=r_res["problems_turned"], report_problems=r_res["problems"],
                                   wilson95=r_res["wilson95_problems"])
                    except Exception as e:                                # the row says so; earlier rows are already out
                        row["error"] = f"report: {type(e).__name__}: {e}"[-500:]
        emit(row)
        last = row
    return rows


def still_rejected_by_tools():
    """Attempt ids the replay's `on` arm (today's tools) still rejects, from ledger/replay/results-*.jsonl."""
    import replay
    ids = set()
    for r in replay.load_results():
        if r.get("arm") == "on" and r.get("verdict") == "reject":
            ids.add(int(r["attempt_id"]))
    return ids


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--class", dest="cls", required=True, choices=sorted(OUR_PASS))
    ap.add_argument("--lanes", help="the writers, Kumori router lanes in preference order, comma-separated")
    ap.add_argument("--rounds", type=int, default=MAX_ASKS)
    ap.add_argument("--count", action="store_true", help="print the tune and report counts and stop (no model, no Lean)")
    ap.add_argument("--out", default=None)
    ap.add_argument("--max-minutes", type=float, default=300, help="overall deadline; unjudged work is recorded as pending")
    a = ap.parse_args(argv)
    import replay
    cohort = [dict(r, id=int(r["id"])) for r in replay.load_cohort()]
    cohort, _ = replay.eligible(cohort)
    still = still_rejected_by_tools()
    tune, report = items(cohort, a.cls, still, problem_half, "tune"), items(cohort, a.cls, still, problem_half, "report")
    print(f"{a.cls}: {len(tune)} tune rejects the tools still reject, {len(report)} report; "
          f"{len(examples(cohort, a.cls, problem_half))} examples for the writer", flush=True)
    if a.count:
        return 0
    if not a.lanes:
        sys.exit("--lanes names the writers")
    import decompose, lean_tools
    writers = [(lane, decompose.router_ask(lane)[0]) for lane in a.lanes.split(",") if lane.strip()]
    prefix_of = lambda s, t: (lambda text: text[:PROOF_SEP.search(text).end()])((ROOT / "targets" / s / f"{t}.lean").read_text())
    run_id = os.environ.get("GITHUB_RUN_ID") or datetime.now(timezone.utc).strftime("local-%Y%m%dT%H%M%S")
    out = Path(a.out) if a.out else OUT / f"{a.cls}-{run_id}.jsonl"
    out.parent.mkdir(parents=True, exist_ok=True)
    def sink(row):
        with out.open("a") as fh:
            fh.write(json.dumps(row, ensure_ascii=False) + "\n")
    rows = run(a.cls, writers, cohort, still, problem_half, container_runner, lean_tools.judge_text, prefix_of,
               rounds=a.rounds, log=lambda s: print(s, flush=True), max_minutes=a.max_minutes, sink=sink)
    kept = [r for r in rows if r.get("kept")]
    each = "; ".join(f"{r['writer']} r{r['round']}: report {r.get('report_problems_turned', '?')} of {r.get('report_problems', '?')} problems"
                     for r in kept)                       # every kept pass, its own held-out result; no winner (Codex f6)
    print(f"{a.cls}: {len(rows)} rows, {len(kept)} kept" + (f"; {each}" if kept else "; a miss"))
    return 0


if __name__ == "__main__":
    sys.exit(main())
