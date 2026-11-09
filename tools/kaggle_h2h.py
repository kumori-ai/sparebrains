"""The Kaggle head-to-head (DECISIONS.md 2026-11-08): the skeleton pilot's manifest generated on Kaggle's free GPUs from
Mistral's open Ministral 3 3B checkpoint, because the router lane (mistral-ministral-3b-2512) has 150 calls a day and
the pilot needs 1,440 (run 42496660867, refused by lane_budget before any call). Judged here, raw: every sample, no
fixer, no loop, nothing credited to a try series or verified/.

The lane is the checkpoint's own (kaggle-ministral-3-3b-instruct-2512), kept apart from the router lane's series: the
same weights in fp16 on vLLM are not shown equal to Mistral's API; both arms share one copy, so the within-run comparison
holds. Every sample has an id <manifest>/<target_set>/<target>/<arm>/<index> and its prompt's sha256; a target is paired
only when all its samples are present and judged; a batch the budget trimmed reads complete false. Codex
20261108T161803773335Z (DISAGREE: completeness and the prover path), 20261108T162104656262Z (AGREE).

    python3 tools/kaggle_h2h.py build --manifest ledger/headtohead/manifest-...-kaggle-....json --out DIR [--smoke]
    python3 tools/kaggle_h2h.py judge --manifest ... --answers answers.jsonl --out ledger/headtohead/kaggle-B.jsonl [--smoke]
"""
import argparse, hashlib, json, sys
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT), str(ROOT / "tools")]
import headtohead as h
from proof_text import PROOF_SEP, extract_proof

LANE = "kaggle-ministral-3-3b-instruct-2512"
KERNEL_ID = "kumoriai/sparebrains-h2h"
SMOKE_TARGETS, SMOKE_SAMPLES = 2, 2
KEYS = ("id", "kind", "lane", "transport", "arms", "calls", "max_tokens", "temperature", "top_p", "cohort", "schedule",
        "claim", "checkpoint", "revision")


def check(m):
    missing = [x for x in KEYS if x not in m]
    assert not missing, f"manifest misses {missing}"
    assert [tuple(e) for e in m["schedule"]] == h.schedule(), "manifest schedule is not 2601.16172 Appendix A"
    assert m["lane"] == LANE, f"the lane is the checkpoint's, {LANE}"
    assert len(m["revision"]) == 40 and all(c in "0123456789abcdef" for c in m["revision"]), "pin a revision sha"
    assert m["arms"] == ["alone", "skeleton"] and m["transport"] == "kaggle"
    return m


def prompt(arm, index, text):
    import leanstral
    if arm == "alone":
        return leanstral.PROMPT.format(target=text)
    skel, hint = h.schedule()[index % 16]
    return h.skeleton_prompt(text, skel, hint)


def expected(m, cohort, read, smoke=False):
    """Every sample the batch owes, in order: cohort x arms x indices, each with its prompt and the prompt's sha."""
    targets, n = (cohort[:SMOKE_TARGETS], SMOKE_SAMPLES) if smoke else (cohort, m["calls"])
    out = []
    for t in targets:
        text = read(t["target_set"], t["target"])
        for arm in m["arms"]:
            for i in range(n):
                p = prompt(arm, i, text)
                out.append({"id": f"{m['id']}/{t['target_set']}/{t['target']}/{arm}/{i}", "target_set": t["target_set"],
                            "target": t["target"], "rung": t.get("rung"), "arm": arm, "index": i, "prompt": p,
                            "prompt_sha": hashlib.sha256(p.encode()).hexdigest()})
    return out


def build(out_dir, m, items, batch, budget_s, sec_per_sample):
    import attempt
    out = Path(out_dir)
    out.mkdir(parents=True, exist_ok=True)
    src = (ROOT / "tools" / "kaggle_h2h_kernel.py").read_text()
    fills = [("ITEMS = []", "ITEMS = " + json.dumps([{k: e[k] for k in ("id", "prompt", "prompt_sha")} for e in items],
                                                   ensure_ascii=False)),
             ('BATCH = ""', f"BATCH = {json.dumps(batch)}"), ('MODEL = ""', f"MODEL = {json.dumps(m['checkpoint'])}"),
             ('REVISION = ""', f"REVISION = {json.dumps(m['revision'])}"), ('SYSTEM = ""', f"SYSTEM = {json.dumps(attempt.SYSTEM)}"),
             ("MAX_TOKENS, TEMPERATURE, TOP_P = 1024, 0.6, 0.95",
              f"MAX_TOKENS, TEMPERATURE, TOP_P = {m['max_tokens']}, {m['temperature']}, {m['top_p']}"),
             ("BUDGET_S = 0 ", f"BUDGET_S = {int(budget_s)} "), ("SEC_PER_SAMPLE = 0.0 ", f"SEC_PER_SAMPLE = {float(sec_per_sample)} ")]
    for old, new in fills:
        assert src.count(old) == 1, old
        src = src.replace(old, new, 1)
    (out / "kaggle_h2h_kernel.py").write_text(src)
    (out / "kernel-metadata.json").write_text(json.dumps({
        "id": KERNEL_ID, "title": "sparebrains-h2h", "code_file": "kaggle_h2h_kernel.py", "language": "python",
        "kernel_type": "script", "is_private": "false", "enable_internet": "true", "enable_gpu": "true",
        "machine_shape": "NvidiaTeslaT4", "dataset_sources": [], "model_sources": [], "competition_sources": [],
        "kernel_sources": []}, indent=1))
    return len(items)


def ingest(answers, ex):
    """({id: answer}, [void]): an answer is kept only when its id is expected, seen once, and its prompt sha matches."""
    want = {e["id"]: e for e in ex}
    seen, valid, void = {}, {}, []
    for a in answers:
        seen[a.get("id")] = seen.get(a.get("id"), 0) + 1
    for a in answers:
        i = a.get("id")
        why = ("unknown" if i not in want else "duplicate" if seen[i] > 1 else
               "prompt_sha" if a.get("prompt_sha") != want[i]["prompt_sha"] else None)
        if why:
            void.append({"id": i, "void": why})
        else:
            valid[i] = a
    return valid, list({v["id"]: v for v in void}.values())


def judge(valid, ex, read, judge_text, jobs=4):
    """One row per present sample, in the expected order: extracted and judged raw, as headtohead's arms judge (no
    fixer, no loop), on `jobs` threads (1,440 samples at ~5.5 s of Lean each is ~2.2 h serial; headtohead runs 3)."""
    from concurrent.futures import ThreadPoolExecutor

    def one(e):
        a = valid[e["id"]]
        text = read(e["target_set"], e["target"])
        name = h.re.search(r"theorem\s+(\S+)", text).group(1)
        proof = extract_proof(a.get("text") or "", name)
        verdict, followed = "no_proof", None
        if proof:
            cand = text[:PROOF_SEP.search(text).end()] + "\n" + proof.lstrip("\n")
            verdict = judge_text(cand)["verdict"]
            if e["arm"] == "skeleton":
                want = h.schedule()[e["index"] % 16][0].splitlines()
                followed = [l.strip() for l in proof.strip().splitlines() if l.strip()][:len(want)] == want
        return {**{k: e[k] for k in ("id", "target_set", "target", "rung", "arm", "index")}, "verdict": verdict,
                "followed": followed, "tokens": a.get("tokens"), "seconds": a.get("seconds"), "finish": a.get("finish")}

    with ThreadPoolExecutor(jobs) as pool:
        return list(pool.map(one, [e for e in ex if e["id"] in valid]))


def targets(samples, ex, void):
    """Per target per arm, in headtohead.summary's row shape. A target with any sample missing, void or unjudged is void
    in both arms."""
    voided = {v["id"] for v in void}
    by = {}
    for s in samples:
        by.setdefault((s["target"], s["arm"]), []).append(s)
    owed = {}
    for e in ex:
        owed.setdefault(e["target"], []).append(e["id"])
    present = {s["id"] for s in samples}
    now = datetime.now(timezone.utc).isoformat(timespec="seconds")
    rows = []
    for e in ex:
        if e["index"] != 0:
            continue
        rs = sorted(by.get((e["target"], e["arm"]), []), key=lambda s: s["index"])
        ok = [s["index"] for s in rs if s["verdict"] == "accept"]
        bad = [i for i in owed[e["target"]] if i not in present or i in voided]
        row = {"at": now, "arm": e["arm"], "target_set": e["target_set"], "target": e["target"], "rung": e["rung"],
               "status": "solved", "outcome": "solved" if ok else "failed", "first_accept_index": min(ok) if ok else None,
               "accepts": len(ok), "generated": len(rs), "judged": len(rs), "calls": len(rs),
               "tokens": None if any(s["tokens"] is None for s in rs) else sum(s["tokens"] for s in rs),
               "seconds": round(sum(s["seconds"] or 0 for s in rs), 1), "writer": LANE,
               "cut": sum(s["finish"] == "length" for s in rs), "no_proof": sum(s["verdict"] == "no_proof" for s in rs)}
        if e["arm"] == "skeleton":
            row["skeleton_followed"] = sum(bool(s["followed"]) for s in rs)
        if bad:
            row["void"] = "incomplete"
            row["missing"] = len(bad)
        rows.append(row)
    return rows


def already_judged(out):
    """Why a batch must not be judged again (two collect runs on one batch doubled every row, smoke 20261108T1747)."""
    out = Path(out)
    return f"{out.name} exists: batch already judged; nothing written" if out.exists() and out.stat().st_size else None


def report(rows, m, ex, void):
    ids = {e["id"] for e in ex}
    present = sum(r["generated"] for r in rows)
    base, why = h.baseline_or_why(ROOT / "ledger")
    s = {"writer": LANE, "manifest": m["id"], "claim": m["claim"],
         **h.summary(rows, tuple(m["arms"]), expected=len({e["target"] for e in ex}), baseline=base)}
    if why:
        s["baseline_missing"] = why
    s.update(samples_expected=len(ids), samples_present=present, samples_void=len(void))
    for f in ("cut", "no_proof"):               # the smoke's gate, auditable from the ledger (Codex 20261108T180533646354Z f1)
        s[f"{f}_by_arm"] = {arm: sum(r.get(f, 0) for r in rows if r["arm"] == arm) for arm in m["arms"]}
    s["complete"] = s["complete"] and present == len(ids) and not void
    return s


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("cmd", choices=["build", "judge"])
    ap.add_argument("--manifest", required=True)
    ap.add_argument("--smoke", action="store_true")
    ap.add_argument("--out", required=True)
    ap.add_argument("--answers", default="")
    ap.add_argument("--batch", default=datetime.now(timezone.utc).strftime("%Y%m%dT%H%M"))
    ap.add_argument("--budget-s", type=float, default=0)
    ap.add_argument("--sec-per-sample", type=float, default=0)
    a = ap.parse_args()
    m = check(json.loads((ROOT / a.manifest).read_text()))
    read = lambda s, t: (ROOT / "targets" / s / f"{t}.lean").read_text()
    ex = expected(m, h.cohort(m["cohort"]), read, a.smoke)
    if a.cmd == "build":
        n = build(a.out, m, ex, a.batch, a.budget_s, a.sec_per_sample)
        print(f"kaggle_h2h: {n} samples for {m['id']}{' (smoke)' if a.smoke else ''}, batch {a.batch}, budget {a.budget_s:.0f} s")
        return 0
    why = already_judged(a.out)
    if why:
        print(f"kaggle_h2h: {why}")
        return 0
    import lean_tools
    answers = [json.loads(l) for l in Path(a.answers).read_text().splitlines() if l.strip()] if Path(a.answers).exists() else []
    valid, void = ingest(answers, ex)
    samples = judge(valid, ex, read, lean_tools.judge_text)
    rows = targets(samples, ex, void)
    Path(a.out).parent.mkdir(parents=True, exist_ok=True)
    with open(a.out, "a") as f:
        f.writelines(json.dumps(r, ensure_ascii=False) + "\n" for r in rows + void)
    print("kaggle_h2h: " + json.dumps({**report(rows, m, ex, void), "smoke": a.smoke}))
    return 0


if __name__ == "__main__":
    sys.exit(main())
