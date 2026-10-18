"""The Leanstral lane (DECISIONS.md 2026-10-18, task #476): Mistral's open Lean prover, Leanstral 1.5, on the open
problems outside the prover lane's 50, judged by the same kernel, fixer and loop as the Kaggle prover
(tools/prover.py, lane LEANSTRAL). Its own try mode, `leanstral`.

Each run is one round: one more try on every problem that is still open here and has tries left (8 each), so a
problem stops at its first accept. Generation and judging are separate commands because the Mistral key may only be
present while no Lean runs (the workflow's steps keep it that way).

    python3 tools/leanstral.py generate --out answers.jsonl       # needs SPAREBRAINS_LEANSTRAL_KEY
    python3 tools/leanstral.py judge --answers answers.jsonl --max-minutes M

Mistral's Labs API lists the model at $0; its own limit is 38 requests and 5,000,000 tokens a minute (the org's Limits
page, 2026-10-18), separate from Kumori Chat's models. We stay at 0.5 requests a second or less and stop at the
first 429."""
import argparse, json, os, sys, threading, time, urllib.error, urllib.request
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT), str(ROOT / "tools")]
import prover

MODEL = "labs-leanstral-1-5-1"
LANE = {"backend": "mistral-leanstral-1-5", "provider": "mistral", "model": MODEL, "mode": "leanstral", "file": "leanstral"}
TRIES = 8
WORKERS = 4                      # calls in flight; each takes ~45 s, so starts stay far under 0.5 a second
MIN_GAP_S = 2.0                  # between request starts: 0.5 a second at most
MAX_TOKENS = 40000                # 16,000 cut off 27 of 36 first-round answers mid-reasoning (DECISIONS 2026-10-18)
TEMPERATURE = 0.6
API = "https://api.mistral.ai/v1/chat/completions"
PROMPT = "Complete the following Lean 4 code. Reply with the whole file in one ```lean4 block.\n\n```lean4\n{target}\n```"


def owed(open_list, rows):
    """[(problem, next sample index)] for the open problems outside the prover's 50 that this lane has not solved
    and that still have tries left, in the open list's order."""
    _, per = prover.judged(rows, LANE["mode"])
    solved = {(r["target_set"], r["target"]) for r in rows if r.get("verdict") == "accept"}
    out = []
    for t in sorted(open_list, key=lambda t: t["order"]):
        key = (t["target_set"], t["target"])
        if t.get("rung") not in prover.RUNGS and key not in solved and per[key] < TRIES:
            out.append((t, per[key]))
    return out


def text_of(content):
    """Leanstral answers in parts (thinking, then text); the proof is in the text parts."""
    if isinstance(content, str):
        return content
    return "".join(p.get("text", "") for p in content or [] if p.get("type") == "text")


class Pacer:
    def __init__(self, gap):
        self.gap, self.next, self.lock, self.stop = gap, 0.0, threading.Lock(), None

    def wait(self):
        with self.lock:
            now = time.monotonic()
            t = max(now, self.next)
            self.next = t + self.gap
        time.sleep(max(0.0, t - now))


def call(key, target_text, pacer):
    if pacer.stop:
        raise RuntimeError(f"stopped: {pacer.stop}")
    pacer.wait()
    body = json.dumps({"model": MODEL, "messages": [{"role": "user", "content": PROMPT.format(target=target_text)}],
                       "max_tokens": MAX_TOKENS, "temperature": TEMPERATURE}).encode()
    req = urllib.request.Request(API, data=body, headers={"Authorization": f"Bearer {key}", "Content-Type": "application/json"})
    t = time.time()
    try:
        with urllib.request.urlopen(req, timeout=600) as r:
            d = json.load(r)
    except urllib.error.HTTPError as e:
        if e.code in (402, 429):          # out of pot or over the limit: stop the whole round, never hammer
            pacer.stop = f"HTTP {e.code}"
        raise RuntimeError(f"HTTP {e.code}: {e.read()[:200].decode(errors='replace')}")
    choice = d["choices"][0]
    return {"text": text_of(choice["message"]["content"]), "tokens": (d.get("usage") or {}).get("completion_tokens"),
            "finish": choice.get("finish_reason"), "seconds": round(time.time() - t, 1), "usage": d.get("usage")}


def generate(out_path, key, open_list, rows, batch):
    work = owed(open_list, rows)
    pacer = Pacer(MIN_GAP_S)
    cfg = {"model": MODEL, "max_tokens": MAX_TOKENS, "temperature": TEMPERATURE, "gpus": None, "dtype": None, "top_p": None}

    def one(item):
        t, sample = item
        text = (ROOT / "targets" / t["target_set"] / f"{t['target']}.lean").read_text()
        try:
            r = call(key, text, pacer)
        except Exception as e:
            return {"target_set": t["target_set"], "target": t["target"], "error": str(e)[:300]}
        return {"batch": batch, "target_set": t["target_set"], "target": t["target"], "sample": sample, "config": cfg, **r}

    with ThreadPoolExecutor(WORKERS) as pool:
        answers = list(pool.map(one, work))
    good = [a for a in answers if "error" not in a]
    with open(out_path, "w") as fh:
        for a in good:
            fh.write(json.dumps(a) + "\n")
    errors = [a["error"] for a in answers if "error" in a]
    print(f"leanstral round {batch}: {len(work)} problems owed a try, {len(good)} answered, {len(errors)} errors"
          + (f" (first: {errors[0]})" if errors else "") + (f"; stopped: {pacer.stop}" if pacer.stop else ""))
    return good


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("cmd", choices=["generate", "judge"])
    ap.add_argument("--out")
    ap.add_argument("--answers")
    ap.add_argument("--max-minutes", type=float, default=60)
    a = ap.parse_args()
    import relay
    open_list = relay.fetch_json("/targets.json")["open"]
    rows = prover.prover_rows(lane=LANE)
    if a.cmd == "generate":
        key = os.environ.get("SPAREBRAINS_LEANSTRAL_KEY", "").strip()
        if not key:
            sys.exit("SPAREBRAINS_LEANSTRAL_KEY is not set")
        batch = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M")
        generate(a.out, key, open_list, rows, batch)
        return 0
    import lean_tools, fixer, subgoals
    answers = prover.read_answers(a.answers)
    if not answers:
        print("leanstral judged: nothing to judge")
        return 0
    still_open = {(t["target_set"], t["target"]) for t in open_list}
    batch = answers[0]["batch"]
    post = None
    from utilities.kumori_api_client import init as kumori_init, sparebrains_attempt
    try:
        kumori_init()
        post = sparebrains_attempt
    except Exception as e:                    # the site record is a nicety; the ledger gets every row regardless
        print(f"site recording off ({type(e).__name__}); the ledger still gets every row", flush=True)
    names_ix = lean_tools.index()
    stats = prover.judge_answers(
        answers, rows, judge_text=lean_tools.judge_text,
        fix=lambda proof, out: fixer.fix(proof, out, *names_ix),
        repair=lambda cand, prefix, out: subgoals.repair(cand, prefix, out, ask=None, run_lean=lean_tools.run_lean,
                                                         judge_text=lean_tools.judge_text),
        record=prover.Recorder(batch, post, LANE), run_id=f"leanstral-{batch}",
        deadline=time.time() + a.max_minutes * 60, still_open=still_open, lane=LANE)
    print("leanstral judged: " + json.dumps(stats))
    return 0


if __name__ == "__main__":
    sys.exit(main())
