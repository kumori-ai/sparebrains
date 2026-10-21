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
import argparse, http.client, json, os, sys, threading, time, urllib.error, urllib.request
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT), str(ROOT / "tools")]
import prover

MODEL = "labs-leanstral-1-5-1"
KEY_ENV = "SPAREBRAINS_LEANSTRAL_KEY"     # the Mistral key; present only in steps where no Lean runs, or as another user
LANE = {"backend": "mistral-leanstral-1-5", "provider": "mistral", "model": MODEL, "mode": "leanstral", "file": "leanstral"}
TRIES = 8                        # answers that finished; one cut off at the token cap is not a try
MAX_CALLS = 3 * TRIES            # calls a problem may take in all, so one that always runs out still stops
WORKERS = 4                      # calls in flight; each takes ~45 s, so starts stay far under 0.5 a second
MIN_GAP_S = 2.0                  # between request starts: 0.5 a second at most
MAX_TOKENS = 120000               # 40,000 cut off 129 of 225 answers (DECISIONS 2026-10-20); 128k is the model's max output
TEMPERATURE = 0.6
API = "https://api.mistral.ai/v1/chat/completions"
PROMPT = "Complete the following Lean 4 code. Reply with the whole file in one ```lean4 block.\n\n```lean4\n{target}\n```"


def owed(open_list, rows, bar=False, reachable=frozenset()):
    """[(problem, next sample index)] for the open problems this lane has not solved and that still have tries left:
    outside the prover's 50 unless `bar` (once the plan arm is judged, DECISIONS 2026-10-20), the problems a
    published prover reached as stated first (tools/reachable.py), then the open list's order. A try is an answer
    that finished; one cut off at the token cap never wrote its proof."""
    keys, per = prover.judged(rows, LANE["mode"])
    cut = {(r.get("batch"), r["target_set"], r["target"], r.get("sample_no"), r.get("goal")) for r in rows
           if r.get("try_mode") == LANE["mode"] and (r.get("inference") or {}).get("finish") == "length"}
    capped = Counter((s, t) for _, s, t, _, _ in cut)
    solved = {(r["target_set"], r["target"]) for r in rows if r.get("verdict") == "accept"}
    out = []
    for t in sorted(open_list, key=lambda t: ((t["target_set"], t["target"]) not in reachable, t["order"])):
        key = (t["target_set"], t["target"])
        if ((bar or t.get("rung") not in prover.RUNGS) and key not in solved and per[key] - capped[key] < TRIES
                and per[key] < MAX_CALLS):
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


def key_from_env():
    key = os.environ.get(KEY_ENV, "").strip()
    if not key:
        sys.exit(f"{KEY_ENV} is not set")
    return key


def call(key, target_text, pacer):
    return call_prompt(key, PROMPT.format(target=target_text), pacer)


def call_prompt(key, prompt, pacer):
    """One Leanstral call with any prompt (tools/decompose.py asks for steps), paced, stopping at 402/429."""
    if pacer.stop:
        raise RuntimeError(f"stopped: {pacer.stop}")
    pacer.wait()
    body = json.dumps({"model": MODEL, "messages": [{"role": "user", "content": prompt}],
                       "max_tokens": MAX_TOKENS, "temperature": TEMPERATURE, "stream": True}).encode()
    req = urllib.request.Request(API, data=body, headers={"Authorization": f"Bearer {key}", "Content-Type": "application/json"})
    t = time.time()
    for attempt in (0, 1):
        try:
            with urllib.request.urlopen(req, timeout=1200) as r:
                d = read_stream(r)
            break
        except urllib.error.HTTPError as e:
            if e.code in (402, 429):          # out of pot or over the limit: stop the whole round, never hammer
                pacer.stop = f"HTTP {e.code}"
            raise RuntimeError(f"HTTP {e.code}: {e.read()[:200].decode(errors='replace')}")
        # A dropped connection is retried once (8 of 68 decomposition asks, 2026-10-19); an HTTP error never is.
        except (http.client.RemoteDisconnected, ConnectionError, TimeoutError, urllib.error.URLError):
            if attempt or pacer.stop:
                raise
            pacer.wait()
    return {**d, "tokens": (d["usage"] or {}).get("completion_tokens"), "seconds": round(time.time() - t, 1),
            "retried": bool(attempt)}


def read_stream(r):
    """A streamed reply (Mistral's docs, read 2026-10-20): delta.content is a list holding a thinking chunk while the
    model thinks, then a plain string for the answer. Streaming keeps bytes flowing on a long answer: 12 of 20 calls
    were dropped as idle when the reply came back whole (round 20261020T2158, after the 120,000 cap)."""
    text, finish, usage, other = [], None, None, []
    for line in r:
        line = line.decode().strip()
        if not line.startswith("data:"):
            other.append(line)
            continue
        if line == "data: [DONE]":
            continue
        e = json.loads(line[5:])
        for c in e.get("choices") or []:
            text.append(text_of((c.get("delta") or {}).get("content")))
            finish = c.get("finish_reason") or finish
        usage = e.get("usage") or usage
    if not text and "".join(other).startswith("{"):        # a whole JSON reply after all: read it as one
        d = json.loads("".join(other))
        c = d["choices"][0]
        return {"text": text_of(c["message"]["content"]), "finish": c.get("finish_reason"), "usage": d.get("usage")}
    return {"text": "".join(text), "finish": finish, "usage": usage}


def reply(r):
    """A call's text, or why there is none: 16 of 68 decomposition asks came back empty with no reason kept."""
    if (r.get("text") or "").strip():
        return r["text"]
    return {"error": f"empty reply (finish={r.get('finish')}, {r.get('tokens')} tokens)"}


def generate(out_path, key, open_list, rows, batch):
    reach = ({(r["target_set"], r["target"]) for r in json.loads(prover.REACHABLE.read_text())["reachable"]}
             if prover.REACHABLE.exists() else frozenset())
    work = owed(open_list, rows, bar=prover.plan_owed() is None, reachable=reach)
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
        key = key_from_env()
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
