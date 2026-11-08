"""The Kaggle head-to-head's generation half (tools/kaggle_h2h.py fills ITEMS and the rest, then pushes it as a public
Kaggle script; DECISIONS 2026-11-08). One chat-templated prompt per sample id, generated once each; nothing here
judges or repairs anything. Answers go to /kaggle/working/answers.jsonl, one line per id, written after each chunk."""
import hashlib, json, os, subprocess, sys, time
from datetime import datetime, timezone

ITEMS = []             # filled: [{"id", "prompt", "prompt_sha"}]
BATCH = ""
MODEL = ""
REVISION = ""
SYSTEM = ""
MAX_TOKENS, TEMPERATURE, TOP_P = 1024, 0.6, 0.95
BUDGET_S = 0           # filled: the session's seconds; no chunk starts unless its estimate fits
SEC_PER_SAMPLE = 0.0   # filled: the measured rate for this lane (the smoke's), never another model's
CHUNK = 64
OUT, TIMING = "/kaggle/working/answers.jsonl", "/kaggle/working/timing.json"

timing = {"batch": BATCH, "chunks": [], "started_at": datetime.now(timezone.utc).isoformat(timespec="seconds")}
t0 = time.time()
subprocess.run([sys.executable, "-m", "pip", "install", "-q", "vllm"], check=True)
subprocess.run([sys.executable, "-m", "pip", "uninstall", "-y", "-q", "torchaudio"], check=False)
import vllm
from vllm import LLM, SamplingParams

# Mistral's own tokenizer and its chat format, as the model card's vLLM command sets (`--tokenizer_mode mistral`);
# vLLM picked it unasked in smoke 20261108T1651, whose HF-template call then failed. llm.chat formats each conversation
# with whatever tokenizer was loaded, so the prompt format is the one Mistral ships.
llm = LLM(model=MODEL, revision=REVISION, dtype="half", tensor_parallel_size=2, max_model_len=MAX_TOKENS + 4096,
          gpu_memory_utilization=0.9, limit_mm_per_prompt={"image": 0}, tokenizer_mode="mistral")
tok = llm.get_tokenizer()
try:
    import mistral_common
    mc = mistral_common.__version__
except Exception:
    mc = None
timing.update(load_s=round(time.time() - t0, 1), vllm=vllm.__version__, tokenizer=type(tok).__name__, mistral_common=mc,
              gpus=subprocess.run(["nvidia-smi", "--query-gpu=name", "--format=csv,noheader"], capture_output=True,
                                  text=True).stdout.split("\n")[0])
params = SamplingParams(n=1, temperature=TEMPERATURE, top_p=TOP_P, max_tokens=MAX_TOKENS)
rate = SEC_PER_SAMPLE
with open(OUT, "a") as out:
    for i in range(0, len(ITEMS), CHUNK):
        chunk = ITEMS[i:i + CHUNK]
        if rate * len(chunk) > BUDGET_S - (time.time() - t0):
            print(json.dumps({"stopped": "budget", "done": i}), flush=True)
            timing["stopped"] = {"budget": True, "done": i}
            break
        convs = [[{"role": "system", "content": SYSTEM}, {"role": "user", "content": it["prompt"]}] for it in chunk]
        t = time.time()
        results = llm.chat(convs, params, use_tqdm=False)
        secs = time.time() - t
        for it, r in zip(chunk, results):
            o = r.outputs[0]
            out.write(json.dumps({"batch": BATCH, "id": it["id"], "prompt_sha": it["prompt_sha"], "text": o.text,
                                  "tokens": len(o.token_ids), "finish": o.finish_reason,
                                  "seconds": round(secs / len(chunk), 2)}, ensure_ascii=False) + "\n")
        out.flush()
        rate = max(rate, secs / len(chunk))
        timing["chunks"].append({"samples": len(chunk), "seconds": round(secs, 1)})
        json.dump(timing, open(TIMING, "w"))
timing["finished_at"] = datetime.now(timezone.utc).isoformat(timespec="seconds")
json.dump(timing, open(TIMING, "w"))
