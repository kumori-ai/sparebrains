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

llm = LLM(model=MODEL, revision=REVISION, dtype="half", tensor_parallel_size=2, max_model_len=MAX_TOKENS + 4096,
          gpu_memory_utilization=0.9, limit_mm_per_prompt={"image": 0})
tok = llm.get_tokenizer()
timing.update(load_s=round(time.time() - t0, 1), vllm=vllm.__version__,
              chat_template_sha=hashlib.sha256((tok.chat_template or "").encode()).hexdigest(),
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
        prompts = [tok.apply_chat_template([{"role": "system", "content": SYSTEM}, {"role": "user", "content": it["prompt"]}],
                                           tokenize=False, add_generation_prompt=True) for it in chunk]
        t = time.time()
        results = llm.generate(prompts, params)
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
