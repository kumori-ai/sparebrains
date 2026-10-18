"""Stage 3's prover, run on Kaggle's free GPUs (DECISIONS.md 2026-10-17). tools/prover.py copies this file,
fills PROBLEMS and BATCH, and pushes it as a Kaggle script; it writes every answer to
/kaggle/working/answers.jsonl, which the prover workflow downloads and judges with tools/check.py. Nothing
here judges anything: the kernel stays in GitHub, beside the ledger.

Measured on Kaggle's GPU T4 x2, 2026-10-17 (canary): vLLM needs Kaggle's torchaudio removed (it is built for
CUDA 12.8, vLLM's PyTorch for 13.0, and transformers imports it); the model loads in about 5.6 minutes; 8
samples of an easy problem came back in 67 s, 108 tokens/s together.
"""
import json, os, subprocess, sys, time
from datetime import datetime, timezone

PROBLEMS = []          # filled by tools/prover.py: [{"target_set", "target", "statement", "n"}], plus "goal" for a goal batch
BATCH = ""             # filled by tools/prover.py
MODEL = "Goedel-LM/Goedel-Prover-V2-8B"
MAX_TOKENS, TEMPERATURE, TOP_P = 16000, 1.0, 0.95
BUDGET_S = 9 * 3600    # no new problem starts after this; Kaggle ends a session at 12 h
CHUNK = 4              # problems per generate call: answers are written after each chunk
OUT = "/kaggle/working/answers.jsonl"
TIMING = "/kaggle/working/timing.json"   # when the GPUs came, the model loaded, each chunk, the end (UTC)
# The model card's prompt (huggingface.co/Goedel-LM/Goedel-Prover-V2-8B, section 6), unchanged.
PROMPT = ("Complete the following Lean 4 code:\n```lean4\n{}```\nBefore producing the Lean 4 code to formally prove "
          "the given theorem, provide a detailed proof plan outlining the main proof steps and strategies.\nThe plan "
          "should highlight key ideas, intermediate lemmas, and proof structures that will guide the construction of "
          "the final formal proof.")

def stamp(**kw):
    timing.update(kw)
    json.dump(timing, open(TIMING, "w"))


def machine():
    """What Kaggle gave this batch: CPUs, CPU model, RAM, GPUs. Kaggle publishes only the GPU; the rest is ours to record."""
    m = {"cpus": os.cpu_count()}
    try:
        m["cpu_model"] = next(l.split(":", 1)[1].strip() for l in open("/proc/cpuinfo") if l.startswith("model name"))
        m["ram_gb"] = round(int(next(l.split()[1] for l in open("/proc/meminfo") if l.startswith("MemTotal"))) / 1048576, 1)
    except Exception:
        pass
    r = subprocess.run(["nvidia-smi", "--query-gpu=name,memory.total", "--format=csv,noheader"], capture_output=True, text=True)
    m["gpus"] = [g.strip() for g in r.stdout.splitlines() if g.strip()]
    return m


timing = {"batch": BATCH, "chunks": [], "machine": machine()}
stamp(started_at=datetime.now(timezone.utc).isoformat(timespec="seconds"))   # the first line run: the queue is over
t0 = time.time()
subprocess.run([sys.executable, "-m", "pip", "install", "-q", "vllm"], check=True)
subprocess.run([sys.executable, "-m", "pip", "uninstall", "-y", "-q", "torchaudio"], check=False)
from vllm import LLM, SamplingParams

llm = LLM(model=MODEL, dtype="half", tensor_parallel_size=2, max_model_len=MAX_TOKENS + 2048,
          gpu_memory_utilization=0.92, trust_remote_code=True)
tok = llm.get_tokenizer()
print(json.dumps({"batch": BATCH, "problems": len(PROBLEMS), "load_s": round(time.time() - t0, 1)}), flush=True)
stamp(loaded_at=datetime.now(timezone.utc).isoformat(timespec="seconds"), load_s=round(time.time() - t0, 1))

with open(OUT, "a") as out:
    for i in range(0, len(PROBLEMS), CHUNK):
        if time.time() - t0 > BUDGET_S:
            print(json.dumps({"stopped": "budget", "done": i}), flush=True)
            break
        chunk = PROBLEMS[i:i + CHUNK]
        prompts = [tok.apply_chat_template([{"role": "user", "content": PROMPT.format(p["statement"])}],
                                           tokenize=False, add_generation_prompt=True) for p in chunk]
        params = [SamplingParams(n=p["n"], temperature=TEMPERATURE, top_p=TOP_P, max_tokens=MAX_TOKENS) for p in chunk]
        t = time.time()
        results = llm.generate(prompts, params)
        secs = time.time() - t
        n_tokens = sum(len(o.token_ids) for r in results for o in r.outputs)
        for p, r in zip(chunk, results):
            for k, o in enumerate(r.outputs):
                out.write(json.dumps({"batch": BATCH, "target_set": p["target_set"], "target": p["target"], "sample": k,
                                      **({"goal": p["goal"]} if p.get("goal") else {}),
                                      "text": o.text, "tokens": len(o.token_ids), "finish": o.finish_reason,
                                      "seconds": round(secs * len(o.token_ids) / max(n_tokens, 1), 1),
                                      "config": {"model": MODEL, "max_tokens": MAX_TOKENS, "temperature": TEMPERATURE,
                                                 "top_p": TOP_P, "dtype": "half", "gpus": "T4 x2"}}) + "\n")
        out.flush()
        print(json.dumps({"chunk": i // CHUNK, "problems": [p["target"] for p in chunk], "seconds": round(secs, 1),
                          "tokens": n_tokens, "tok_per_s": round(n_tokens / secs, 1)}), flush=True)
        timing["chunks"].append({"problems": len(chunk), "seconds": round(secs, 1), "tokens": n_tokens})
        stamp()
stamp(finished_at=datetime.now(timezone.utc).isoformat(timespec="seconds"))
