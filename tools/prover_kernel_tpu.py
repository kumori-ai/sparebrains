"""The prover on Kaggle's free TPU v5e-8 (task #479): the same model, prompt, sampling and answer format as
tools/prover_kernel.py, on the TPU's own weekly hours (about 20, separate from the GPU's 30; aifree.dev, checked
2026-10-12). tools/prover.py fills PROBLEMS and BATCH and pushes it as its own kernel, kumoriai/sparebrains-prover-tpu.

The runtime follows github.com/ARahim3/kaggle-tpu-lab (MIT; read 2026-10-18): a fresh venv with vllm-tpu pinned and
CPU torch, built by uv in about 30 s. Their patch is for Qwen3.8's DeltaNet and MTP layers; Goedel-Prover-V2-8B is a
plain Qwen3-8B, which stock vllm-tpu serves. The model is split over all 8 chips (8 KV heads, 8 chips). Generation
runs in that venv as a child process; this script only builds it, hands over the problems and keeps the timing.
"""
import json, os, subprocess, sys, time
from datetime import datetime, timezone

PROBLEMS = []          # filled by tools/prover.py: [{"target_set", "target", "statement", "n"}], plus "goal" for a goal batch
BATCH = ""             # filled by tools/prover.py
MODEL = "Goedel-LM/Goedel-Prover-V2-8B"
VLLM_TPU = "0.28.0"
MAX_TOKENS, TEMPERATURE, TOP_P = 16000, 1.0, 0.95
BUDGET_S = 7 * 3600    # no new chunk after this; a TPU session ends a little under 9 h
CHUNK = 8              # problems per generate call: answers are written after each chunk
WORK = "/kaggle/working"
OUT, TIMING, VENV = f"{WORK}/answers.jsonl", f"{WORK}/timing.json", "/tmp/vllm-tpu"
PROMPT = ("Complete the following Lean 4 code:\n```lean4\n{}```\nBefore producing the Lean 4 code to formally prove "
          "the given theorem, provide a detailed proof plan outlining the main proof steps and strategies.\nThe plan "
          "should highlight key ideas, intermediate lemmas, and proof structures that will guide the construction of "
          "the final formal proof.")

timing = {"batch": BATCH, "chunks": [], "machine": {"cpus": os.cpu_count(), "accelerator": "TPU v5e-8"}}


def stamp(**kw):
    timing.update(kw)
    json.dump(timing, open(TIMING, "w"))


def sh(cmd):
    print("$", " ".join(cmd), flush=True)
    return subprocess.run(cmd).returncode


stamp(started_at=datetime.now(timezone.utc).isoformat(timespec="seconds"))
t0 = time.time()
PY = f"{VENV}/bin/python"
ok = (sh([sys.executable, "-m", "pip", "install", "-q", "uv"]) == 0
      # Python 3.12, fetched by uv: Kaggle's TPU image runs 3.13, and vllm-tpu 0.28.0 needs nixl 0.3.0, which has
      # no cp313 wheel (the first smoke, 2026-10-18, failed resolving dependencies in 9 s).
      and sh([sys.executable, "-m", "uv", "venv", VENV, "--python", "3.12", "-q"]) == 0
      and sh([sys.executable, "-m", "uv", "pip", "install", "--python", PY, "--torch-backend=cpu", f"vllm-tpu=={VLLM_TPU}"]) == 0)
if not ok:
    stamp(failed="vllm-tpu install")
    sys.exit("vllm-tpu install failed")
stamp(venv_s=round(time.time() - t0, 1))

GEN = r'''
import json, sys, time
from vllm import LLM, SamplingParams
cfg = json.load(open(sys.argv[1]))
t0 = time.time()
llm = LLM(model=cfg["model"], dtype="bfloat16", tensor_parallel_size=8, max_model_len=cfg["max_tokens"] + 2048,
          max_num_seqs=64)
tok = llm.get_tokenizer()
print(json.dumps({"loaded_s": round(time.time() - t0, 1)}), flush=True)
problems = cfg["problems"]
with open(cfg["out"], "a") as out:
    for i in range(0, len(problems), cfg["chunk"]):
        if time.time() - cfg["t0"] > cfg["budget_s"]:
            print(json.dumps({"stopped": "budget", "done": i}), flush=True)
            break
        chunk = problems[i:i + cfg["chunk"]]
        prompts = [tok.apply_chat_template([{"role": "user", "content": cfg["prompt"].format(p["statement"])}],
                                           tokenize=False, add_generation_prompt=True) for p in chunk]
        params = [SamplingParams(n=p["n"], temperature=cfg["temperature"], top_p=cfg["top_p"],
                                 max_tokens=cfg["max_tokens"]) for p in chunk]
        t = time.time()
        results = llm.generate(prompts, params)
        secs = time.time() - t
        n_tokens = sum(len(o.token_ids) for r in results for o in r.outputs)
        for p, r in zip(chunk, results):
            for k, o in enumerate(r.outputs):
                out.write(json.dumps({"batch": cfg["batch"], "target_set": p["target_set"], "target": p["target"],
                                      "sample": k, **({"goal": p["goal"]} if p.get("goal") else {}),
                                      "text": o.text, "tokens": len(o.token_ids), "finish": o.finish_reason,
                                      "seconds": round(secs * len(o.token_ids) / max(n_tokens, 1), 1),
                                      "config": {"model": cfg["model"], "max_tokens": cfg["max_tokens"],
                                                 "temperature": cfg["temperature"], "top_p": cfg["top_p"],
                                                 "dtype": "bfloat16", "gpus": "TPU v5e-8"}}) + "\n")
        out.flush()
        print(json.dumps({"chunk": i // cfg["chunk"], "seconds": round(secs, 1), "tokens": n_tokens,
                          "tok_per_s": round(n_tokens / secs, 1)}), flush=True)
'''
open("/tmp/gen.py", "w").write(GEN)
json.dump({"model": MODEL, "problems": PROBLEMS, "batch": BATCH, "out": OUT, "chunk": CHUNK, "prompt": PROMPT,
           "max_tokens": MAX_TOKENS, "temperature": TEMPERATURE, "top_p": TOP_P, "t0": t0, "budget_s": BUDGET_S},
          open("/tmp/gen.json", "w"))
proc = subprocess.Popen([PY, "/tmp/gen.py", "/tmp/gen.json"], stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
for line in proc.stdout:
    print(line, end="", flush=True)
    if line.startswith("{"):
        try:
            ev = json.loads(line)
        except ValueError:
            continue
        if "loaded_s" in ev:
            stamp(loaded_at=datetime.now(timezone.utc).isoformat(timespec="seconds"), load_s=round(time.time() - t0, 1))
        elif "chunk" in ev:
            timing["chunks"].append(ev)
            stamp()
stamp(finished_at=datetime.now(timezone.utc).isoformat(timespec="seconds"), exit=proc.wait())
