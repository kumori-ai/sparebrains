"""The prover on Kaggle's free TPU v5e-8 (task #479): the same model, prompt, sampling and answer format as
tools/prover_kernel.py, on the TPU's own weekly hours (about 20, separate from the GPU's 30; aifree.dev, checked
2026-10-12). tools/prover.py fills PROBLEMS and BATCH and pushes it as its own kernel, kumoriai/sparebrains-prover-tpu.

The runtime follows github.com/ARahim3/kaggle-tpu-lab (MIT; read 2026-10-18): a fresh venv with vllm-tpu pinned and
CPU torch, built by uv in about 30 s. Their patch is for Qwen3.8's DeltaNet and MTP layers; Goedel-Prover-V2-8B is a
plain Qwen3-8B, which stock vllm-tpu serves. The model is split over all 8 chips (8 KV heads, 8 chips). Generation
runs in that venv as a child process; this script only builds it, hands over the problems and keeps the timing.

Getting a TPU from `kaggle kernels push`, as found 2026-10-18 (sources: Kaggle staff on Kaggle/kaggle-cli#1197,
2026-09-17; our own smokes):
- The account must be identity-verified (Settings, Persona). Kaggle's prompt: "Scarce resources such as TPUs ...
  require identity verification." Before ours was verified (2026-10-18, just before the 22:10 UTC push), three pushes ran at once on a
  4-CPU machine with no error; the first push after it went QUEUED instead.
- Metadata: enable_tpu "true", machine_shape "TpuV5E8", no docker_image. A pinned CPU/GPU docker_image overrides
  the TPU VM and the kernel silently runs on CPU (staff, #1197). tools/prover.py writes it that way.
- A pushed TPU kernel is a batch TPU session: it waits in a background queue, longer than a browser session.
  Waits of 2 h to 9 h are reported (Kaggle forum, product-feedback 271777, 253459); ours queued 2 h+ on 10-18.
- One batch TPU session per user, queued or running ("Maximum batch TPU session count of 1 reached"), so never
  push a second while one waits. We set no expiry: prover.yml waits while it says QUEUED (the 8B batch queued 1,121 min
  from 2026-10-20, the 32B ~31 h from 10-21). An earlier line here named a 12 h expiry that was never built.
- Status: `kaggle kernels status` (prover.yml's TPU leg, every two hours) says QUEUED / RUNNING / COMPLETE; we found no
  queue position for pushed kernels. Proof of a TPU is tpu_devices in timing.json, never the name we asked for:
  this script exits at once when /dev/accel* and /dev/vfio/* are both empty.

Heartbeats (2026-10-23): the 32B batch tpu32-20261021T2327 ran ~80 min and ended in ERROR with nothing kept, not even
timing.json, so a death leaves no trace on Kaggle. The kernel posts its phase, cgroup and host memory, disk, and on a
failure the child's first error block to ntfy.sh on a random per-batch topic, every 5 min and at each milestone (the
pattern of kaggle-tpu-lab's serve_qwen38.py; ntfy: 250 messages a day, 4,096 bytes each, kept 12 h, docs.ntfy.sh).
The kernel is public, so the topic is too: anyone can read or post to it. Heartbeats are diagnostics only; nothing
read back decides a retry or completion, and answers never travel this way. prover.py beats keeps them in the ledger.
"""
import collections, glob, json, os, shutil, subprocess, sys, threading, time, urllib.request
from datetime import datetime, timezone

PROBLEMS = []          # filled by tools/prover.py: [{"target_set", "target", "statement", "n"}], plus "goal" for a goal batch
BATCH = ""             # filled by tools/prover.py
NTFY_TOPIC = ""        # filled by tools/prover.py: random per batch; empty sends no heartbeats
MODEL = "Goedel-LM/Goedel-Prover-V2-8B"
VLLM_TPU = "0.28.0"
MAX_TOKENS, TEMPERATURE, TOP_P = 16000, 1.0, 0.95
BUDGET_S = 7 * 3600    # no new chunk after this; a TPU session ends a little under 9 h
CHUNK = 2              # problems per generate call: answers are written after each chunk; 2 x n=32 fills max_num_seqs 64
BEAT_S = 300           # a heartbeat every 5 min: ~110 in a 9 h session, under ntfy's 250 a day
WORK = "/kaggle/working"
OUT, TIMING, VENV = f"{WORK}/answers.jsonl", f"{WORK}/timing.json", "/tmp/vllm-tpu"
PROMPT = ("Complete the following Lean 4 code:\n```lean4\n{}```\nBefore producing the Lean 4 code to formally prove "
          "the given theorem, provide a detailed proof plan outlining the main proof steps and strategies.\nThe plan "
          "should highlight key ideas, intermediate lemmas, and proof structures that will guide the construction of "
          "the final formal proof.")

# the TPU devices themselves, not the name we asked for: empty means Kaggle ran us without a TPU
timing = {"batch": BATCH, "chunks": [], "machine": {"cpus": os.cpu_count(), "asked": "TPU v5e-8",
                                                    "tpu_devices": sorted(glob.glob("/dev/accel*") + glob.glob("/dev/vfio/*"))}}
phase = "started"


def _read(path):
    try:
        return open(path).read().strip()
    except OSError:
        return None


def _gb(v):
    return round(int(v) / 1e9, 2) if v and v.isdigit() else v


def memory():
    """The cgroup's memory (v2, else v1) and the host's, in GB: current, peak, limit, OOM events, anon vs page cache."""
    cg = "/sys/fs/cgroup"
    m = {"current": _gb(_read(f"{cg}/memory.current") or _read(f"{cg}/memory/memory.usage_in_bytes")),
         "peak": _gb(_read(f"{cg}/memory.peak") or _read(f"{cg}/memory/memory.max_usage_in_bytes")),
         "max": _gb(_read(f"{cg}/memory.max") or _read(f"{cg}/memory/memory.limit_in_bytes"))}
    ev = _read(f"{cg}/memory.events")
    if ev:
        m["events"] = {k: int(v) for k, v in (l.split() for l in ev.splitlines()) if v != "0"}
    st = dict(l.split() for l in (_read(f"{cg}/memory.stat") or "").splitlines() if len(l.split()) == 2)
    m.update({k: _gb(st[k]) for k in ("anon", "file") if k in st})
    info = dict(l.split(":", 1) for l in (_read("/proc/meminfo") or "").splitlines() if ":" in l)
    for k in ("MemTotal", "MemAvailable"):
        if k in info:
            m[k] = round(int(info[k].split()[0]) / 1e6, 2)
    return m


def beat(event, **kw):
    """One heartbeat to ntfy, best effort: nothing in it, reading memory or disk, building or posting, may raise
    into the batch. Bounded under ntfy's 4,096 bytes."""
    if not NTFY_TOPIC:
        return
    try:
        _beat(event, **kw)
    except BaseException as e:      # a heartbeat never stops the batch, even an interrupt raised inside one
        try:
            print(f"(heartbeat failed: {type(e).__name__})", flush=True)
        except BaseException:
            pass


def _beat(event, **kw):
    body = {"batch": BATCH, "event": event, "phase": phase, "elapsed_s": round(time.time() - T_START),
            "memory": memory(), "disk_free_gb": {d: round(shutil.disk_usage(d).free / 1e9, 1) for d in DISKS if os.path.isdir(d)},
            **kw}
    msg = json.dumps(body)
    # the tail gives way first, keeping its last lines; the error block keeps its first lines, the root cause
    for k, keep in (("tail", lambda v, n: v[-n:]), ("error", lambda v, n: v[:n])):
        if len(msg) > 3900 and k in body:
            body[k] = keep(body[k], max(200, len(body[k]) - (len(msg) - 3900)))
            msg = json.dumps(body)
    if len(msg) > 3900:
        msg = json.dumps({k: body[k] for k in ("batch", "event", "phase", "elapsed_s", "exit") if k in body})
    urllib.request.urlopen(urllib.request.Request(f"https://ntfy.sh/{NTFY_TOPIC}", data=msg.encode(),
                                                  headers={"Title": f"{BATCH} {event}"}), timeout=10)


def pulse():
    while True:
        time.sleep(BEAT_S)
        beat("alive")


T_START = time.time()
DISKS = ("/tmp", os.path.expanduser("~"), "/kaggle/temp", "/mnt", WORK)
threading.Thread(target=pulse, daemon=True).start()
if not timing["machine"]["tpu_devices"]:
    json.dump({**timing, "failed": "no TPU device"}, open(TIMING, "w"))
    beat("failed", reason="no TPU device")
    sys.exit("no TPU device: Kaggle ran this kernel without a TPU")


def stamp(**kw):
    timing.update(kw)
    json.dump(timing, open(TIMING, "w"))


def sh(cmd):
    print("$", " ".join(cmd), flush=True)
    return subprocess.run(cmd).returncode


stamp(started_at=datetime.now(timezone.utc).isoformat(timespec="seconds"))
beat("started", machine=timing["machine"])

# Disk before anything is downloaded (task #534): the 32B is 65.6 GB in bf16 and the TPU VM's disk was never measured.
# The model goes to the mount with the most room, never /kaggle/working, whose files become the kernel's output.
MODEL_GB = {"Goedel-LM/Goedel-Prover-V2-8B": 16.4, "Goedel-LM/Goedel-Prover-V2-32B": 65.6}
need_gb = MODEL_GB.get(MODEL, 70) * 1.15 + 8          # weights, headroom, and the vllm-tpu venv
free = {d: round(shutil.disk_usage(d).free / 1e9, 1) for d in ("/tmp", os.path.expanduser("~"), "/kaggle/temp", "/mnt")
        if os.path.isdir(d)}
stamp(disk={"free_gb": free, "need_gb": round(need_gb, 1)})
best = max(free, key=free.get) if free else None
if not best or free[best] < need_gb:
    stamp(failed=f"disk: {need_gb:.0f} GB needed, most free {free.get(best)} GB at {best}")
    beat("failed", reason=timing["failed"])
    sys.exit(f"not enough disk for {MODEL}: {free}")
os.environ["HF_HOME"] = f"{best}/hf"                 # the generation child inherits it
t0 = time.time()
phase = "venv"
PY = f"{VENV}/bin/python"
ok = (sh([sys.executable, "-m", "pip", "install", "-q", "uv"]) == 0
      # Python 3.12, fetched by uv: Kaggle's TPU image runs 3.13, and vllm-tpu 0.28.0 needs nixl 0.3.0, which has
      # no cp313 wheel (the first smoke, 2026-10-18, failed resolving dependencies in 9 s).
      and sh([sys.executable, "-m", "uv", "venv", VENV, "--python", "3.12", "-q"]) == 0
      and sh([sys.executable, "-m", "uv", "pip", "install", "--python", PY, "--torch-backend=cpu", f"vllm-tpu=={VLLM_TPU}"]) == 0)
if not ok:
    stamp(failed="vllm-tpu install")
    beat("failed", reason="vllm-tpu install")
    sys.exit("vllm-tpu install failed")
stamp(venv_s=round(time.time() - t0, 1))
beat("venv", venv_s=timing["venv_s"])

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
# The child downloads the weights to HF_HOME and loads them: "loading" until it says loaded; disk_free_gb tracks the download.
phase = "loading"
beat("loading", model=MODEL)
tail, error = collections.deque(maxlen=40), []
proc = subprocess.Popen([PY, "/tmp/gen.py", "/tmp/gen.json"], stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
for line in proc.stdout:
    print(line, end="", flush=True)
    tail.append(line.rstrip()[:300])
    # the first error block, the root cause, as kaggle-tpu-lab keeps it: later lines are usually its consequences
    if not error and any(k in line for k in ("Traceback", "RESOURCE_EXHAUSTED", "Error:", "out of memory", "Killed")):
        error = [line.rstrip()[:300]]
    elif 0 < len(error) < 25:
        error.append(line.rstrip()[:300])
    if line.startswith("{"):
        try:
            ev = json.loads(line)
        except ValueError:
            continue
        if "loaded_s" in ev:
            stamp(loaded_at=datetime.now(timezone.utc).isoformat(timespec="seconds"), load_s=round(time.time() - t0, 1))
            phase = "generating"
            beat("loaded", load_s=timing["load_s"])
        elif "chunk" in ev:
            timing["chunks"].append(ev)
            stamp()
            beat("chunk", **ev)
code = proc.wait()
stamp(finished_at=datetime.now(timezone.utc).isoformat(timespec="seconds"), exit=code)
phase = "finished"
if code == 0:
    beat("finished", chunks=len(timing["chunks"]))
else:          # a negative code is the signal that killed the child (-9: SIGKILL, the OOM killer's)
    beat("failed", exit=code, error="\n".join(error), tail="\n".join(list(tail)[-15:]))
