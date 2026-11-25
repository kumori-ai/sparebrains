"""The TPU kernel's weight prefetch (2026-10-24; DECISIONS.md). Both 32B batches died at ~80 min in one "loading" phase
that hid the download inside vLLM, so the beats could not tell a stalled download from a hung initialization. Here
the pinned snapshot is fetched first, over HTTP (HF_HUB_DISABLE_XET=1: range-resumable), in its own process; no new
bytes for STALL_S kills and restarts it (resuming the partial files), at most MAX_RESTARTS times; then every file is
checked against the hub's manifest for that revision, and vLLM loads the local copy offline. prover.py inlines this
file into the kernel (Kaggle runs one file), between the kernel's hf_prefetch markers.
"""
import fnmatch, hashlib, json, os, subprocess, time, urllib.request
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

STALL_S = 300
MAX_RESTARTS = 3
WORKERS = 4
LOADS = ("*.safetensors", "*.json", "tokenizer*", "*.model", "*.tiktoken", "merges.txt", "vocab.*")
PINS = {"Goedel-LM/Goedel-Prover-V2-32B": "851bf85d329b0f819e1a44db30e05d16e07d15c0",   # hub sha read 2026-10-24
        "Goedel-LM/Goedel-Prover-V2-8B": "dfd02e6271a58375dfbf3ece0175277cf6b6a89a"}
BEAT_FILES = 40                     # files per manifest beat: ~2.2 KB, under the kernel's 3,900-byte beat cap
# Kaggle Model mirrors, mounted read-only at /kaggle/input instead of downloading (2026-11-25, #534). Four of four 32B
# batches died reading the vllm-tpu venv in /tmp after the 65 GB download landed on the same disk (a failed mmap of
# libstdc++, modules missing that the probe had just imported, an EIO); kaggle-tpu-lab mounts its 55 GB Qwen weights
# the same way. Not ours, so every file is hash-checked against PINS before vLLM loads it. Read 2026-11-25: all 23
# files the pinned revision loads, at the same sizes, plus README.md and .gitattributes.
MIRRORS = {"Goedel-LM/Goedel-Prover-V2-32B": "mykhailynabondarenko/goedel-prover-v2/transformers/32b/1"}
MOUNT_ROOTS = ("/kaggle/input",)


def _get(url):
    return urllib.request.urlopen(url, timeout=60).read().decode()


def manifest(repo, revision, fetch=_get):
    """{file: bytes} at the pinned revision, only what vLLM loads (weights, config, tokenizer)."""
    d = json.loads(fetch(f"https://huggingface.co/api/models/{repo}/revision/{revision}?blobs=true"))
    return {s["rfilename"]: s["size"] for s in d.get("siblings", [])
            if s.get("size") is not None and any(fnmatch.fnmatch(s["rfilename"], p) for p in LOADS)}


def child_cmd(py, repo, revision, local_dir, workers=WORKERS):
    """The download process: one snapshot_download, HTTP only, into local_dir (its partial files resume there)."""
    code = ("import os\nos.environ['HF_HUB_DISABLE_XET'] = '1'\nfrom huggingface_hub import snapshot_download\n"
            f"snapshot_download({repo!r}, revision={revision!r}, local_dir={str(local_dir)!r}, "
            f"allow_patterns={list(LOADS)!r}, max_workers={workers})\n")
    return lambda attempt: [py, "-c", code]


def dir_bytes(path):
    """Bytes on disk under path; a partial file renamed between listing and stat is skipped (Codex 20261024T195435827483Z)."""
    n = 0
    for f in Path(path).rglob("*"):
        try:
            if f.is_file():
                n += f.stat().st_size
        except FileNotFoundError:
            pass
    return n


def prefetch(cmd_for, watch_dir, beat=lambda event, **kw: None, stall_s=STALL_S, max_restarts=MAX_RESTARTS,
             poll_s=10, popen=subprocess.Popen, now=time.monotonic):
    """(ok, restarts, reason). Runs cmd_for(attempt) until it exits 0. No growth in watch_dir's bytes for stall_s, or a
    non-zero exit, restarts it, at most max_restarts times; a stalled child is killed (process isolation, the only
    reliable cancel)."""
    Path(watch_dir).mkdir(parents=True, exist_ok=True)
    reason = ""
    for attempt in range(max_restarts + 1):
        if attempt:
            beat("restart", attempt=attempt, reason=reason, bytes=dir_bytes(watch_dir))
        proc = popen(cmd_for(attempt), env={**os.environ, "HF_HUB_DISABLE_XET": "1"})
        try:
            last, since = dir_bytes(watch_dir), now()
            while proc.poll() is None:
                time.sleep(poll_s)
                b = dir_bytes(watch_dir)
                if b != last:
                    last, since = b, now()
                elif now() - since > stall_s:
                    reason = f"no new bytes for {stall_s} s at {b} bytes"
                    break
            else:
                if proc.returncode == 0:
                    return True, attempt, ""
                reason = f"download process exit {proc.returncode}"
        finally:                                         # whatever happened, no download child outlives its turn
            if proc.poll() is None:
                proc.kill()
                proc.wait()
    return False, max_restarts, reason


def verify(local_dir, man):
    """Every manifest file present at its exact size: [] when complete, else what is missing or short."""
    bad = []
    for name, size in sorted(man.items()):
        p = Path(local_dir) / name
        if not p.exists():
            bad.append(f"{name}: missing")
        elif p.stat().st_size != size:
            bad.append(f"{name}: {p.stat().st_size} of {size} bytes")
    return bad


def hashes(repo, revision, fetch=_get):
    """{file: (kind, hex)} at the pinned revision for what vLLM loads: the LFS sha256, else the git blob sha1."""
    d = json.loads(fetch(f"https://huggingface.co/api/models/{repo}/revision/{revision}?blobs=true"))
    return {s["rfilename"]: ("sha256", s["lfs"]["sha256"]) if (s.get("lfs") or {}).get("sha256") else ("gitsha1", s["blobId"])
            for s in d.get("siblings", []) if any(fnmatch.fnmatch(s["rfilename"], p) for p in LOADS)}


def _digest(path, kind):
    h = hashlib.sha256() if kind == "sha256" else hashlib.sha1(b"blob %d\0" % path.stat().st_size)
    with open(path, "rb") as f:
        while chunk := f.read(1 << 24):
            h.update(chunk)
    return h.hexdigest()


def verify_hashes(local_dir, hs, expect, workers=8):
    """Every file present with the pinned revision's hash: [] when it matches, else what is missing or differs. A hash
    list that is empty or does not cover exactly the manifest (`expect`) never passes (Codex 20261125T182811031376Z f1)."""
    if not hs or set(hs) != set(expect):
        return [f"hash list ({len(hs)} files) does not match the manifest ({len(expect)} files)"]
    def one(item):
        name, (kind, want) = item
        p = Path(local_dir) / name
        if not p.is_file():
            return f"{name}: missing"
        return None if _digest(p, kind) == want else f"{name}: {kind} differs"
    with ThreadPoolExecutor(workers) as ex:                 # hashlib releases the GIL: the shards hash in parallel
        return [b for b in ex.map(one, sorted(hs.items())) if b]


def find_mounted(man, roots=MOUNT_ROOTS, depth=6):
    """The first directory under roots holding every manifest file at its exact size (Kaggle mounts a model at
    /kaggle/input/<slug>/<framework>/<instance>/<version> or under models/<owner>/...), else None."""
    if not man:                                          # an empty manifest matches any directory
        return None
    for root in roots:
        root = str(root)
        for d, dirs, files in os.walk(root):
            if d[len(root):].count(os.sep) >= depth:
                dirs.clear()
            if "config.json" in files and not verify(d, man):
                return d
    return None


def parts(man, n=BEAT_FILES):
    """The manifest in numbered beats small enough that none is cut down to its bare fields."""
    items = sorted(man.items())
    chunks = [items[i:i + n] for i in range(0, len(items), n)] or [[]]
    return [{"part": i + 1, "of": len(chunks), "files": dict(c)} for i, c in enumerate(chunks)]
