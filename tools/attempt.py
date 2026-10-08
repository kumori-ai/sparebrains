"""The loop. Ask the free pool for proofs, let the kernel grade them, keep every receipt.

    python3 tools/attempt.py --ladder --jobs 2 --max-minutes 320          # what the schedule runs
    python3 tools/attempt.py --ladder --plan                                # print the queue, call nothing
    python3 tools/attempt.py --sample 5 --seed 1 --order asc --stop-on-accept --max-calls 300
    python3 tools/attempt.py --sample 30 --seed 2 --min-tier medium --skip-benched --jobs 2 --max-calls 1400

--ladder is the 24/7 mode (2026-09-02): every lane, every target of every set, --attempts
tries per (target, lane) cell, first tries of the whole ladder before anyone's second try,
rungs in order (tools/ladder.py). The queue is whatever the git ledger says is still owed;
a job works until its wall-clock budget, and the workflow chains the next one. Lanes the
router is benching are left in the queue for later, never recorded as skipped.

The older modes stay for hand runs: lanes walked by quality tier (tiny → frontier, or
reversed with --order desc); --stop-on-accept stops a target at its first kernel-verified
proof, so the ledger records the cheapest brain that solved it; without it every lane gets
every target. Each attempt writes one compact line to the git ledger and posts its full
transcript to kumori's sparebrains_attempts table. Accepted proofs are saved whole under
verified/.
"""
import argparse, hashlib, json, os, random, re, sys, threading, time, uuid
from collections import defaultdict, deque
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT), str(ROOT / "tools")]
from check import judge                                              # the judge, unchanged
from ladder import (rung_of, failure_kind, sort_key, RUNGS, error_scope, lane_is_gone, ALIVE_WINDOW_S,
                    owed_history, build_ladder_queue, interleave_by_provider)   # the ladder's queue, read from the committed ledger
import relay                                                         # stage 2: tries from a problem's dossier
import lean_tools                                                     # real mathlib names for invented ones
import subgoals                                                      # APOLLO's loop on a rejected relay try
import fixer                                                         # issue #3: repairs form, no model
from proof_text import extract_proof, align_tactics, PROOF_SEP                 # what a reply hands to Lean
from utilities.kumori_api_client import (KumoriAPIError, init as kumori_init, llm_backends, llm_backoff_state,
                                         llm_chat, sparebrains_attempt)
MISSING = []                                                          # client functions this checkout lacks: said out loud, never silent
try:                                                                  # the clock on the site
    from utilities.kumori_api_client import sparebrains_heartbeat
except ImportError:
    MISSING.append("sparebrains_heartbeat (the site's clock and Right-now box will stay empty)")
    def sparebrains_heartbeat(row):
        return None
try:                                                                  # what a repair try is told
    from utilities.kumori_api_client import sparebrains_previous
except ImportError:
    MISSING.append("sparebrains_previous (repair tries would run cold; they are labeled cold when that happens)")
    def sparebrains_previous(target_set, target, backend):
        return None

TIER_RANK = {"tiny": 0, "low": 1, "medium": 2, "high": 3, "frontier": 4}
RUNNER_PATH = re.compile(r"\S*/\.lake/attempts/\S+?\.lean:")     # keep "line:col: error: …", drop the path
MIN_ANSWERED_TO_COUNT_SWEPT = 8   # a target is "swept" only once this many lanes actually answered it
SITE = "https://sparebrains.kumori.ai"
SYSTEM = ("You are an expert in Lean 4 and Mathlib. You complete formal proofs. "
          "You answer with code only.")
EXAMPLE = ("import Mathlib\n\n/-- A demonstration, not a target. -/\n"
           "theorem demo_mul_two (n : ℕ) : n * 2 = n + n := by\n  ring\n")
REPAIR = ("You already tried this Lean 4 file (Lean v4.33.1, mathlib v4.33.1, `import Mathlib` is already "
          "there) and the kernel rejected your proof. Fix it. Replace only the `sorry`; keep the theorem statement "
          "byte-for-byte; no `sorry`, `admit`, or `native_decide`; no new axioms; Lean 4 syntax, not Lean 3. "
          "Answer with the ENTIRE file inside one ```lean fence and nothing else.\n\n")
ASK = ("Complete the proof in this Lean 4 file (Lean v4.33.1, mathlib v4.33.1, `import Mathlib` is "
       "already there). Replace only the `sorry` with a complete proof.\n"
       "Rules: keep the theorem statement byte-for-byte; no `sorry`, `admit`, or `native_decide`; "
       "no new axioms; Lean 4 syntax, not Lean 3.\n"
       "Answer with the ENTIRE file inside one ```lean fence and nothing else. "
       "This is the exact shape of a correct answer, for a different theorem:\n\n"
       "```lean\n" + EXAMPLE + "```\n\nNow the file to complete:\n\n")


ERROR_STREAK_TO_PARK = 3      # failures in a row before a lane is parked (60 s, doubling to 30 min)


RUNNING_DRY = set()   # lanes whose recent calls mostly came back empty, from the ledger at job start


def lane_effort(lane):
    """Thinking models are asked for medium reasoning effort, and for low when they keep coming back
    empty (DECISIONS.md 2026-10-07): at 16,000 tokens and medium they still ran out mid-thought."""
    if not (lane.get("capability") or {}).get("is_reasoning_model"):
        return None
    return "low" if lane.get("backend") in RUNNING_DRY else relay.REASONING_EFFORT


def lane_max_tokens(lane, default):
    """A thinking model gets relay.MAX_TOKENS in every mode (DECISIONS.md 2026-10-07): at the ladder's
    4,000 apodex-1-1-mini ran out of thought before writing a word on 120 calls in one day."""
    return max(default, relay.MAX_TOKENS) if (lane.get("capability") or {}).get("is_reasoning_model") else default


def bench_delay(retry_after, consecutive):
    """Repeated refusals park a lane longer, never less than the router asks."""
    minimum = max(5, retry_after or 60)
    return max(minimum, min(1800, minimum * 2 ** min(max(0, consecutive - 1), 9)))


def public_record_ok(lane):
    """DECISIONS.md 2026-09-02: two provider groups may not appear in a public, Apache-2.0 record.
    Cohere's Terms of Use bar benchmarking and distributing anything the API returns; NVIDIA's API
    Trial ToS is trial-only and bars letting others use generated content competitively, which an
    open license cannot promise. The router keeps these lanes for other apps; this loop never asks
    them. Narrow the Nemotron rule if a non-trial free host ever serves those weights."""
    model = (lane.get("model") or "").lower()
    provider = (lane.get("provider") or "").lower()
    if provider == "cohere" or model.startswith("cohere/"):
        return False
    if provider == "nvidia" or model.startswith("nvidia/") or "nemotron" in model:
        return False
    return True


def lanes(explicit, min_tier=None, skip_benched=False):
    """Live chat lanes, ordered by quality tier. Shape of a backend dict is logged once.
    min_tier drops everything below it (and every untiered lane); skip_benched drops lanes
    the router's circuit breaker currently refuses, instead of spending a call to learn it."""
    raw = llm_backends()
    if raw:
        print("backend[0] =", json.dumps(raw[0])[:400])
    out = []
    for b in raw:
        name = b.get("name") or b.get("backend")
        if (not name or b.get("enabled") is False or b.get("modality") not in (None, "chat")
                or b.get("lifecycle_status") not in (None, "active", "probationary", "revived")):
            continue
        tier = (b.get("quality_tier") or "unknown").lower()
        out.append({"backend": name, "provider": b.get("provider") or b.get("route") or name.split("-")[0],
                    "model": b.get("model"), "tier": tier, "rank": TIER_RANK.get(tier, -1),
                    "capability": {k: b.get(k) for k in (
                        "is_reasoning_model", "supports_thinking", "reasoning_sources", "model_slug",
                        "model_identity_kind", "reasoning_effort_control")}})
    if explicit:
        want = [x.strip() for x in explicit.split(",") if x.strip()]
        known = {l["backend"]: l for l in out}
        missing = [w for w in want if w not in known]
        if missing:
            raise ValueError(f"Requested lanes are absent from the live eligible catalog: {', '.join(missing)}")
        out = [known[w] for w in want]
    barred = [l["backend"] for l in out if not public_record_ok(l)]
    out = [l for l in out if public_record_ok(l)]
    print(f"skipping {len(barred)} lane(s) whose provider terms forbid a public record: {', '.join(barred) or 'none'}")
    if skip_benched:
        state = llm_backoff_state()
        benched = {n for n, d in state.items() if d.get("backed_off")}
        dropped = [l["backend"] for l in out if l["backend"] in benched]
        out = [l for l in out if l["backend"] not in benched]
        print(f"skipping {len(dropped)} benched lane(s): {', '.join(dropped) or 'none'}")
    if min_tier:
        floor = TIER_RANK[min_tier]
        out = [l for l in out if l["rank"] >= floor]
    known = sorted((l for l in out if l["rank"] >= 0), key=lambda l: (l["rank"], l["backend"]))
    unknown = sorted((l for l in out if l["rank"] < 0), key=lambda l: l["backend"])
    return known, unknown                                # untiered lanes always go last


def repair_prompt(target_text, prev):
    """Tries two and three of a cell whose earlier try was rejected: the lane sees its own
    proof and the kernel's exact complaint. A reply with no code block gets told that instead."""
    if prev.get("failure_kind") == "no_fence" or not prev.get("proof"):
        head = (prev.get("response_head") or "").strip()
        note = ("Your previous reply contained no ```lean code block, so nothing could be checked. It began:\n\n"
                + head[:600] + ("\n…" if len(head) > 600 else "") + "\n\n")
    else:
        out = (prev.get("lean_output") or prev.get("reason") or "").strip()
        note = ("Your previous proof was:\n\n```lean\n" + prev["proof"].rstrip() + "\n```\n\nLean said:\n\n```\n"
                + out[:2000] + ("\n…" if len(out) > 2000 else "") + "\n```\n\n")
    return REPAIR + note + "The file to complete:\n\n" + target_text


def load_sets(spec):
    """[(target_set, dir, [names])] for a comma-separated list of sets under targets/."""
    out = []
    for item in [x.strip() for x in spec.split(",") if x.strip()]:
        tdir = ROOT / "targets" / item
        names = sorted(p.stem for p in tdir.glob("*.lean"))
        if names:
            out.append((item, tdir, names))
        else:
            print(f"set {item}: no targets on disk, skipped")
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--ladder", action="store_true",
                    help="the 24/7 mode: every lane × every target of --sets, --attempts tries per cell, owed cells only")
    ap.add_argument("--sets", default="primer,mil,minif2f/test", help="ladder mode: target sets under targets/, in rung order")
    ap.add_argument("--max-minutes", type=float, default=0, help="ladder mode: stop taking new cells after this wall clock (0 = no limit)")
    ap.add_argument("--idle-minutes", type=float, default=20, help="ladder mode: give up after this long with nothing answerable")
    ap.add_argument("--plan", action="store_true", help="ladder mode: print the queue and exit without a call")
    ap.add_argument("--relay", action="store_true",
                    help="stage 2: the strongest live lanes try --only targets (in --targets) from each problem's dossier")
    ap.add_argument("--relay-lanes", type=int, default=5, help="relay mode: how many of the strongest live lanes")
    ap.add_argument("--relay-next", action="store_true",
                    help="relay mode: take the first open problem in the stage-2 order that still has relay tries left")
    ap.add_argument("--fixer", action="store_true",
                    help="issue #3: re-check --only targets' closest misses with their layout fixed; no model call")
    ap.add_argument("--fixer-ask", action="store_true",
                    help="fixer mode: a near miss's steps Lean's automation leaves open go to the lane that wrote it, "
                         "if it is live (tools/subgoals.py); counts against --max-calls")
    ap.add_argument("--targets", default="targets/minif2f/test")
    ap.add_argument("--only", default="", help="comma-separated target names (overrides --sample)")
    ap.add_argument("--unattempted", action="store_true",
                    help="take the first --sample targets no sweep run has touched (alphabetical); exit 0 when none remain")
    ap.add_argument("--sample", type=int, default=5)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--lanes", default="", help="comma-separated backend names (default: every live lane)")
    ap.add_argument("--min-tier", choices=list(TIER_RANK), default=None, help="drop lanes below this tier")
    ap.add_argument("--skip-benched", action="store_true", help="drop lanes the router currently refuses")
    ap.add_argument("--jobs", type=int, default=1, help="parallel attempts; ladder preserves queue order while workers overlap calls")
    ap.add_argument("--max-per-provider", type=int, default=0,
                    help="keep at most N lanes per provider, highest tier first (0 = all); the Mistral list is 28 aliases of a few models")
    ap.add_argument("--order", choices=["asc", "desc"], default="asc")
    ap.add_argument("--stop-on-accept", action="store_true")
    ap.add_argument("--attempts", type=int, default=1)
    ap.add_argument("--max-calls", type=int, default=300, help="hard stop on calls (ladder mode: 5000 unless set)")
    ap.add_argument("--max-tokens", type=int, default=4000)
    ap.add_argument("--call-timeout", type=int, default=180)
    ap.add_argument("--lean-timeout", type=int, default=300)
    ap.add_argument("--pace", type=float, default=1.0)
    args = ap.parse_args()

    if not os.environ.get("KUMORI_API_KEY"):
        sys.exit("KUMORI_API_KEY is not set")
    for m in MISSING:
        print(f"WARNING: the vendored kumori client lacks {m}; run 2026-09-02's __init__ export fix through `deploy`", flush=True)
        summary = os.environ.get("GITHUB_STEP_SUMMARY")
        if summary:
            with open(summary, "a") as fh:
                fh.write(f"> **WARNING:** vendored client lacks {m}\n\n")
    kumori_init(min_inter_call_sec=args.pace)
    run_id = os.environ.get("GITHUB_RUN_ID") or datetime.now(timezone.utc).strftime("local-%Y%m%dT%H%M%S")
    tdir = ROOT / args.targets
    target_set = str(Path(args.targets).relative_to("targets"))
    names = sorted(p.stem for p in tdir.glob("*.lean"))
    sets = []
    if args.ladder:
        sets = load_sets(args.sets)
        names = [n for _, _, ns in sets for n in ns]
        if args.max_calls == 300:
            args.max_calls = 5000
    elif args.only:
        names = [n.strip() for n in args.only.split(",") if n.strip()]
    elif args.unattempted:
        answered = defaultdict(int)          # target → lanes that actually answered in sweep runs
        for f in (ROOT / "ledger" / target_set).glob("*.jsonl"):
            for line in f.read_text().splitlines():
                try:
                    r = json.loads(line)
                except ValueError:
                    continue
                if str(r.get("mode", "")).startswith("sweep") and r.get("verdict") in ("accept", "reject"):
                    answered[r["target"]] += 1
        swept = {t for t, k in answered.items() if k >= MIN_ANSWERED_TO_COUNT_SWEPT}
        remaining = [n for n in names if n not in swept]
        print(f"unattempted: {len(remaining)} of {len(names)} targets not yet swept")
        if not remaining:
            print("all targets swept; nothing to do")
            return 0
        names = remaining[:args.sample]
    else:
        names = random.Random(args.seed).sample(names, min(args.sample, len(names)))
    known, unknown = lanes(args.lanes, args.min_tier, args.skip_benched)
    ledger_rows = [json.loads(l) for f in (ROOT / "ledger").glob("**/*.jsonl")
                   for l in f.read_text().splitlines() if l.strip()]
    RUNNING_DRY.update(l["backend"] for l in known + unknown if relay.running_dry(ledger_rows, l["backend"]))
    for b in sorted(RUNNING_DRY):
        print(f"  {b}: most recent calls came back empty; asked for low reasoning effort")
    if args.max_per_provider:
        kept, seen = [], defaultdict(int)
        for l in sorted(known, key=lambda l: (-l["rank"], l["backend"])):   # strongest first within a provider
            if seen[l["provider"]] < args.max_per_provider:
                kept.append(l)
                seen[l["provider"]] += 1
        dropped = len(known) - len(kept)
        known = sorted(kept, key=lambda l: (l["rank"], l["backend"]))
        print(f"max {args.max_per_provider} lanes per provider: kept {len(known)}, dropped {dropped}")
    order = (known[::-1] if args.order == "desc" else known) + unknown
    mode = f"{'ladder' if args.stop_on_accept else 'sweep'}-{args.order}"
    if args.ladder:
        order = sorted(known, key=lambda l: (-l["rank"], l["backend"])) + unknown     # strongest first, untiered last
        mode = f"ladder-x{args.attempts}"
    live_lanes = {l["backend"]: l for l in known + unknown}   # the fixer's asks go to a near miss's own lane
    if args.fixer:
        if not args.only:
            sys.exit("--fixer needs --only")
        order, mode = [], "fixer"
    if args.relay:
        if not (args.only or args.relay_next):
            sys.exit("--relay needs --only or --relay-next")
        strength = relay.lane_strength(ledger_rows, RUNGS)
        now_iso = datetime.now(timezone.utc).isoformat()
        benched_out = [l["backend"] for l in known + unknown if relay.relay_benched(ledger_rows, l["backend"], now_iso)]
        for b in benched_out:
            print(f"  {b}: its last {relay.BENCH_LAST} relay calls all came back empty; out of the relay for {relay.BENCH_DAYS} days")
        order = relay.strongest([l for l in known + unknown if l["backend"] not in benched_out], strength, args.relay_lanes)
        if not order:
            sys.exit("relay: no live lane has a solve above MATH level 2 in the ledger")
        args.attempts = relay.RELAY_TRIES
        if args.max_tokens == 4000:                      # the ladder's default; reasoning lanes need room
            args.max_tokens = relay.MAX_TOKENS
        mode = "relay"
        for l in order:
            print(f"  relay lane {l['backend']}: {strength[l['backend']]} targets proved above MATH level 2")
        fixed_ids = {r.get("prev_id") for r in ledger_rows if r.get("try_mode") == "fixer+loop"}   # once per near miss
        by_problem = relay.problem_rows(ledger_rows)               # rounds: the swarm (DECISIONS.md 2026-10-08)
        people = (relay.load_people(os.environ["SB_PEOPLE_FILE"]) if os.environ.get("SB_PEOPLE_FILE")
                  else relay.people_comments())
        if args.relay_next:
            pick = relay.next_problem(relay.fetch_json("/targets.json")["open"], order, by_problem, people)
            names = [pick[1]] if pick else []
            if pick:
                target_set, tdir = pick[0], ROOT / "targets" / pick[0]
                print(f"relay: next open problem with tries left is {target_set}/{pick[1]}")
            else:
                print("relay: no open problem has news since its last round, or every one is resting")
    lane_manifest = [{k: l[k] for k in ("backend", "provider", "model", "tier", "rank")} for l in order]
    lane_roster_sha = hashlib.sha256(json.dumps(lane_manifest, sort_keys=True).encode()).hexdigest()[:12]
    t_start = time.time()
    print(f"run {run_id}: {len(names)} targets × {len(order)} lanes × {args.attempts} attempts, "
          f"mode {mode}, cap {args.max_calls} calls")
    for l in order:
        print(f"  lane {l['backend']:40s} tier={l['tier']:8s} model={l['model']}")

    def ledger_for(tset):
        path = ROOT / "ledger" / tset / f"{run_id}.jsonl"
        path.parent.mkdir(parents=True, exist_ok=True)
        return path
    ledger = ledger_for(target_set)
    tmpdir = ROOT / ".lake" / "attempts"
    tmpdir.mkdir(parents=True, exist_ok=True)
    lock = threading.Lock()
    # The git ledger is the durable record and is written synchronously. The site transcript and
    # heartbeat posts are useful telemetry, but must not make every model/Lean attempt wait on an
    # HTTP round trip. Bound the queue so a slow site cannot consume unbounded runner memory; it
    # drains before the job exits, preserving the public transcript record.
    telemetry = ThreadPoolExecutor(max_workers=2, thread_name_prefix="sparebrains-telemetry")
    telemetry_slots = threading.BoundedSemaphore(32)
    telemetry_futures = []

    def submit_telemetry(fn, *fn_args):
        telemetry_slots.acquire()
        future = telemetry.submit(fn, *fn_args)
        future.add_done_callback(lambda _: telemetry_slots.release())
        with lock:
            telemetry_futures.append(future)
        return future

    def drain_telemetry():
        with lock:
            futures = list(telemetry_futures)
        for future in futures:
            try:
                future.result()
            except Exception as e:
                print(f"telemetry worker failed: {type(e).__name__}: {e}", flush=True)
        telemetry.shutdown(wait=True)

    def previous_id(prev):
        """Resolve a background transcript insert only when a repair row needs its parent id."""
        if not prev:
            return None
        future = prev.get("telemetry_future")
        if future:
            try:
                saved = future.result(timeout=35) or {}
                if saved.get("id"):
                    prev["id"] = saved["id"]
            except Exception as e:
                print(f"previous transcript id unavailable: {type(e).__name__}: {e}", flush=True)
        return prev.get("id")
    state = {"calls": 0, "accepts": 0, "errors": 0, "skipped": 0, "waits": 0}
    solved = {}
    per_target = {n: {"done": 0, "accepts": 0, "errors": 0, "lanes": []} for n in names}
    per_lane = {l["backend"]: {"tier": l["tier"], "attempts": 0, "accepts": 0, "errors": 0} for l in order}
    planned_per_target = len(order) * args.attempts
    provider_lock = defaultdict(threading.Lock)          # never two workers on one provider at once
    bench = {"t": 0.0, "state": {}, "told": {}, "streak": {}, "gone": set()}   # told: backend → monotonic time the router said to come back
                                                         # gone: lanes the router 404s, not asked again this job
    exhausted = {}                                       # provider → why it is parked for the rest of the run

    def benched(backend):
        """Router bench state, refreshed at most every 30 s. True = the router would 503 this lane now.
        A refusal's own Retry-After is a minimum. Repeated refusals extend the local
        wait so permanently rate-limited providers are not retried every two minutes."""
        now = time.monotonic()
        with lock:
            if bench["told"].get(backend, 0) > now:
                return True
            if now - bench["t"] > 30:
                try:
                    bench["state"] = llm_backoff_state() or {}
                except Exception as e:
                    print(f"bench state unavailable ({e}); assuming nothing is benched", flush=True)
                bench["t"] = now
            d = bench["state"].get(backend, {})
        return bool(d.get("backed_off")) and (d.get("remaining_sec") or 0) > 0

    def record(row, prompt=None, reply=None, proof=None, candidate=None, lean_out=None):
        with lock:
            with ledger_for(row["target_set"]).open("a") as fh:
                fh.write(json.dumps(row) + "\n")
        return submit_telemetry(sparebrains_attempt, {**row, "prompt": prompt, "response": reply, "proof": proof,
                                                       "candidate": candidate, "lean_output": lean_out})

    def base_row(name, lane, attempt_no, statement_sha, tset=None):
        tset = tset or target_set
        rung, rank = rung_of(tset, name)
        return {"ts": datetime.now(timezone.utc).isoformat(timespec="seconds"), "run_id": run_id,
                "target_set": tset, "target": name, "statement_sha": statement_sha, "rung": rung, "rung_rank": rank,
                "backend": lane["backend"], "provider": lane["provider"], "model": lane["model"],
                "quality_tier": lane["tier"], "tier_rank": lane["rank"], "attempt_no": attempt_no, "mode": mode,
                "capability": lane.get("capability", {}),
                "request_config": {"max_tokens": lane_max_tokens(lane, args.max_tokens), "temperature": 0.2,
                                   "reasoning_effort": lane_effort(lane), "router_timeout_s": 60,
                                   "client_read_timeout_s": args.call_timeout,
                                   "lean_timeout_s": args.lean_timeout}}

    def skip(name, lane, attempt_no, why):
        """A pair the router would refuse: recorded honestly, no model call, no Lean."""
        target_text = (tdir / f"{name}.lean").read_text()
        prefix = target_text[:PROOF_SEP.search(target_text).end()]
        row = {**base_row(name, lane, attempt_no, hashlib.sha256(prefix.encode()).hexdigest()),
               "verdict": "skipped", "reason": why, "call_seconds": 0.0, "lean_seconds": 0.0,
               "response_chars": 0, "proof_sha": None}
        with lock:
            state["skipped"] += 1
            t = per_target[name]
            t["done"] += 1
            target_done = (not args.stop_on_accept) and t["done"] >= planned_per_target
        record(row)
        print(f"[skip] {name} ← {lane['backend']} ({lane['tier']}): {why}", flush=True)
        if target_done:
            who = ", ".join(t["lanes"]) if t["lanes"] else "nobody"
            print(f"[target done] {name}: {t['accepts']}/{t['done']} lanes proved it ({t['errors']} lane errors) — {who}",
                  flush=True)

    memory = {}                                          # (set, target, backend) → what this job learned, for repair tries

    def run_one(name, lane, attempt_no, tset=None, tdir_=None, prev=None, relay_ctx=None):
        """One attempt: ask (honoring retry-after once), splice, judge, record. Returns the verdict,
        or 'defer' when the router benched the lane between the pre-check and the call.
        With `prev` (the cell's last rejected attempt) the ask is a repair try."""
        tset, tdir_ = tset or target_set, tdir_ or tdir
        target_text = (tdir_ / f"{name}.lean").read_text()
        prefix = target_text[:PROOF_SEP.search(target_text).end()]
        statement_sha = hashlib.sha256(prefix.encode()).hexdigest()
        repair = bool(prev) and prev.get("verdict") == "reject"
        prompt = repair_prompt(target_text, prev) if repair else ASK + target_text
        meta = None
        if relay_ctx:                                    # stage 2: the dossier, never a known proof
            prompt, meta = relay.relay_prompt(target_text, relay_ctx["dossier"], relay_ctx["this_job"],
                                              relay_ctx.get("real_names"))
        # a relay try may think for minutes (kumori's opt-in long_call, sparebrains keys only)
        long_or_not = {"timeout_s": relay.LONG_CALL_S, "long_call": True} if relay_ctx else {"timeout_s": 60}
        if lane_effort(lane):
            long_or_not["reasoning_effort"] = lane_effort(lane)
        t0 = time.monotonic()
        reply, err = "", None
        returned_backend, inference = None, {}
        with provider_lock[lane["provider"]]:
            # Another worker may have benched this lane while we waited for the provider.
            if benched(lane["backend"]):
                return "defer"
            for tries in (1, 2):
                try:
                    reply, returned_backend, inference = llm_chat(lane["backend"], [{"role": "user", "content": prompt}],
                                        max_tokens=lane_max_tokens(lane, args.max_tokens), temperature=0.2, system=SYSTEM,
                                        app_name="sparebrains", timeout=(10, args.call_timeout),
                                        include_metadata=True, **long_or_not,
                                        request_id=uuid.uuid4().hex)  # a proof cut off at 100 s is fetched, not lost
                    with lock:
                        bench["streak"].pop(lane["backend"], None)
                        bench["told"].pop(lane["backend"], None)
                    err = None
                    break
                except KumoriAPIError as e:
                    msg = str(e)
                    if (e.payload or {}).get("reason") == "held_for_others":
                        # kumori 9dfd540: the pool's rest is held for tenants still owed their share, and the
                        # hold shrinks through the day, so park this provider's lanes only as long as it says
                        wait = max(5, e.retry_after or 900)
                        with lock:
                            until = time.monotonic() + wait
                            for other in order:
                                if other["provider"] == lane["provider"]:
                                    bench["told"][other["backend"]] = max(bench["told"].get(other["backend"], 0), until)
                        print(f"{lane['provider']}: share held for other tenants; parked for {wait:.0f}s", flush=True)
                        return "defer"
                    if "spent its share" in msg or "is gated" in msg:
                        with lock:                        # the router's fair-share or pool gate: done for today
                            exhausted[lane["provider"]] = msg.split(" : ", 1)[-1][:120]
                        return "exhausted"
                    if "is benched" in msg:              # the router's gate refused: wait as long as it says
                        with lock:
                            count = bench["streak"].get(lane["backend"], 0) + 1
                            bench["streak"][lane["backend"]] = count
                            wait = bench_delay(e.retry_after, count)
                            bench["told"][lane["backend"]] = time.monotonic() + wait
                        print(f"{lane['backend']}: refusal {count}; parked for {wait:.0f}s", flush=True)
                        return "defer"
                    limited = e.status_code == 429 or "rate limit" in msg.lower() or "RPM spacing" in msg
                    if tries == 1 and limited and e.retry_after and e.retry_after <= 90:
                        with lock:
                            state["waits"] += 1
                        time.sleep(e.retry_after + 0.5)   # the router said when; wait and ask once more
                        continue
                    err = f"KumoriAPIError: {msg[:200]}"
                    break
                except Exception as e:
                    err = f"{type(e).__name__}: {str(e)[:200]}"
                    break
            if err:
                # A lane that keeps failing is parked like a refused one, and a lane the router no
                # longer routes is dropped for the job. Without this, run 35481806786 asked one dead
                # lane 1,702 times in under two hours (2026-09-20).
                with lock:
                    if lane_is_gone(err):
                        if lane["backend"] not in bench["gone"]:
                            print(f"{lane['backend']}: the router does not route this lane now; dropped for this job", flush=True)
                        bench["gone"].add(lane["backend"])
                    else:
                        count = bench["streak"].get(lane["backend"], 0) + 1
                        bench["streak"][lane["backend"]] = count
                        if count >= ERROR_STREAK_TO_PARK:
                            wait = bench_delay(60, count - ERROR_STREAK_TO_PARK + 1)
                            bench["told"][lane["backend"]] = time.monotonic() + wait
                            print(f"{lane['backend']}: {count} failures in a row; parked for {wait:.0f}s", flush=True)
        with lock:
            state["calls"] += 1
            n = state["calls"]
        call_s = time.monotonic() - t0
        proof = extract_proof(reply or "", name) if reply else None
        candidate = lean_out = None
        tools_used = {}
        lean_s = 0.0
        if err:
            verdict, reason = "error", err
        elif not proof:
            verdict, reason = "reject", "no proof extracted from reply"
        else:
            candidate = prefix + "\n" + proof
            cpath = tmpdir / f"{name}.{lane['backend']}.{attempt_no}.lean"
            cpath.write_text(candidate)
            verdict, reason, lean_s, lean_out = judge(str(cpath), args.lean_timeout)
            reason = RUNNER_PATH.sub("", reason)
            if verdict == "wellformed":
                verdict, reason = "reject", "proof still contains sorry"
            if relay_ctx and verdict == "reject":       # APOLLO's loop: holes, Lean's closers, the same model per step
                t_rep = time.monotonic()
                rep = subgoal_repair(name, lane, attempt_no, tset, statement_sha, prefix, candidate, lean_out)
                tools_used = {"subgoals": {**{k: v for k, v in rep.items() if k not in ("accepted", "sketch", "lean_output")},
                                           "seconds": round(time.monotonic() - t_rep, 1)}}
                if rep.get("accepted"):
                    candidate, lean_out = rep["accepted"], rep.get("lean_output") or lean_out
                    proof = candidate[len(prefix):].lstrip("\n")
                    verdict = "accept"
                    reason = (f"kernel accepted after the loop: {rep.get('closed_by_lean', 0)} step(s) closed by Lean's "
                              f"automation, {rep.get('lemmas_proved', 0)} proved by the model as lemmas")
                elif rep.get("sketch"):
                    tools_used["sketch"] = rep["sketch"]
        row = {**base_row(name, lane, attempt_no, statement_sha, tset), "verdict": verdict, "reason": reason[:300],
               "returned_backend": returned_backend, "inference": inference,
               "failure_kind": failure_kind(verdict, reason),
               "try_mode": "repair" if repair else "cold", "prev_id": previous_id(prev) if repair else None,
               **({k: meta[k] for k in ("try_mode", "prev_id", "comment_ids", "dossier_sha")} if meta else {}),
               "call_seconds": round(call_s, 1), "lean_seconds": round(lean_s, 1),
               "response_chars": len(reply or ""),
               "proof_sha": hashlib.sha256(proof.encode()).hexdigest() if proof else None}
        if relay_ctx:                                    # which tools this try had, for the digest and the before/after
            row["tools"] = {"names_shown": sorted((relay_ctx.get("real_names") or {}))[:12],
                            **{k: v for k, v in tools_used.items() if k != "sketch"}}
        with lock:
            t, pl = per_target[name], per_lane[lane["backend"]]
            t["done"] += 1
            pl["attempts"] += 1
            if verdict == "accept":
                state["accepts"] += 1
                solved.setdefault(name, lane)
                t["accepts"] += 1
                pl["accepts"] += 1
                t["lanes"].append(lane["backend"])
            elif verdict == "error":
                state["errors"] += 1
                t["errors"] += 1
                pl["errors"] += 1
            target_done = (not args.stop_on_accept) and t["done"] >= planned_per_target
        telemetry_future = record(row, prompt, reply, proof, candidate, lean_out)
        if relay_ctx and verdict == "reject" and proof:
            said = RUNNER_PATH.sub("", lean_out or reason)
            sg = tools_used.get("subgoals") or {}
            if tools_used.get("sketch"):                 # the next lane starts from what Lean already accepted
                said += (f"\nAfter this try, Lean's automation closed {sg.get('closed_by_lean', 0)} failing step(s). "
                         "What still needs a proof is each `sorry` in:\n" + tools_used["sketch"][len(prefix):][-2500:])
            relay_ctx["this_job"].append((lane["backend"], row["failure_kind"], proof, said))
            look_up_names(relay_ctx, fixer.UNKNOWN.findall(lean_out or ""))   # names this try just invented
        if verdict in ("accept", "reject"):
            with lock:
                memory[(tset, name, lane["backend"])] = {"id": None, "verdict": verdict, "failure_kind": row["failure_kind"],
                                                         "reason": reason, "proof": proof, "lean_output": lean_out,
                                                         "response_head": (reply or "")[:800],
                                                         "telemetry_future": telemetry_future}
        print(f"[{n}/{args.max_calls}] {name} ← {lane['backend']} ({lane['tier']}) → {verdict}"
              f"{' (repair)' if repair else ''}{' (' + meta['try_mode'] + ')' if meta else ''}  call {call_s:.0f}s lean {lean_s:.1f}s  {reason[:110]}", flush=True)
        if verdict == "accept":
            vpath = ROOT / "verified" / tset / name / f"{lane['backend']}.lean"
            vpath.parent.mkdir(parents=True, exist_ok=True)
            vpath.write_text(candidate)
            print("    ┌ kernel-accepted proof, verbatim:\n" +
                  "\n".join("    │ " + l for l in proof.rstrip("\n").splitlines()) + "\n    └", flush=True)
        if target_done:
            t = per_target[name]
            who = ", ".join(t["lanes"]) if t["lanes"] else "nobody"
            print(f"[target done] {name}: {t['accepts']}/{t['done']} lanes proved it ({t['errors']} lane errors) — {who}",
                  flush=True)
        if n % 25 == 0:
            if state.get("heartbeat"):
                state["heartbeat"]()
            with lock:
                print(f"[tally] {n} calls · {state['accepts']} verified · {state['errors']} lane errors · "
                      f"{state['skipped']} skipped (benched) · {state['waits']} rate-limit waits · "
                      f"{len(solved)}/{len(names)} targets solved so far", flush=True)
        if verdict == "error" and error_scope(reason) == "router":
            return "error_router"                        # says nothing about this lane on this target
        return verdict

    def subgoal_repair(name, lane, attempt_no, tset, statement_sha, prefix, candidate, lean_out, try_mode="relay-subgoal"):
        """tools/subgoals.py on one rejected relay try. Its model calls go to the same lane and count against
        --max-calls; each lemma it asks for is its own ledger row (try_mode relay-subgoal, verdict
        lemma-accept / lemma-reject), so the loop's work is as public as the try itself."""
        def ask(prompt):
            with lock:
                if state["calls"] >= args.max_calls:
                    return None
            if lane["provider"] in exhausted or benched(lane["backend"]):
                return None
            extra = {"reasoning_effort": lane_effort(lane)} if lane_effort(lane) else {}
            try:
                with provider_lock[lane["provider"]]:
                    reply, _, _ = llm_chat(lane["backend"], [{"role": "user", "content": prompt}],
                                           max_tokens=lane_max_tokens(lane, args.max_tokens), temperature=0.2,
                                           system=SYSTEM, app_name="sparebrains", timeout=(10, args.call_timeout),
                                           include_metadata=True, timeout_s=relay.LONG_CALL_S, long_call=True,
                                           request_id=uuid.uuid4().hex, **extra)
            except Exception as e:
                print(f"    subgoal ask to {lane['backend']} failed: {type(e).__name__}: {str(e)[:120]}", flush=True)
                reply = None
            with lock:
                state["calls"] += 1
            return reply

        def on_lemma(statement, t):
            verdict = "lemma-accept" if t["verdict"] == "accept" else "lemma-reject"
            row = {**base_row(name, lane, attempt_no, statement_sha, tset), "verdict": verdict,
                   "reason": RUNNER_PATH.sub("", t.get("reason") or "")[:300], "try_mode": try_mode,
                   "failure_kind": failure_kind(t["verdict"], t.get("reason") or ""), "lemma": statement[:600],
                   "call_seconds": 0.0, "lean_seconds": t.get("seconds", 0.0), "response_chars": len(t.get("reply") or ""),
                   "proof_sha": hashlib.sha256(t["proof"].encode()).hexdigest() if t.get("proof") else None}
            record(row, t["prompt"], t.get("reply"), t.get("proof"),
                   subgoals.lemma_file(prefix, statement, t.get("proof") or ""), t.get("output"))
            print(f"    subgoal {verdict} ← {lane['backend']}: {statement[:110]}", flush=True)

        try:
            rep = subgoals.repair(candidate, prefix, lean_out, ask=ask, run_lean=lean_tools.run_lean,
                                  judge_text=lean_tools.judge_text, on_lemma=on_lemma,
                                  fix=lambda proof, out: fixer.fix(proof, out, *lean_tools.index()))
        except Exception as e:                           # the loop is a bonus on a try already recorded as rejected
            print(f"    subgoal loop failed: {type(e).__name__}: {str(e)[:160]}", flush=True)
            return {"stopped": f"loop error: {type(e).__name__}"}
        print(f"    loop: {rep.get('rounds', 0)} round(s) of holes, {rep.get('closed_by_lean', 0)}/{rep.get('holes', 0)} "
              f"closed by Lean, {rep.get('lemmas_proved', 0)} lemma(s) proved in {rep.get('asked', 0)} ask(s)"
              f"{'; ' + rep['stopped'] if rep.get('stopped') else ''}", flush=True)
        return rep

    def look_up_names(ctx, invented):
        """Real mathlib names for invented ones, into the next relay prompt (tools/lean_tools.py names).
        Library-style names only; a lookup failure just leaves the name without suggestions."""
        for n in invented:
            if "." in n and n[0].isupper() and n not in ctx["real_names"]:
                try:
                    ctx["real_names"][n] = [r for r in lean_tools.names(n, k=4) if r != n]
                except Exception as e:
                    print(f"relay: name lookup unavailable ({type(e).__name__}); prompt without suggestions", flush=True)
                    ctx["real_names"][n] = []

    def relay_ask(name, lane, attempt_no, ctx):
        """One relay try, waiting out the router's pacing. After every reply the router parks a lane
        for a few seconds to a couple of minutes; run 37522262314 lost each lane's 2nd and 3rd try
        to that. A park is waited for (up to relay.PARK_WAIT_S) and a mid-ask defer is retried."""
        for _ in range(relay.DEFERS):
            waited = 0
            while benched(lane["backend"]) and waited < relay.PARK_WAIT_S and lane["provider"] not in exhausted:
                time.sleep(5)
                waited += 5
            if lane["provider"] in exhausted or benched(lane["backend"]):
                skip(name, lane, attempt_no, f"lane still parked after {waited}s at the time of the relay ask")
                return "gave_up"
            v = run_one(name, lane, attempt_no, relay_ctx=ctx)
            if v != "defer":
                return v
        skip(name, lane, attempt_no, f"router deferred the relay ask {relay.DEFERS} times")
        return "gave_up"

    fix_index = {}

    def fix_one(name, near, tset=None):
        """Issue #3: a stored failed proof with its form repaired (layout, Lean 3 syntax, invented names;
        tools/fixer.py), then taken apart by tools/subgoals.py with Lean's automation only (no model in this
        pass). Credited to the lane that wrote it; try_mode 'fixer+loop', prev_id its row, the passes that
        changed it in `fixes`, the loop's summary in `tools`. Every near miss gets this pass once: the first
        replay (2026-10-08) solved 2 of 15 open problems' closest misses this way (435, 233)."""
        tset = tset or target_set
        if "names" not in fix_index:                     # mathlib's real names, built once per job
            src = ROOT / ".lake" / "packages" / "mathlib" / "Mathlib"
            fix_index["names"] = fixer.mathlib_index(src) if src.is_dir() else set()
            fix_index["by_last"] = fixer._by_last(fix_index["names"])
            print(f"fixer: {len(fix_index['names'])} mathlib names indexed", flush=True)
        fixed, fixes = fixer.fix(near["proof"], near.get("lean_output") or "", fix_index["names"], fix_index["by_last"])
        target_text = (ROOT / "targets" / tset / f"{name}.lean").read_text()
        prefix = target_text[:PROOF_SEP.search(target_text).end()]
        candidate = prefix + "\n" + fixed
        cpath = tmpdir / f"{name}.fixer.{near['id']}.lean"
        cpath.write_text(candidate)
        verdict, reason, lean_s, lean_out = judge(str(cpath), args.lean_timeout)
        reason = RUNNER_PATH.sub("", reason)
        if verdict == "wellformed":
            verdict, reason = "reject", "proof still contains sorry"
        loop = {}
        own = live_lanes.get(near["backend"]) if args.fixer_ask else None
        if verdict == "reject":
            t_loop = time.monotonic()
            if own:                                      # the lane that wrote it proves its own open steps
                rep = subgoal_repair(name, own, 1, tset, hashlib.sha256(prefix.encode()).hexdigest(), prefix,
                                     candidate, lean_out, try_mode="fixer-subgoal")
            else:
                try:
                    rep = subgoals.repair(candidate, prefix, lean_out, ask=None, run_lean=lean_tools.run_lean,
                                          judge_text=lean_tools.judge_text)
                except Exception as e:
                    rep = {"stopped": f"loop error: {type(e).__name__}"}
            loop = {k: v for k, v in rep.items() if k not in ("accepted", "sketch", "lean_output")}
            loop["seconds"] = round(time.monotonic() - t_loop, 1)
            if rep.get("accepted"):
                candidate, lean_out = rep["accepted"], rep.get("lean_output") or lean_out
                fixed = candidate[len(prefix):].lstrip("\n")
                verdict = "accept"
                reason = (f"kernel accepted after Lean's automation closed {rep.get('closed_by_lean', 0)} failing step(s)"
                          + (f" and the lane proved {rep['lemmas_proved']} open step(s) as lemmas" if rep.get("lemmas_proved") else ""))
        lane = own or {"backend": near["backend"], "provider": None, "model": None, "tier": None, "rank": None}
        row = {**base_row(name, lane, 1, hashlib.sha256(prefix.encode()).hexdigest(), tset), "verdict": verdict,
               "reason": reason[:300], "failure_kind": failure_kind(verdict, reason), "try_mode": "fixer+loop", "fixes": fixes,
               "prev_id": near["id"], "call_seconds": 0.0, "lean_seconds": round(lean_s, 1), "response_chars": 0,
               "proof_sha": hashlib.sha256(fixed.encode()).hexdigest(), "tools": {"subgoals": loop}}
        record(row, None, None, fixed, candidate, lean_out)
        with lock:
            state["calls"] += 1
            if verdict == "accept":
                state["accepts"] += 1
                solved.setdefault(name, lane)
        print(f"[fixer] {name} ← {near['backend']} (#{near['id']}, {'+'.join(fixes) or 'no form fix'}) → {verdict}  {reason[:110]}"
              f"{'  loop: ' + loop['stopped'] if loop.get('stopped') else ''}", flush=True)
        if verdict == "accept":
            vpath = ROOT / "verified" / tset / name / f"{near['backend']}.lean"
            vpath.parent.mkdir(parents=True, exist_ok=True)
            vpath.write_text(candidate)
            print("    ┌ kernel-accepted proof, verbatim:\n" + "\n".join("    │ " + l for l in fixed.rstrip().splitlines()) + "\n    └", flush=True)
        return verdict

    remaining = 0
    if args.ladder:                                      # 24/7: owed cells across every set, in rung order
        hist = owed_history()
        work = build_ladder_queue(sets, order, args.attempts, hist)
        # A lane that keeps running dry on a rung is skipped there and kept everywhere else (DECISIONS.md 2026-10-08)
        now_iso = datetime.now(timezone.utc).isoformat()
        duds = {(l["backend"], r) for l in order for r in RUNGS if relay.ladder_dud(ledger_rows, l["backend"], r, now_iso)}
        for b, r in sorted(duds):
            print(f"  {b} on {r}: {relay.LADDER_DUD_SHARE:.0%}+ of its last {relay.LADDER_DUD_LAST} ladder calls there came "
                  f"back empty; skipped on {r} for {relay.BENCH_DAYS} days (other rungs and the relay still ask it)")
        if duds:
            before = len(work)
            work = type(work)(item for item in work if (item[5]["backend"], item[3]) not in duds)
            print(f"ladder: {before - len(work)} cells set aside on dry rungs")
        total_cells = sum(len(ns) for _, _, ns in sets) * len(order) * args.attempts
        by_rung = defaultdict(int)
        for item in work:
            by_rung[item[3]] += 1
        print(f"ladder: {len(work)} of {total_cells} cells still owed "
              f"({sum(len(ns) for _, _, ns in sets)} targets × {len(order)} lanes × {args.attempts} tries); by rung: "
              + ", ".join(f"{r} {by_rung[r]}" for r in RUNGS if by_rung[r]))
        if args.plan:
            for item in list(work)[:40]:
                print(f"  {item[3]:8s} {item[2]:45s} {item[5]['backend']:40s} try {item[6]}")
            print(f"  … {max(0, len(work) - 40)} more")
            return 0
        parked = []                                      # cells whose provider is parked for this job
        cell_errors = defaultdict(int)                   # (set, target, lane) → lane errors in this job
        deadline = t_start + args.max_minutes * 60 if args.max_minutes else None
        idle = {"since": None}

        inflight = {}                                    # thread → the cell it is asking about right now

        heartbeat_state = {"last_sent": 0.0}

        def heartbeat(status="running", force=False):
            now = time.monotonic()
            with lock:
                if not force and now - heartbeat_state["last_sent"] < 5.0:
                    return
                heartbeat_state["last_sent"] = now
                owed = len(work) + len(parked)
                working = list(inflight.values())
                payload = {"run_id": run_id, "mode": mode, "status": status, "cells_total": total_cells,
                           "cells_owed": owed, "calls": state["calls"], "accepts": state["accepts"],
                           "lanes": len(order), "targets": len(names), "working_on": working,
                           "lane_manifest": lane_manifest, "lane_roster_sha": lane_roster_sha}
            submit_telemetry(sparebrains_heartbeat, payload)

        def pulse():
            """The site's "right now" box: only the cells in flight and the running counts."""
            heartbeat()
        heartbeat(force=True)
        state["heartbeat"] = heartbeat

        def worker():
            spins = 0
            while True:
                with lock:
                    if not work or state["calls"] >= args.max_calls:
                        return
                    if deadline and time.time() > deadline:
                        return
                    item = work.popleft()
                tset, tdir_, name, rung, rank, lane, a = item
                if lane["provider"] in exhausted:
                    parked.append(item)
                    continue
                if lane["backend"] in bench["gone"]:
                    parked.append(item)                  # still owed; the next job asks the router afresh
                    continue
                if benched(lane["backend"]):
                    with lock:
                        work.append(item)                # someone else's turn; this lane stays owed
                    spins += 1
                    if spins >= max(1, len(work)):       # a full cycle with nothing answerable
                        if idle["since"] is None:
                            idle["since"] = time.time()
                        if time.time() - idle["since"] > args.idle_minutes * 60:
                            print("nothing answerable for the idle budget; leaving the rest for the next job", flush=True)
                            return
                        time.sleep(30)
                        spins = 0
                    continue
                spins = 0
                idle["since"] = None
                me = threading.get_ident()
                with lock:
                    inflight[me] = {"target_set": tset, "target": name, "rung": rung, "backend": lane["backend"],
                                    "tier": lane["tier"], "attempt_no": a, "since": round(time.time(), 1)}
                pulse()
                prev = None
                if a > 1:                                # a repair try needs the cell's last answer
                    with lock:
                        prev = memory.get((tset, name, lane["backend"]))
                    if prev is None:
                        got = sparebrains_previous(tset, name, lane["backend"]) or {}
                        prev = got if got.get("found") else None
                try:
                    v = run_one(name, lane, a, tset, tdir_, prev)
                finally:
                    with lock:
                        inflight.pop(me, None)
                if v == "exhausted":
                    parked.append(item)
                elif v == "defer":
                    with lock:
                        work.append(item)
                elif v == "error_router":
                    with lock:                           # the router's failure, not the lane's: the cell stays
                        work.append(item)                # owed and nothing is held against it
                elif v == "error":
                    key = (tset, name, lane["backend"])
                    with lock:                           # a lane error is not an answer: the cell goes to the back
                        cell_errors[key] += 1            # of this job's queue, until the ledger's three-error cap
                        if hist[key]["errors"] + cell_errors[key] < 3:
                            work.append(item)

        threads = [threading.Thread(target=worker, daemon=True) for _ in range(max(1, args.jobs))]
        for th in threads:
            th.start()
        for th in threads:
            th.join()
        remaining = len(work) + len(parked)
        heartbeat("done", force=True)
        print(f"ladder: {remaining} cells left for the next job ({len(parked)} behind a parked provider)")
    elif args.fixer:                                     # issue #3: no model call, the kernel re-judges
        fixed_before = {r.get("prev_id") for r in ledger_rows if r.get("try_mode") == "fixer+loop"}
        cells = ([(t["target_set"], t["target"]) for t in relay.fetch_json("/targets.json")["open"]]
                 if args.only == "all" else [(target_set, n) for n in names])
        for tset, name in cells:
            if state["calls"] >= args.max_calls:
                print(f"cap reached: {args.max_calls} fixer checks")
                break
            d = relay.fetch_dossier(tset, name)
            for near in (d.get("near_misses") or []) + (d.get("form_misses") or []):
                if (tset, name) not in solved and name not in solved and near.get("proof") and near["id"] not in fixed_before:
                    fixed_before.add(near["id"])
                    fix_one(name, near, tset)
    elif args.relay:                                     # stage 2: one problem, the strongest lanes in turn
        tried = owed_history(relay_rows=True)
        for name in names:
            try:
                ctx = {"dossier": relay.fetch_dossier(target_set, name), "this_job": [], "real_names": {}}
                look_up_names(ctx, relay.library_names(ctx["dossier"]))
            except Exception as e:
                print(f"relay: no dossier for {target_set}/{name} ({type(e).__name__}: {e}); skipped", flush=True)
                continue
            if ctx["dossier"].get("solved"):
                print(f"relay: {name} is already solved; nothing to relay", flush=True)
                continue
            if args.relay_next:                          # the fixer first: free, and it may already solve it
                for near in (ctx["dossier"].get("near_misses") or []) + (ctx["dossier"].get("form_misses") or []):
                    if near.get("proof") and near["id"] not in fixed_ids and name not in solved:
                        fixed_ids.add(near["id"])
                        fix_one(name, near, target_set)
            for lane in order:
                if name in solved or state["calls"] >= args.max_calls:
                    break
                h = tried[(target_set, name, lane["backend"])]
                left = relay.tries_left(by_problem.get((target_set, name), []), lane["backend"], lane.get("model"),
                                        people.get((target_set, name), []))
                for attempt_no in range(relay.spent(h) + 1, relay.spent(h) + left + 1):
                    if state["calls"] >= args.max_calls:
                        break
                    v = relay_ask(name, lane, attempt_no, ctx)
                    if v in ("accept", "exhausted", "gave_up"):
                        break
        if state["calls"] >= args.max_calls:
            print(f"cap reached: {args.max_calls} calls")
    elif args.stop_on_accept:                            # ladder-asc/desc by hand: order matters, so sequential
        for name in names:
            for lane in order:
                if state["calls"] >= args.max_calls or name in solved:
                    break
                if lane["provider"] in exhausted:
                    skip(name, lane, 1, f"provider parked for the run: {exhausted[lane['provider']]}")
                    continue
                if benched(lane["backend"]):
                    skip(name, lane, 1, "lane benched by the router at the time of the ask")
                    continue
                for attempt_no in range(1, args.attempts + 1):
                    if state["calls"] >= args.max_calls:
                        break
                    v = run_one(name, lane, attempt_no)
                    if v == "defer":
                        skip(name, lane, attempt_no, "router benched the lane mid-ask")
                        break
                    if v == "exhausted":
                        skip(name, lane, attempt_no, f"provider parked for the run: {exhausted[lane['provider']]}")
                        break
                    if v == "accept":
                        break
            if state["calls"] >= args.max_calls:
                print(f"cap reached: {args.max_calls} calls")
                break
    else:                                                # sweep: a queue of pairs, providers interleaved
        lanes_rr = interleave_by_provider(order)
        work = deque((n, l, a) for n in names for l in lanes_rr for a in range(1, args.attempts + 1))
        if len(work) > args.max_calls:
            print(f"cap: {len(work)} planned attempts trimmed to {args.max_calls}")
            work = deque(list(work)[:args.max_calls])
        deferrals = defaultdict(int)

        def worker():
            while True:
                with lock:
                    if not work or state["calls"] >= args.max_calls:
                        return
                    item = work.popleft()
                    remaining = len(work)
                name, lane, a = item
                key = (name, lane["backend"], a)
                if lane["provider"] in exhausted:
                    skip(name, lane, a, f"provider parked for the run: {exhausted[lane['provider']]}")
                    continue
                if benched(lane["backend"]):
                    if deferrals[key] < 3 and remaining > 0:
                        deferrals[key] += 1               # try again after the rest of the queue
                        with lock:
                            work.append(item)
                        continue
                    skip(name, lane, a, "lane benched by the router for the whole run")
                    continue
                v = run_one(name, lane, a)
                if v == "exhausted":
                    skip(name, lane, a, f"provider parked for the run: {exhausted[lane['provider']]}")
                    continue
                if v == "defer":
                    if deferrals[key] < 3:
                        deferrals[key] += 1
                        with lock:
                            work.append(item)
                    else:
                        skip(name, lane, a, "router benched the lane mid-ask, three times")

        threads = [threading.Thread(target=worker, daemon=True) for _ in range(max(1, args.jobs))]
        for th in threads:
            th.start()
        for th in threads:
            th.join()
        if state["calls"] >= args.max_calls and work:
            print(f"cap reached: {args.max_calls} calls, {len(work)} pairs not attempted")

    calls, accepts = state["calls"], state["accepts"]
    drain_telemetry()
    print(f"done: {calls} calls, {accepts} accepts, {state['errors']} lane errors, {state['skipped']} skipped "
          f"(benched), {state['waits']} rate-limit waits honored, {len(solved)}/{len(names)} targets solved, "
          f"mode {mode}, run {run_id}")
    if args.ladder:
        rung_tally = defaultdict(lambda: {"answered": 0, "accepts": 0, "targets": set(), "solved": set()})
        for tset, _, ns in sets:
            for n in ns:
                r, _ = rung_of(tset, n)
                rung_tally[r]["targets"].add(n)
                if n in solved:
                    rung_tally[r]["solved"].add(n)
                t = per_target[n]
                rung_tally[r]["answered"] += t["done"] - t["errors"]
                rung_tally[r]["accepts"] += t["accepts"]
        print("\nper rung (this job):")
        for r in RUNGS:
            rt = rung_tally.get(r)
            if rt and rt["answered"]:
                print(f"  {r:8s} {rt['accepts']:4d}/{rt['answered']:4d} answered, {len(rt['solved'])}/{len(rt['targets'])} targets proved by someone")
    else:
        print("\nper target:")
        for n in names:
            t = per_target[n]
            first = solved.get(n)
            print(f"  {n:45s} {t['accepts']:3d}/{t['done']:3d} lanes  "
                  f"{'first: ' + first['backend'] + ' (' + first['tier'] + ')' if first else 'unsolved so far'}")
    ranked = sorted(per_lane.items(), key=lambda kv: (-kv[1]["accepts"], -kv[1]["attempts"]))
    print("\nper lane:")
    for b, pl in ranked:
        if pl["attempts"]:
            answered = pl["attempts"] - pl["errors"]
            per_k = round(1000 * pl["accepts"] / answered) if answered else 0
            print(f"  {b:40s} {pl['tier']:9s} {pl['accepts']:3d}/{answered:3d} answered  "
                  f"({per_k} per 1,000, {pl['errors']} errors)")
    if exhausted:
        print("\nproviders parked during this run (fair-share or pool gate, resets at UTC midnight):")
        for prov, why in exhausted.items():
            print(f"  {prov}: {why}")
    print(f"\nsite: {SITE}/runs/{run_id}")
    out = os.environ.get("GITHUB_OUTPUT")
    if out:
        with open(out, "a") as fh:
            fh.write(f"calls={calls}\naccepts={accepts}\nlanes={len(order)}\ntargets={len(names)}\nmode={mode}\nremaining={remaining}\n")
            # Stage 2 chains itself (DECISIONS.md 2026-10-08): another relay job follows while this one had a
            # problem to work and made calls. Zero calls (every lane gated) does not chain, so it cannot spin.
            fh.write(f"relay_more={1 if (args.relay and args.relay_next and names and calls > 0) else 0}\n")
    summary = os.environ.get("GITHUB_STEP_SUMMARY")
    if summary:
        with open(summary, "a") as fh:
            fh.write(f"### attempt run `{run_id}` — {mode}: {calls} calls, {accepts} verified, "
                     f"{state['errors']} lane errors, {state['skipped']} skipped as benched, "
                     f"{state['waits']} rate-limit waits, {len(solved)}/{len(names)} targets solved · "
                     f"[every transcript]({SITE}/runs/{run_id})\n\n")
            if args.ladder:
                fh.write(f"{remaining} cells left for the next job.\n\n| rung | verified | answered | targets proved by someone |\n|---|---|---|---|\n")
                for r in RUNGS:
                    rt = rung_tally.get(r)
                    if rt and rt["answered"]:
                        fh.write(f"| {r} | {rt['accepts']} | {rt['answered']} | {len(rt['solved'])} / {len(rt['targets'])} |\n")
            else:
                fh.write("| target | proved by (lanes) | of | first solver | tier |\n|---|---|---|---|---|\n")
                for n in names:
                    t, l = per_target[n], solved.get(n)
                    fh.write(f"| `{n}` | {t['accepts']} | {t['done']} | {l['backend'] if l else '—'} | {l['tier'] if l else '—'} |\n")
            fh.write("\n| lane | tier | verified | answered | per 1,000 | errors |\n|---|---|---|---|---|---|\n")
            for b, pl in ranked:
                if pl["attempts"]:
                    answered = pl["attempts"] - pl["errors"]
                    fh.write(f"| `{b}` | {pl['tier']} | {pl['accepts']} | {answered} | "
                             f"{round(1000 * pl['accepts'] / answered) if answered else 0} | {pl['errors']} |\n")
            if solved:
                fh.write("\n<details><summary>every kernel-accepted proof in this run</summary>\n\n")
                for vf in sorted((ROOT / "verified").glob("**/*.lean")):
                    if vf.stat().st_mtime >= t_start:
                        fh.write(f"**{vf.parent.name} ← {vf.stem}**\n\n```lean\n{vf.read_text()}```\n\n")
                fh.write("</details>\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
