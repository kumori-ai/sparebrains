"""Stage 2, the relay (DECISIONS.md 2026-10-06): the strongest live lanes try an open problem from
its dossier, everything known about it, instead of from nothing.

The dossier is the public page https://sparebrains.kumori.ai/problems/<set>/<target>.json: the
closest rejected proofs with Lean's output, how every try failed, the library names models invented,
and the comments people left on the problem's GitHub thread. It never holds a known proof of the
problem itself (the site leaves near misses out once a problem is solved, and reference proofs
never reach it), and this module refuses a solved one anyway.

Try modes: `relay` (the dossier) and `relay+thread` (the dossier plus at least one comment), each
recorded beside `cold` and `repair` so the clean numbers stay clean.
"""
import hashlib, json, re, time, urllib.error, urllib.request
from collections import Counter

SITE = "https://sparebrains.kumori.ai"
RELAY_TRIES = 3                    # per (target, lane), like the ladder's three tries per cell
# Reasoning lanes think before they answer. At the ladder's 4,000 the router logged "ran out of tokens
# mid-thought (4000 max)" for 4 of the first relay run's 5 calls (37521229581, 2026-10-06).
MAX_TOKENS = 16_000
REASONING_EFFORT = "medium"        # kumori's opt-in reasoning_effort (OpenRouter reasoning.effort, Groq GPT-OSS)
LONG_CALL_S = 240                  # kumori's opt-in pinned long call (api_v1_llm_bp._pinned_timeouts)
LEMMA_CALL_S = 90                  # one small lemma needs no 240 s: Laguna and OpenRouter's free lane hung to the limit (2026-10-09)
PARK_WAIT_S = 180                  # a parked lane is waited for, not dropped (groq parked 119 s, run 37522262314)
DEFERS = 4                         # a mid-ask defer is retried this many times before the lane is left
PROMPT_CAP = 24_000                # free-model context windows; the full dossier stays at its URL
NEAR_SHOWN, PROOF_CAP, LEAN_CAP, COMMENT_CAP = 3, 2_000, 1_500, 1_500
RUNNER_PATH = re.compile(r"\S*/\.lake/attempts/\S+?\.lean:")    # keep "line:col: error", drop the runner path

RELAY = ("Other models, and possibly people, have already tried to prove the Lean 4 theorem at the end of this "
         "message, and every attempt so far was rejected by the Lean kernel. Below is what they tried and exactly "
         "why it failed. Learn from it, then write a complete proof.\n\n"
         "Rules: Lean v4.33.1 and mathlib v4.33.1, and `import Mathlib` is already in the file. Replace only the "
         "`sorry`; keep the theorem statement byte-for-byte; no `admit` or `native_decide`; no new "
         "axioms; Lean 4 syntax, not Lean 3. Answer with only the proof that replaces `sorry` (the tactic lines "
         "after `:= by`), in one ```lean code block, and nothing else.\n\n"
         "Tools: you cannot run Lean, but this harness runs it for you, step by step. Write the proof's shape "
         "with `have` steps; if you cannot do one step, write `sorry` there. Every step Lean rejects becomes a "
         "hole too. Lean's own automation (omega, linarith, nlinarith, positivity, norm_num, simp, aesop, "
         "exact?) tries each hole, and any hole still open comes back to you alone, as a small lemma with what "
         "Lean said about it. A correct outline with a few hard steps is worth more than a long guess. Real "
         "mathlib names for invented ones are listed below when a name was the problem.\n\n")


def is_relay(row):
    return str(row.get("try_mode") or "").startswith("relay")


# Cloudflare in front of kumori.ai answers the default "Python-urllib/x.y" agent with error 1010
# (403); run 37520440995's first relay fetch died on it, 2026-10-06. Say who is asking instead.
USER_AGENT = "sparebrains-relay (+https://github.com/kumori-ai/sparebrains)"
REPO = "kumori-ai/sparebrains"


EMPTY = re.compile(r"HTTP 502 : unknown")    # how an answer that never came (out of thought) reaches the ledger
TIMED_OUT = re.compile(r"HTTP 504")          # the lane did not answer in time
DRY_LAST, DRY_SHARE = 10, 0.6                # last 10 calls at least 60% empty: ask for less thinking
BENCH_LAST, BENCH_DAYS = 6, 3                # last 6 relay calls all empty or timed out: out of the relay for 3 days
FAIL_LAST, FAIL_MIN, FAIL_HOURS = 12, 8, 24    # 8+ of a lane's last 12 relay calls in 24 h were errors: it sits out
                                              # the job (2026-10-09: openrouter lanes failed 9-11 of 12, often after
                                              # hanging 260 s, as their account's daily share ran out)
NEWS_MIN = 5                                  # others' answered tries on a problem since a lane's last: a new round
NEWS_MODES = ("cold", "repair", "volunteer")  # tries from outside the relay; relay tries are never news (2026-10-17: rounds
                                              # fed on each other, ~1,000 calls a day for 3 accepts in 2,682 answers)
PROBLEM_CEILING = 1000                        # relay tries on one problem since a person last spoke on it (Andy:
                                              # assume nobody shows up; the swarm keeps trying)
PROBLEM_FIRST, PROBLEM_CAP = 10, 30           # answered relay tries (lane errors left out) before a problem rests: 10, or 30
                                              # once a try made progress; until a person speaks or a model that never
                                              # relayed it is live (DECISIONS 2026-10-23)
LADDER_DUD_LAST, LADDER_DUD_SHARE = 20, 0.6   # a lane's last 20 ladder calls on a rung, 60%+ empty: off that rung


def _calls(rows, backend, relay_only=False):
    rs = [r for r in rows if r.get("backend") == backend and r.get("verdict") in ("accept", "reject", "error")
          and (is_relay(r) or not relay_only)]
    return sorted(rs, key=lambda r: r.get("ts") or "")


def is_empty(r):
    return r.get("verdict") == "error" and bool(EMPTY.search(r.get("reason") or ""))


def running_dry(rows, backend):
    """A thinking model that mostly comes back with nothing: asked for low effort (DECISIONS.md 2026-10-07)."""
    last = _calls(rows, backend)[-DRY_LAST:]
    return len(last) == DRY_LAST and sum(map(is_empty, last)) >= DRY_SHARE * DRY_LAST


def is_timed_out(r):
    return r.get("verdict") == "error" and bool(TIMED_OUT.search(r.get("reason") or ""))


def relay_benched(rows, backend, now_iso):
    """Every one of the lane's last BENCH_LAST relay calls came back empty or timed out, the latest within
    BENCH_DAYS: skip it in the relay until then. A bench that expires lets the lane back in to be measured
    again. Timeouts count since 2026-10-17: openrouter-dots-3-note timed out on 33 of 33 relay calls from
    10-11, a few a day, too spread out for relay_failing's 24 hours to catch."""
    from datetime import datetime, timedelta
    last = _calls(rows, backend, relay_only=True)[-BENCH_LAST:]
    if len(last) < BENCH_LAST or not all(is_empty(r) or is_timed_out(r) for r in last):
        return False
    latest = datetime.fromisoformat(last[-1]["ts"].replace("Z", "+00:00"))
    return datetime.fromisoformat(now_iso.replace("Z", "+00:00")) - latest < timedelta(days=BENCH_DAYS)


def relay_failing(rows, backend, now_iso):
    """At least FAIL_MIN of the lane's last FAIL_LAST relay calls, all within FAIL_HOURS, were errors of any
    kind: the lane sits out this relay job. Only the last FAIL_HOURS count, so a lane whose provider's daily
    share comes back is asked again without anyone deciding it (relay_benched needs every call empty)."""
    from datetime import datetime, timedelta
    now = datetime.fromisoformat(now_iso.replace("Z", "+00:00"))
    recent = [r for r in _calls(rows, backend, relay_only=True)
              if r.get("ts") and now - datetime.fromisoformat(r["ts"].replace("Z", "+00:00")) < timedelta(hours=FAIL_HOURS)]
    last = recent[-FAIL_LAST:]
    return sum(r.get("verdict") == "error" for r in last) >= FAIL_MIN


def ladder_dud(rows, backend, rung, now_iso):
    """The lane's last LADDER_DUD_LAST ladder calls on this rung came back mostly empty (out of thought
    before it answered), the latest within BENCH_DAYS: the ladder skips the lane on that rung until then,
    and keeps asking it everywhere else. Per rung, because a thinking model can be strong on easy
    problems and run dry on hard ones: 2026-10-08 openrouter-apodex-1-1-mini, the one lane still owing
    ladder cells, solved 34 primer targets in a night while 119 of its calls in a day on amc12 and
    MATH L4/L5 ran out of 16,000 tokens mid-thought, and stage 2 waited on that chain."""
    from datetime import datetime, timedelta
    last = [r for r in _calls(rows, backend) if not is_relay(r) and r.get("rung") == rung][-LADDER_DUD_LAST:]
    if len(last) < LADDER_DUD_LAST or sum(map(is_empty, last)) < LADDER_DUD_SHARE * LADDER_DUD_LAST:
        return False
    latest = datetime.fromisoformat(last[-1]["ts"].replace("Z", "+00:00"))
    return datetime.fromisoformat(now_iso.replace("Z", "+00:00")) - latest < timedelta(days=BENCH_DAYS)


FETCH_WAITS = (5, 10, 20, 40)      # seconds before each further try: 75 s in all, then the error stands


def fetch_json(path, timeout=30):
    """One page of the public site, as JSON. The site answers 5xx for a short while each time a new version of it
    takes over (2026-10-11: three jobs of run 38154955711 died on one 503, 32 s after a deploy), so a server
    error or a dropped connection is tried again before it may end a job. A 4xx is ours to fix: raised at once."""
    req = urllib.request.Request(SITE + path, headers={"User-Agent": USER_AGENT, "Accept": "application/json"})
    for wait in (*FETCH_WAITS, None):
        try:
            with urllib.request.urlopen(req, timeout=timeout) as r:
                return json.loads(r.read().decode())
        except urllib.error.HTTPError as e:
            if e.code < 500 or wait is None: raise
            why = f"HTTP {e.code}"
        except (urllib.error.URLError, TimeoutError) as e:
            if wait is None: raise
            why = type(e).__name__
        print(f"  {SITE}{path} answered {why}; trying again in {wait}s", flush=True)
        time.sleep(wait)


def fetch_dossier(target_set, target, timeout=30):
    return fetch_json(f"/problems/{target_set}/{target}.json", timeout)


def lane_strength(rows, rungs):
    """backend → distinct targets it proved above MATH level 2: the stage-2 lane ranking."""
    hard = set(rungs[rungs.index("math-L2") + 1:])
    seen = {(r.get("backend"), r.get("target_set"), r.get("target"))
            for r in rows if r.get("verdict") == "accept" and r.get("rung") in hard}
    return Counter(b for b, _, _ in seen)


def strongest(live_lanes, strength, k):
    """The k live lanes with the most hard solves; a lane with none never relays."""
    ranked = sorted((l for l in live_lanes if strength.get(l["backend"])),
                    key=lambda l: (-strength[l["backend"]], l["backend"]))
    return ranked[:k]


def library_names(dossier):
    """Invented names that look like library names (`Nat.foo`, `Finset.bar`). `h`, `k` and `x.val` are
    the model's own out-of-scope locals, not missing lemmas."""
    return [n for n, _ in dossier.get("unknown_names") or [] if "." in n and n[0].isupper()]


def spent(h):
    """Relay tries a lane has used on a problem: every call, an empty one included. Counting answers
    only kept two lanes that always came back empty "owed" on the first problem, and the relay asked
    it all night, 2026-10-07 01:10-11:31 (6 runs, 29 calls, 3 answers)."""
    return h["answered"] + h["errors"] + h.get("router_errors", 0)


# ── Rounds: the swarm (DECISIONS.md 2026-10-08) ───────────────────────────────────────────────────
# Every try on a problem, by any lane, a volunteer's agent or a person's hint, is a new angle in its
# dossier. A lane's three relay tries on a problem are a round; it earns another round when there is
# news from outside the relay since its last try: NEWS_MIN answered cold, repair or volunteer tries by
# others, a person's comment, or a different model behind the lane (2026-10-17: relay tries stopped
# counting, because rounds fed on each other's tries and never ran out). The relay works breadth-first (a fresh comment first, then the problem with the
# fewest relay tries), so every open problem gets a round before any gets another, and a problem
# rests once it has had PROBLEM_CEILING relay tries since a person last said anything about it, or PROBLEM_FIRST
# answered ones since then (PROBLEM_CAP if one made progress) and every live lane's model has relayed it already.

def _ts(r):
    return r.get("ts") or ""


def problem_rows(rows):
    """(set, target) → every judged try on it, any mode but the fixer's re-judging, oldest first."""
    from collections import defaultdict
    by = defaultdict(list)
    for r in rows:
        if not str(r.get("try_mode") or "").startswith("fixer") and r.get("verdict") in ("accept", "reject", "error"):
            by[(r.get("target_set"), r.get("target"))].append(r)
    for v in by.values():
        v.sort(key=_ts)
    return by


def _news(prow, backend, after, before, people):
    """Did enough happen on this problem between two times (before=None: until now)?"""
    if any(after < c and (before is None or c < before) for c in people):
        return True
    others = sum(1 for r in prow if r.get("backend") != backend and r.get("verdict") in ("accept", "reject")
                 and r.get("try_mode") in NEWS_MODES and after < _ts(r) and (before is None or _ts(r) < before))
    return others >= NEWS_MIN


def tries_left(prow, backend, model, people=()):
    """Relay tries this lane has left on one problem in its current round."""
    mine = [r for r in prow if r.get("backend") == backend and is_relay(r)]
    if not mine:
        return RELAY_TRIES
    in_round, prev = 0, None
    for r in mine:
        if prev is not None and (r.get("model") != prev.get("model") or _news(prow, backend, _ts(prev), _ts(r), people)):
            in_round = 0
        in_round += 1
        prev = r
    if (model and prev.get("model") and model != prev.get("model")) or _news(prow, backend, _ts(prev), None, people):
        return RELAY_TRIES
    return max(0, RELAY_TRIES - in_round)


def made_progress(r):
    """The subgoal loop closed a step with Lean's automation or proved a lemma on this try (tools.subgoals)."""
    sg = (r.get("tools") or {}).get("subgoals") or {}
    return bool(sg.get("closed_by_lean") or sg.get("lemmas_proved"))


def resting(prow, people=(), lanes=()):
    """The problem waits for new input: PROBLEM_CEILING relay tries since a person last commented, or PROBLEM_FIRST
    answered ones with no progress (PROBLEM_CAP with some; a lane error is the router's or provider's failure, not
    the problem's), unless a live lane's model has never relayed it. Successive-halving practice: a small budget
    for every problem, more only for those showing signs of being solvable."""
    since = max(people, default="")
    mine = [r for r in prow if is_relay(r) and _ts(r) > since]
    if len(mine) >= PROBLEM_CEILING:
        return True
    answered = [r for r in mine if r.get("verdict") in ("accept", "reject") and r.get("failure_kind") != "lane_error"]
    if len(answered) < (PROBLEM_CAP if any(made_progress(r) for r in mine) else PROBLEM_FIRST):
        return False
    seen = {r.get("model") for r in prow if is_relay(r)}
    return not any(l.get("model") and l["model"] not in seen for l in lanes)


def rests_now(by_problem, job_rows, key, people=(), lanes=()):
    """resting() on the history the job started with plus the rows this job wrote since, so a job stops a
    problem the moment it crosses its budget, an explicit --only target included."""
    mine = [r for r in job_rows if (r.get("target_set"), r.get("target")) == key]
    return resting(problem_rows(by_problem.get(key, []) + mine).get(key, []), people, lanes)


def next_problem(open_list, lanes, by_problem, people_by_problem=None):
    """(set, target) the relay works next, or None: a problem a person spoke on since its last relay try
    first, then the fewest relay tries so far (breadth-first), then the stage-2 order. Only problems
    where some live lane has tries left in its current round, and that are not resting."""
    best = None
    for t in open_list:
        key = (t["target_set"], t["target"])
        prow, people = by_problem.get(key, []), (people_by_problem or {}).get(key, [])
        if resting(prow, people, lanes) or not any(tries_left(prow, l["backend"], l.get("model"), people) > 0 for l in lanes):
            continue
        relay_rows = [r for r in prow if is_relay(r)]
        fresh = bool(people) and (not relay_rows or max(people) > _ts(relay_rows[-1]))
        rank = (0 if fresh else 1, len(relay_rows), t["order"])
        if best is None or rank < best[0]:
            best = (rank, key)
    return best[1] if best else None


# The relay's backoff (DECISIONS.md 2026-10-24). Dry streaks before the 9 relay solves to 2026-10-24, in relay jobs:
# 4, 23, 4, 1, 1, 20, 19, 109, 154. 160 is above all of them, so it would have delayed none; past it, a job relays only
# on a wake, and never chains the next.
RELAY_DRY_JOBS = 160
DAILY_S = 24 * 3600


def _when(ts):
    from datetime import datetime
    return datetime.fromisoformat(ts.replace("Z", "+00:00")).timestamp()


def dry_streak(rows, records):
    """(relay jobs since the last one with an accept, the latest relay activity) from the relay ledger rows grouped by
    run_id plus the job records (ledger/relay-jobs/), which also count a job that wrote no relay row. A rerun's
    attempts are one job."""
    jobs = {}
    for r in rows:
        if is_relay(r) and r.get("run_id"):
            j = jobs.setdefault(r["run_id"], {"ts": _ts(r), "accepts": 0})
            j["ts"] = min(j["ts"], _ts(r))
            j["accepts"] += r.get("verdict") == "accept"
    for rec in records:
        j = jobs.setdefault(rec["run_id"], {"ts": rec["ts"], "accepts": 0})
        j["ts"] = min(j["ts"], rec["ts"])
        j["accepts"] += rec.get("accepts") or 0
    streak = 0
    for j in sorted(jobs.values(), key=lambda j: j["ts"], reverse=True):
        if j["accepts"]:
            break
        streak += 1
    clock = max([_ts(r) for r in rows if is_relay(r)] + [rec["ts"] for rec in records], default="")
    return streak, clock


def choose_problem(open_list, lanes, by_problem, people_by_problem, rows, records, now_iso):
    """(problem, woken_by, backed_off). Under RELAY_DRY_JOBS dry jobs: next_problem, as before. At or past it, only a
    wake not spent by an earlier job's record: a person comment newer than the problem's last relay try, a lane in
    this job whose model never relayed anything, or the daily probe once the last relay activity is a day old."""
    streak, clock = dry_streak(rows, records)
    if streak < RELAY_DRY_JOBS:
        return next_problem(open_list, lanes, by_problem, people_by_problem), None, False
    spent = [rec.get("woken_by") or {} for rec in records]
    people_by_problem = people_by_problem or {}
    for t in sorted(open_list, key=lambda t: t["order"]):
        key = (t["target_set"], t["target"])
        prow, people = by_problem.get(key, []), people_by_problem.get(key, [])
        if not people or resting(prow, people, lanes):
            continue
        relay_rows = [r for r in prow if is_relay(r)]
        latest = max(people)
        woken = {"kind": "comment", "problem": f"{key[0]}/{key[1]}", "comment_ts": latest}
        if (not relay_rows or latest > _ts(relay_rows[-1])) and woken not in spent \
                and any(tries_left(prow, l["backend"], l.get("model"), people) > 0 for l in lanes):
            return key, woken, True
    relayed = {r.get("model") for r in rows if is_relay(r)}
    for l in lanes:
        woken = {"kind": "model", "model": l.get("model")}
        if l.get("model") and l["model"] not in relayed and woken not in spent:
            pick = next_problem(open_list, lanes, by_problem, people_by_problem)
            return (pick, woken, True) if pick else (None, None, True)
    if not clock or _when(now_iso) - _when(clock) > DAILY_S:
        pick = next_problem(open_list, lanes, by_problem, people_by_problem)
        return (pick, {"kind": "daily"}, True) if pick else (None, None, True)
    return None, None, True


def chains(backed_off, picked, calls):
    """Another relay job follows (attempt.yml): only after a job that had a problem and made calls, never a backed-off
    one, so a wake buys exactly one job."""
    return bool(picked and calls > 0 and not backed_off)


def write_job_record(jobs_dir, run_id, run_attempt, ts, problem, calls, accepts, relay_rows, woken_by, backed_off):
    """ledger/relay-jobs/<run_id>-<run_attempt>.json, one per job that picked a problem, whatever it then did: the
    backoff's clock and its spent wakes. .json, never .jsonl, so ledger_files.try_files never reads it as tries; the
    attempt in the name keeps a rerun from colliding in publish.py."""
    jobs_dir.mkdir(parents=True, exist_ok=True)
    path = jobs_dir / f"{run_id}-{run_attempt}.json"
    path.write_text(json.dumps({"run_id": str(run_id), "run_attempt": str(run_attempt), "ts": ts,
                                "problem": "/".join(problem) if problem else None, "calls": calls, "accepts": accepts,
                                "relay_rows": relay_rows, "woken_by": woken_by, "backed_off": backed_off}) + "\n")
    return path


def load_job_records(jobs_dir):
    out = []
    for f in sorted(jobs_dir.glob("*.json")) if jobs_dir.exists() else []:
        try:
            out.append(json.loads(f.read_text()))
        except ValueError:
            pass
    return out


def load_people(path):
    """people_comments() written to a file by an earlier workflow step, so the step that runs untrusted
    Lean never holds the GitHub token. Missing or unreadable reads as no comments."""
    try:
        raw = json.loads(open(path).read())
        return {tuple(k.rsplit("/", 1)): v for k, v in raw.items()}
    except Exception:
        return {}


def people_comments(token=None):
    """(set, target) → created_at of every comment a person (not a bot) left on its problem thread.
    One GitHub call for the threads, one per thread with comments. A failure reads as no comments."""
    import urllib.request
    headers = {"User-Agent": USER_AGENT, "Accept": "application/vnd.github+json"}
    if token:
        headers["Authorization"] = f"Bearer {token}"
    def get(url):
        with urllib.request.urlopen(urllib.request.Request(url, headers=headers), timeout=30) as r:
            return json.loads(r.read().decode())
    out = {}
    try:
        for issue in get(f"https://api.github.com/repos/{REPO}/issues?labels=problem&state=all&per_page=100"):
            m = re.match(r"<!-- sparebrains:problem ([\w./-]+)/([\w.-]+) -->", issue.get("body") or "")
            if not m or not issue.get("comments"):
                continue
            stamps = [c["created_at"].replace("Z", "+00:00") for c in get(issue["comments_url"] + "?per_page=100")
                      if (c.get("user") or {}).get("type") != "Bot"]
            if stamps:
                out[(m.group(1), m.group(2))] = sorted(stamps)
    except Exception as e:
        print(f"relay: person comments unavailable ({type(e).__name__}); rounds open on others' tries alone")
    return out


def _clip(text, cap):
    text = (text or "").rstrip()
    return text if len(text) <= cap else text[:cap] + "\n…"


def relay_prompt(target_text, dossier, this_job=(), real_names=None):
    """(prompt, meta). `this_job` holds this run's own rejected relay tries on the target, newest
    last, so the next lane sees them before the site has caught up."""
    if dossier.get("solved"):
        raise ValueError(f"{dossier.get('target')} is solved: a relay prompt would carry a known proof")
    parts = [RELAY]
    fails = ", ".join(f"{f['kind']} {f['n']} (by {f['lanes']} lanes)" for f in dossier.get("failures", []))
    parts.append(f"## Earlier tries\n{dossier.get('answered', 0)} answered tries by {dossier.get('lanes_tried', 0)} "
                 f"models, all rejected. How they failed: {fails or 'unknown'}.\n\n")
    names = list(dict.fromkeys(library_names(dossier) + list(real_names or {})))
    if names:
        # With the closest real names (tools/lean_tools.py names, DECISIONS.md 2026-10-08): an invented
        # lemma name was the commonest failure, and a model cannot look one up; an agent can.
        lines = [f"- `{n}` does not exist" + (f"; real names close to it: {', '.join(f'`{r}`' for r in real_names[n])}"
                                                if real_names and real_names.get(n) else "") for n in names]
        parts.append("## Names that do not exist in this mathlib (models used them anyway)\n" + "\n".join(lines) + "\n\n")
    near = [{"backend": b, "failure_kind": k, "proof": p, "lean_output": o, "id": None} for b, k, p, o in this_job][::-1]
    near += dossier.get("near_misses") or []
    if near:
        parts.append("## The closest attempts, best first, each with what Lean said\n")
        for i, m in enumerate(near[:NEAR_SHOWN], 1):
            parts.append(f"### Attempt {i} ({m['failure_kind']})\n```lean\n{_clip(m['proof'], PROOF_CAP)}\n```\n"
                         f"Lean said:\n```\n{_clip(RUNNER_PATH.sub('', m['lean_output'] or ''), LEAN_CAP)}\n```\n\n")
    thread = [c for c in dossier.get("thread") or [] if c.get("author_type") != "Bot"]   # people, not our digests
    if thread:
        parts.append("## What people said on the problem's public thread (ideas, not checked)\n")
        for c in thread:
            parts.append(f"- {c.get('author') or 'someone'}: {_clip(c.get('body'), COMMENT_CAP)}\n")
        parts.append("\n")
    tail = "## The file to complete\n\n" + target_text
    body = "".join(parts)
    if len(body) + len(tail) > PROMPT_CAP:
        body = body[:PROMPT_CAP - len(tail) - 2] + "\n…\n\n"
    shown = [m["id"] for m in near[:NEAR_SHOWN] if m.get("id")]
    meta = {"try_mode": "relay+thread" if thread else "relay",
            "prev_id": shown[0] if shown else None,
            "comment_ids": [c.get("comment_id") for c in thread],
            "dossier_sha": hashlib.sha256(body.encode()).hexdigest()[:16]}
    return body + tail, meta
