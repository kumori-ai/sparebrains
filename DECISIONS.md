# DECISIONS — the settled ledger

Dated, with receipts. Re-open one only with new evidence; otherwise it stands.
Everything NOT here is open and lives in `PLAN.md` §6.

## 2026-10-28

- **The daily school report (`tools/daily_report.py`, `ledger/daily/<day>.{json,md}`).** Andy's ask: one morning
  read of how close the project is getting, across every student, tool and grade, in place of the counts-only daily
  log and kumori's mail reading a lagging table. The report is read from the ledger alone: the last 24 hours by grade
  (kindergarten primer, middle school MIL, high school miniF2F, college formal-conjectures and openproblems.bio), who
  answered, who passed first and by which mode, the top performers (accepts over answered, ranked only from 3
  answered), the size series as tool lift (this week beside last, refusals shown), the Kaggle batches finished and
  failed, the relay's backoff and the days each rung has sat idle. The openproblems rung shows the leave-one-site-out
  qualify verdict, never a screen score: the best evolve rmse on record (0.8916 vs 0.9684, round 2, 2026-10-21)
  came from one split and that candidate missed qualify on Pearson (-0.010 over 6 sites, 2026-10-22). The retro
  workflow writes the files daily; the issues workflow posts the same text as the daily log comment; kumori's
  07:00 mail is to render the JSON (kumori's side, handed to a kumori session). What the first run showed
  (2026-10-28 15:09 UTC): 0 first-time solves, goal-closer idle 7.5 days, formal-conjectures 6.5, openproblems.bio
  5.7, relay backed off, and the 3B lane at 11 of 26 first accepts against 3 of 11 the week before. 439 tests OK.
- **Two idle rungs get a schedule (Andy: "go build it", 2026-10-28).** The goal closer, by hand only since 10-19,
  made 11 of W43's 28 first-time solves at 11 for 11 tries and then sat 7.5 days; the biology evolve sat 5.7. Now:
  `tactics.yml` runs Sunday 03:10 UTC on `--new-only`, the open problems' one-step goals no literal recipe has a
  row for (a templated recipe leaves no row where it cannot be built, so it never decides; 105 goals on 10-28,
  of 300 open one-step goals in the ledger, 208 queued), about 30 goals a job and 4 jobs at most, no job when
  nothing is new, so no Lean run repeats (the 10-19 Actions rule). `openproblems.yml` runs daily 09:00 UTC, 12
  Leanstral asks seeded from every evolve row, same bar, same sandbox; final test shots stay by hand (2 of 3 left).
  The hand dispatches keep their inputs. 443 tests OK.
- **A cold try is a long_call of 120 s, and the ladder runs 3 workers (was 60 s and 2).** Measured today: the
  ladder's largest outcome was kumori's HTTP 504 (10-27: 419 of 958 ladder tries; 10-28: 278 of 690; 2,937 since
  10-20, median at 45.5 s against 9.1 s for an answered call). kumori (#572) read its logs: every one is an upstream
  timeout at the timeout_s the call asked, 30 or 60 s, never a finished answer, so a client-side recovery would
  save nothing; the slow lanes answer in 15-24 s median and lose half their calls at the line (sealion 27B 223 of
  290, iteracompute qwen3 27B 202 of 227, agnes 3.0 flash 199 of 394, 3 days). The lever on our side is the time:
  the relay already asks 240 s through kumori's long_call (sparebrains keys only); a cold try now asks 120 s the
  same way (`attempt.LADDER_CALL_S`), and the job's workers go from 2 to 3 so a slow lane holding one for two
  minutes costs less of the clock (run 40609387312: 334 calls in its first 90 min, 100 in the next 230, most lanes
  parked by then). The daily report now carries "lost before the kernel" by kind, so tomorrow's 504 count is the
  receipt: the bar is the 504 share of ladder tries under 20% on 10-29 (was 40-44%). kumori's own next step on
  #572, a 503 with Retry-After at once for a lane whose recent timeout rate is high, is theirs to ship.
- **A free lane writes a repair pass, rules written before it runs (2026-10-28; Andy's school: the stronger free
  lanes teach the weaker, Kumori's tools carry the lesson; no frontier model in the loop).** The question: can a
  free lane write a python repair pass that turns stored rejects our chain still rejects after its own run? The
  frozen groq-allam replay (ledger/replay/, 2026-10-24) sets the cohort. On the tune half the chain itself turns
  6 of 44 unknown_name rejects, 2 of 47 lean3_syntax, 20 of 54 unsolved_goals (Codex f1: the first draft here said
  "0", which was the on-arm vs off-arm difference, not the chain's lift); the experiment is the residual, the rows
  the chain's `on` arm still rejects: unknown_name 38 tune on 33 problems, 26 report on 22; "tools today: 0" is
  true of that residual only and is said so. `tools/lane_repair.py`: the writer is one Kumori router lane named
  per run (strongest free tier first), asked with the class, the contract `repair(proof, lean_output) -> proof`,
  our pass for that class as the thing to beat, and up to 8 example (proof, Lean output) pairs drawn from the TUNE
  half only; a candidate that crashes or changes nothing on the examples goes back to the writer with the
  traceback, at most 2 repairs a round, at most 12 writer asks a run (the evolve loop's shape). Untrusted python
  runs only in the candidate container (`tools/sandbox`, gVisor, no network, read-only root, a second entry
  `repair_entry.py`: JSON lines in, JSON lines out); the host validates the output (every id once, nothing unsent,
  every proof a string under 20,000 chars, 4 MB total) and judges each repaired proof by the kernel in CI's judge
  sandbox, each independently, under the target's own prefix. Score: residual tune rejects turned. A candidate is
  kept at 3 or more (a screening rule, not evidence); every kept candidate runs ONCE on the report half and every
  kept candidate's report result is published, no winner picked on report. What we may say: the report half's
  count of distinct problems turned with its Wilson interval over problems (repeated attempts of one problem are
  one observation, Codex f2), attempt counts beside it as description. The writer never sees a report-half row.
  A run has an overall deadline (`--max-minutes`, 300); work past it is recorded pending, never as a miss, and a
  cut-off tune run keeps nothing (Codex f4). Credit: the row names the writer lane and the pass's sha. Cost $0
  (free lanes); runner time about one kernel judge per changed proof. First class: unknown_name. Expected before it
  runs: a miss is likelier than not; a miss still measures the writer lanes' ceiling on this work, which the school
  needs to know. Codex DISAGREE 20261028T153820660037Z (f1 blocking, fixed here; f2-f4 built in); round 2 DISAGREE (f3 the
  output cap was post-exit, now bounded while it streams; f5 rows now reach the ledger as each finishes and a
  report-half crash is an error on its own row; f6 no "best report" summary, every kept pass printed with its own
  held-out result), all three built, two-round cap reached. Smoke 40719242897 (4 asks, Leanstral): the harness ran
  end to end (sandbox proven, 38 residual tune rejects, rows published) and every ask was refused in 0.5 s, the
  lane benched by its upstream free tier; so a writer is now a list of lanes, a refused ask hands to the next lane
  without spending a round, and a round every writer refuses ends the run as one row. **Result, run 40720731565
  (6 asks, Leanstral refused, Codestral wrote all 6): every pass passed the screen and turned 0 of 38 residual tune
  rejects; 0 kept, a miss, as expected before it ran.** What the residual is: 46 of the 64 residual rows (tune and
  report) carry Lean 3 syntax and 37 use Lean 3's trailing-comma tactic lines; `unknown_name` is only the FIRST error
  Lean reports on a proof wrong in several places, so there is no one step for a text pass to fix. The measurement
  stands as the weakest lane's ceiling for this class; the next cohort is one where a single named error is the
  whole distance (a medium-tier lane's residual with exactly one positioned error after the chain), kumori #573.
- **The reach run's verdict (rules written 2026-10-19, judged 2026-10-28).** Runs 39301536190 and 39328013197
  together: 59 open problems (32 and 27; one of the planned 60 is missing from job 2), tools arm solved 2
  (amc12_2001_p21, amc12a_2009_p6), alone arm 3 (algebra_sum1onsqrt2to1onsqrt10000lt198, induction_sumkexp3eqsumksq,
  aime_1988_p8), tools-only 2 against alone-only 3, two-sided sign test p = 1.0: no claim, as the rule predicted.
  Re-derived here from the rows; kumori-ff's script reproduces run 39271052543 exactly (12 vs 5 of 30, p 0.039).
  The replication (seed headtohead-replication-2026-10-19) has not run: run 1's "better" stands unreplicated until it does.

## 2026-10-24

- **The TPU kernel fetches its weights itself, before vLLM, so a stalled download and a hung initialization are told
  apart (`tools/hf_prefetch.py`, inlined into the kernel by `prover.build`).** Both 32B batches died at ~80 min in one
  "loading" phase that hid vLLM's download: in tpu32-20261023T1659's beats free disk fell 40 GB in 4 min, stayed flat
  35 min, fell 26 GB, stayed flat to the end; by 2,701 s it had fallen 65.5 GB, the model's size, so the second
  plateau may be initialization, and host memory says nothing about TPU HBM. Now: the pinned revision over HTTP
  (Xet off: range resume) in its own process, killed and restarted when no byte lands for 300 s (at most 3 times),
  every file checked against the hub's manifest for that revision, and vLLM loads that local copy offline, answers
  keeping the canonical model id. Phases: downloading, downloaded (seconds, sizes, restarts, package versions, the
  manifest in bounded beats), loading (vLLM only), loaded. A failed download or generation child now fails the
  kernel, so Kaggle reports ERROR and `prover.py failed` records it once. A hand-dispatched smoke (`push` + `tpu32` +
  `smoke=N`) pushes only on the TPU leg, names its batch smoke-tpu32-..., so a failed smoke never triggers the 8B
  replacement, and is a startup check, not a full-batch one. If loading still dies after a verified download, the
  next suspect is initialization (tp=8, max_model_len x max_num_seqs). Codex: DISAGREE 20261024T194304201890Z
  (diagnosis beyond the evidence, no safe cancel or resume, no failure propagation, no smoke path) and
  20261024T194446491583Z (the pinned snapshot not handed to vLLM, manifest beats too big, the simulator's cleanup):
  all taken; decided and recorded after the second round under the 2026-10-24 rule. On the build, DISAGREE
  20261024T195435827483Z (a smoke still let the GPU leg push on a missing or finished kernel; load_s counted the
  venv and download; a partial file renamed mid-scan could crash the watchdog and leave its child): fixed, the
  loaded beat now gives vLLM's own load_s beside startup_s and download_s. Not used: hf_transfer (deprecated
  by Hugging Face), a Kaggle Dataset copy (65.5 GB rehosted; kept as the fallback).

- **Sparebrains' operating rule: build tools that let any model, of any size, compete.** Andy made it Kumori's
  sixth non-negotiable today: "it's NOT my call". Every build is judged by its measured tool lift, the same model
  with the tool and without it (lanes page, task #462, 2026-10-17; per tool, the scoreboard, #463, 2026-10-17).
  Solved work is never done: it is re-run on a cadence with smaller models and this week's tools, and the
  calls to a first accept are charted over time (the speed receipt, #191, 2026-10-18). A tool that lets a lesser
  model match a stronger one is the win. Design calls, thresholds, accepted residuals and what to build next are
  the lab's: Claude and Codex decide them from evidence and record them here with both verdict IDs. Only money,
  security and access, deploys, anything public, and people go to Andy.

- **A weekly failure triage ranks which answered failures, across every lane, are worth a tool
  (`tools/triage.py`, `ledger/retro/<year>-W<week>-triage.md`).** Andy, through kumori-89: make the allam process
  automatic. A class is a lane's failure_kind on answered rejects (non-answers, lane errors and fixer re-judges out;
  no label = unclassified, kept). A candidate is >=40% of some lane's rejects with that lane's n>=100, or in the top 5
  by cross-lane total; ranked by that total (demand), the last closed week beside it, because one tool fixes every
  model with the same habit. Frozen replies refine a class by reply signature (lean3_body > fenced_lean4 >
  unfenced_lean4 > prose, truncation a flag) in their own column with coverage, joined by attempt, database-only rows
  apart; they never move a rank. Recoverability stays "unknown" until a replay measures it; nothing is built
  automatically. Each page records the ledger rev, cutoff and classifier hash. First run, the week to 2026-10-26:
  38,021 answered rejects over 96 lanes (804 unclassified); candidates tactic_failed 9,364, unknown_name 8,310,
  unsolved_goals 4,573, no_fence 4,370, lean3_syntax 3,987, other
  3,050; allam's frozen replies match all 780 of its ledger no_fence rejects (lean3_body 476, prose 252, 260
  truncated) with 45 database-only rows apart. Codex: DISAGREE 20261024T192423729277Z (a fictitious lane from ledger/fc's `lane` field, ranks that depend on
  which replies are frozen, overlapping signatures, unlabeled rates, no input boundary), AGREE 20261024T192633227087Z
  with the unclassified bucket and attempt-level joins built in; on the build DISAGREE 20261024T193402083246Z (the
  join was by run, not attempt, and ignored the cutoff; the Lean 3 fallback read past its declaration; the page hid
  database-only and truncated counts), fixed.

- **The worst free lane, lifted by tools: groq-allam's frozen answers replayed with zero model calls
  (`tools/replay.py`, `ledger/replay/`).** groq-allam (allam-2-7b) is the weakest live lane: 8 of 1,129 answered
  ladder tries in the ledger. Read 2026-10-24: 829 of its replies were rejected as "no proof extracted", and 510 of
  those are Lean 3 (`:= begin ... end`, 279 cut off mid-loop by the output cap), which `extract_proof` cannot read
  because it looks for `:= by`, so the fixer's Lean 3 pass never saw them. The tool: `proof_text.recover_lean3`, at
  the raw-reply boundary, every transformation recorded (lean3_begin, repetition_cut, cut_at_max_lines,
  truncated_closed, unclosed_braces), bounded at 200 lines; then the loop's Lean-only chain. Dry run, no Lean: the
  replies Lean can be shown go from 365 to 867 of 1,190. The denominator for every claim is tools alone,
  `subgoals.whole_goal` (each closer on the bare statement, once per problem), so automation that proves a goal by
  itself is never the model's. Reported on the report half by problem hash (recovery built on the tune half), per
  problem and per rung with Wilson intervals: as recorded, recovery off and on (each through the chain), tools
  alone, and "model-assisted only" (on, not tools alone) beside "tools alone only"; neither alone is a net lift, and
  failure-selected numbers are never a whole-lane claim. Exploratory: a historical cohort; fresh allam answers test
  it again. The cohort is the full answered set (1,190, frozen with its query and provenance in
  ledger/replay/README.md; all already public on /attempts), kumori-89's call over a new read endpoint. Lean runs
  only in CI's sandbox (`attempt.yml` fixer_target=replay). Codex: DISAGREE 20261024T161556623579Z (the `sorry`
  baseline never reaches automation, recovery in the wrong place, a failure-only cohort), AGREE
  20261024T161801868685Z with follow-ups taken (first accepts kept, the cohort reconciled not cut, held out by
  problem). On the build, DISAGREE 20261024T170221251251Z, fixed: the three attempts read during diagnosis
  (15335, 15336, 15354) take their problems out; only results of the current code and Lean, for eligible attempts,
  count; a problem counts only once every attempt has both arms and tools alone, the rest shown as pending, never as
  failures; tools alone has one owner slice per problem; every rung has its own interval.

- **The size series: 45 solved targets re-run every week by Ministral 3B, 8B and 14B (the -2512 snapshots) with
  that week's chain (`tools/toolscore.py`, extending the speed receipt #191).** Audit, 2026-10-24: nothing re-ran
  solved work with fresh calls. #191's re-solve wrote 0 answered tries in 4 nightly runs; its one pinned lane,
  openrouter-minimax-m3-1-flash, now answers "HTTP 404: unknown backend", which the code took for a spent share and
  stopped quietly. The rest (#462, #463, `--speed`, the retro) replays stored answers; the ladder tries a cell once.
  Now a gone lane is `lane_gone` in ledger/speed/ and turns the nightly run red; a refused one skips only itself.
  The sample is frozen once (ledger/speed/sample-solved-2026-10-24.jsonl, cohort `solved`): first accepted before
  2026-10-24, report half, proportional to rung by largest remainder, at least 3 per rung, weights kept; 45 of the
  329 solved, 11 rungs. Each week every lane gets up to 3 tries a problem and stops at its first raw accept; each
  arm's cost runs to its own first accept (raw = the model's answer, with tools = after the chain); a problem with
  none is "not solved within 3", never 3. Reported: per arm solved with a per-problem Wilson interval, attempts to
  first accept, requests (retries included) and output chars, as proxies (kumori reports no tokens yet). One family at
  three sizes, not a controlled size experiment; a pilot, and no parity claim unless intervals separate. Practice:
  cost-of-pass (Erol et al., arXiv 2504.13359, 2025). Codex: DISAGREE 20261024T150248489394Z and
  20261024T150510924100Z (schema, cohort boundaries, paired replay, arm costs, request caps, pilot statistics), all
  taken. **Call and residuals:** the paired replay (stored answers through an older and a newer chain, the only
  week-over-week tool-lift claim) ships next week, when a second run week exists; every row keeps its answer,
  answer_id, tools_hash and lean_env for it. The cap is 80 requests per process (6 nightly slices, so 480 at most),
  every request counted before it is made and every one spent on the record (cut-short and refused tries too). On the
  built code Codex DISAGREE 20261024T151621770745Z (cap per request, refusals, gone then crash, weekly tries, arm
  costs) and 20261024T152323969171Z (gone lost in a same-round crash, spent requests off the record); all fixed, the
  last two with tests that failed on the build itself. **Residual:** the first build's five fixes were shown failing
  against main, not against that build, which was not kept. **The weekly series is re-pinned** to
  agnes-agnes-2-5-flash, so a gone lane does not turn every night red: among live lanes with 40+ cold answers in the
  14 days to 2026-10-24 it is active (not probationary), 353/584 cold accepts (60.4%), 37 errors; the higher-rate
  qwen3.8-27b lanes are probationary (146 errors on 77 answers) or error-bound (1,113 errors on 156). A new lane starts
  a new series. Every try now also records the provider's prompt, completion and thinking tokens (kumori ef6b11b,
  #562); the size report sums output tokens per arm, thinking included per adapter (OpenAI-shaped lanes count it
  inside completion_tokens, Google's own API apart; kumori `_backends.py`), shows "unknown" where no counts came
  back and how many tries lacked them. Codex DISAGREE 20261024T155243924125Z (thinking counted twice, missing counts
  shown as 0), fixed.
  **First run, 2026-10-24 (40114239227): 5 answered tries**, because every lane refused once around 17:03Z and the
  re-solve dropped it for the run, without keeping the refusal's text, and the table counted untried problems as
  failures ("0/45"). Fixed: a refused lane is waited for (the server's retry_after when it gives one, at most 600 s,
  else 180 s) and asked again up to 2 times a run, never for daily_cap_exhausted; every refusal recorded with the
  router's text and kumori's error_code; no request past the deadline, a retry after a wait included; each row its
  own answer_id beside the try_id it shares with the refusal before it (Codex DISAGREE 20261024T191033337558Z and
  20261024T191733767933Z: the deadline sits in the per-request wrapper, so router-error retries stop at it too;
  fixed and recorded after the second round under the 2026-10-24 rule); each arm's interval is over its finished problems (solved, or not within 3),
  owed ones shown apart.
  **kumori's lane contract, 2026-10-24:** a pin to a paused, flaky or newly found lane answers 503 {paused: true,
  retry_after_s: 3600}, a catalog lookup failure 503 {retry_after_s: 60}, and only a retired or never-catalogued lane
  answers 404 "unknown backend". So only a 404 is `lane_gone` (red run); a paused lane, a catalog miss or a known
  refusal code is a refusal, recorded, waited for when its clock is at most 600 s and ends before the deadline, else
  the lane is left for this run and comes back next run. An upstream 5xx, which kumori also answers as 503
  {retry_after_s: 30}, stays a router error (Codex DISAGREE 20261024T203935061717Z, fixed).

- **The relay backs off after 160 relay jobs without an accept (`relay.RELAY_DRY_JOBS`): then a job relays only on a
  wake, each wake spent once, and a backed-off job never chains the next.** Measured from the ledger by run_id
  (2026-10-24): 478 relay jobs; the dry streaks before the 9 relay solves were 4, 23, 4, 1, 1, 20, 19, 109 and 154
  jobs, and the current one is 134 (last relay solve 2026-10-18). Relay jobs per day, 10-18..24: 26, 32, 12, 14, 21,
  34, 19. A threshold of 30 (the plan's first number) would have pushed the 10-14 and 10-18 solves back by ~79 and
  ~123 days at one job a day; any threshold under 109 delays a past solve, and 160 delays none. A trial: the long
  streaks predate the 10-23 per-problem budget, which may shorten them. Re-open with new solves. Wakes: a person
  comment newer than the problem's last relay try (once per comment), a lane in the job whose model never relayed
  anything (once per model, spent even when the lane is parked and writes no relay row), and the daily probe once the
  last relay activity is 24 h old. The state is one file per job that picked a problem, `ledger/relay-jobs/
  <run_id>-<run_attempt>.json` (fixer-only jobs included), plus the relay rows. **Accepted residual (Andy, option B):
  the record is published after the job, so a failed publish or a crash can let the next job spend the same wake
  again; the job count stays bounded by the cron and the ladder hand-offs, never a chain.** Codex's fix (reserve the
  wake and publish before any relay work) would put a push token next to the step that runs untrusted Lean; not taken.
  Codex: DISAGREE 20261024T133712452968Z, 20261024T134108240062Z, 20261024T140235994841Z, 20261024T140526958577Z
  (the last on this residual alone).

- **The scheduled TPU leg runs the 8B again; the 32B (#534) goes only by hand (prover.yml dispatch `push` +
  `tpu32`).** Both 32B batches died in loading at ~80 min and Kaggle kept nothing: tpu32-20261021T2327, and
  tpu32-20261023T1659 (18 heartbeats, all `loading` after the venv, last at 4,501 s, memory peak 153 of 354 GB, no OOM
  event; Kaggle's ListKernelSessionOutput returned no files and an empty log on 2026-10-24). The 8B on the same TPU:
  tpu-20261020T2225, 640 answers in 92.7 min, 1,274 tok/s. After a failed tpu32- batch the scheduled leg pushes the
  8B once the failure's record (ledger/prover-beats/failed.jsonl) is confirmed on main, and only after it reserves
  that replacement in the same ledger, published and confirmed on main before `kaggle kernels push`: one replacement
  per failed 32B batch by our own ledger, never Kaggle's read-back after a push (undocumented). A push that fails
  after its reservation is not retried; a person reads it. **Accepted residual (fails closed):** any interruption
  after the reservation reaches main, the confirming fetch included, spends the one replacement with no push; the run
  goes red and a person dispatches the 8B with `push` (Codex 20261024T144736458820Z offered "accept and document").
  A failed 8B batch is never replaced. Worst case: one 8B session, up to 8.5 h of the week's TPU quota, the same as any scheduled 8B
  batch. The 32B's lane and rows stay its own (`prover-32b`); its #534 bar now waits on a hand dispatch once a
  captured log or heartbeats show the cause. Andy approved the plan; Codex on the built code: DISAGREE
  20261024T141626925446Z (a tpu32 input could make the replacement a 32B; fixed) and 20261024T142004542959Z (the
  guard leaned on Kaggle's read-back; replaced by the reservation).

## 2026-10-23

- **The relay gives each problem 10 answered tries, and 30 once a try made progress (`relay.PROBLEM_FIRST`,
  `PROBLEM_CAP`); then it rests until a person speaks or a model that never relayed it is live. The 1,000-try
  ceiling stays as the outer bound.** Andy: "if this is best practice, do it". Measured from the ledger,
  10-06..10-23: 4,418 relay rows on 102 problems produced 9 solves, whose first accepts came at answered tries 1, 1,
  2, 3, 5, 5, 6, 20, 27; the 93 never-solved problems took 4,311 of the rows (median 48). Progress is the subgoal
  loop closing a step with Lean or proving a lemma (`tools.subgoals`, 749 relay rows): both late solves showed it by
  their 2nd answered try, and so did 54 of the 93 unsolved within 10. Replayed on that history: 10-then-30 keeps all
  9 on 1,974 of 3,075 answered tries; a flat 30 keeps 9 on 2,556, a flat 20 keeps 8, and 5-then-30 keeps 9 on 1,546
  but sits within one try of two solves (at 5 and 6), too tight for 9 data points. Lane errors (1,343 rows, 30%) do
  not count: they are the router's or provider's failure, and the solves at tries 19 and 41 each followed 14. The
  job re-checks before every lane and try, on its own rows too, so an explicit --only target faces it as well.
  Practice: a small budget for every problem, more only where there is a sign of solvability (successive halving,
  Li et al., JMLR 2018; bandit allocation that stops feeding unsolvable queries, Zuo and Zhu, arXiv 2506.12721,
  2025). Codex DISAGREE on the first cut (wrong progress field, cap checked only at selection), then fixed.
  On 2026-10-23 it rests 36 of 49 open problems. Re-open with more solves.

## 2026-10-22

- **Sparebrains' needle metrics, for the tracker's impact field (trial agreed 2026-10-22 by the sparebrains,
  kumori, cardstock, code-56 and rog-gateway sessions and Codex with deep-search; Andy took the
  recommendations).** M1: first-time accepted targets per week, from the ledger (`tools/retro.py`'s
  first-ever-accept count; 39 in 10-15..22). M2: an openproblems method passing the pre-registered bar (0 of 1
  shot used so far). M4: named outside users of a sparebrains result (0 as of 2026-10-22; #465). A needle task
  cites one of these. formal-conjectures (#478) is not declared a metric: Leanstral 0 of 88 declarations and the
  automation sweep 0 of 139, so it ranks as nice until a prover reaches it.

- **A parse error is `parse_error`; `lean3_syntax` now means Lean 3.** The old label put every parse error
  ("unexpected token", a stray `...`) under Lean 3: 6,630 ledger rows, of which 5 name `begin`/`end`, and on
  2026-10-07 only 10 of 400 such rejects on open problems were really Lean 3. `ladder.failure_kind` now returns
  `lean3_syntax` only when the proof reads as Lean 3 (`fixer.looks_lean3`) or Lean names `begin`/`end`, else
  `parse_error`. Past rows keep their label (a ledger row is a record, not rewritten). Shipped after kumori's
  FORM, FORM_FIXABLE and `_NOT_MATH` took `parse_error` beside `lean3_syntax`, so the fixer's near-miss feed
  loses nothing.

- **openproblems test scoring 1 of 3 missed the bar; validation now asks for the bar's own intervals.** Evolve
  39538429513 round 12 led knnr_py on validation by points only (normal rmse 0.9304 vs 0.9688, Pearson per cell
  0.7876 vs 0.7856; swap 0.3176 vs 0.3229, 0.7612 vs 0.7497). On the test set (run 39696762308,
  `ledger/openproblems/final-39696762308.json`) rmse held (0.6927 vs 0.7239, interval -0.040 to -0.023) but
  Pearson per cell fell (0.7508 vs 0.7706, interval -0.024 to -0.016), and swap was a shade worse on both. Not
  useful; 2 scorings left. The +0.002 Pearson lead was noise. Now `prepare` keeps knnr_py's validation predictions
  and every candidate carries the same paired bootstrap the bar uses (2,000 resamples over the site-1 cells); a
  candidate qualifies for a scoring only if its rmse interval sits below zero and its Pearson interval above, as on
  test. Rows scored before this can still seed a run but cannot qualify.
- **The weekly retro is a page in the ledger, not an issue (task #460).** `tools/retro.py` reads the ledger
  alone and writes `ledger/retro/<year>-W<week>.md` for the last closed ISO week: tries and accepts by mode,
  first-time solves (a target's first accept ever) and the loop's stop reasons beside the week before, with the one
  that grew most. `retro.yml` runs it daily as a backup for GitHub's dropped crons; a week whose page exists
  publishes nothing, and a rerun writes the same bytes. A GitHub issue stays Andy's call each time. First page
  (2026-W42, dry run): 8,746 tries, 14 first-time solves (5 checked against the date each first entered
  `verified/`, all inside the week), "1 step left for a model" grew most (705 to 944).
- **Benchmark rows are fenced off from every reader of tries (task #191, step 1).** The speed receipt's re-solves will
  live in `ledger/speed/`. Eight readers walked the ledger themselves (attempt, ladder, decompose, goal_closer,
  retro, prover, problem_issues twice); a speed row would have retired ladder cells, owed prover samples or closed
  an issue. All go through `tools/ledger_files.try_files` now, which leaves out `speed/` by where a file sits and
  where it points, and a test fails if a tool walks the ledger itself again. On today's ledger it returns the same
  1,405 files. Reviewed by Codex to ACCEPT in three rounds (round 1 found the missed `--digest` reader and the
  `--ledger ledger/speed` bypass; round 2 the links out of `speed/` and the per-set reader).
- **fc_prove keeps its answers and judges two at a time under Lean's memory cap (task #478).** Run 39695793555 lost
  all 40 Leanstral answers (77 min of generation): the runner shut down 3 min into judging (exit 143; even the
  `always()` publish step was skipped), with 4 Lean checks at once in formal-conjectures' build. Suspected memory
  pressure, not proven: one check with `import Mathlib` peaks at 3.35 GB resident, so 4 sit near 13.4 GB on a 16 GB
  runner before any proof. Now: the answers are an artifact before any Lean runs; 2 checks at once (the sweep
  too), each `lean -M 6000`, so a runaway proof fails alone; and a check that hits the memory cap or the timeout
  is verdict `resource`, which decides nothing, so the declaration is asked again instead of counting as a reject.
  Codex ACCEPT after three rounds (round 2 found effort() still counting resource rows).
- **The evolve brief names the swap direction's memory trap (task #477).** Evolve 39698543319 (the first with the
  validation gate) ran only 2 of 20 rounds: 12 crashed on swap allocating 5.35 GiB to cast its 51,506 x 13,953
  float32 Y_train to float64 inside a 13 GiB budget, 2 imported PLSRegression from the wrong module, 3 got empty
  replies. Two lines in the brief; the crash rate is measured on the next run. Its gate also showed a limit: with
  ~15,000 validation cells the intervals are tiny (round 6: Pearson +0.0021 to +0.0037), so shot 1's lead would
  likely have passed it and still failed on test. The miss is the shift from site 1 to site 4, not noise; a
  shift-robust check comes before shot 2 (task #477).
- **A test scoring is reserved, in public, before the test set is read; the candidate sandbox has holes, now
  partly closed (task #477).** Two existing defects found by a Codex review of the leave-one-site-out design:
  - *Shots:* `final-*.json` was written only after scoring, so a run lost mid-scoring would not count. Now a
    `reserve` step publishes `shot-<run>.json` (candidate source and code hash) before the sandbox exists; `final()`
    scores only under its own run's reservation for that exact code; shots are unique runs over both files (the
    existing scoring still counts 1). The push token lives in `.git/config` for that step only, and the step fails
    if it is still there.
  - *Leaks:* the sandbox user could read both directions' inputs all run, and the other direction's `X_test` is
    this one's answer. Now each candidate runs with only its own inputs open, and the job fails if any of its
    processes survives. Still open, so validation and test scores are not yet enforceably leak-proof: a candidate
    can leave files in its home or output directory for a later one, and it has network access (the answer files
    are public). No candidate shows signs of either (validation rmse ~0.93, shot 1 lost). The fix is a container per
    candidate with no network and throwaway storage; it comes before shot 2.
  - *The prediction file:* the host `np.load()`ed the candidate's output and so followed a link: a candidate could
    have pointed it at `answers/Y_val.npy` and scored the answers. Now `load_prediction` opens it without following
    links, takes only a regular `.npy` 1.0/2.0 file whose header is under 4 KiB (checked before NumPy reads it),
    float32 of the expected shape and exact size, after the candidate's processes are gone. Codex AGREE after two
    rounds (round 1 found NumPy reads a declared header whole, up to 4 GiB, before its own limit).
- **Evolve now ranks by the metric we lose, and starts from the published winner, credited and disclosed (task
  #477).** Shot 1 won rmse on test and lost Pearson per cell; selection had picked the lowest rmse among candidates
  merely tied on Pearson. `best()` now needs both metrics strictly better than knnr_py on validation (the bar's
  pair) and ranks by Pearson, rmse breaking ties (shrinkage as the cause is our hypothesis, not established). A
  deep-search found the cause the two models had not: the organizers' results paper (Lance et al., PMLR 176, 2022)
  says expression scales differ by site, limiting generalization to an unseen site. The brief now describes their
  GEX->ADT winner (Guanlab-dengkw: train+test SVD, a z-score of each cell's reduced row, RBF kernel ridge on an
  output SVD, models on batch halves averaged; swap per its own code: no input SVD, 50 output components), plus our
  adaptation (each kernel model on at most 12,000 cells). Under the bar's "who writes it" clause the brief was chosen
  and adapted by Claude Opus, and every evolve row says so (`brief_assist`). Resource fit is unverified until the
  next run. Codex AGREE after three rounds (round 3 read the upstream script itself).
- **Every openproblems candidate runs in its own gVisor container (task #477; before shot 2).** Replaces the
  sandbox user and the permission fence, which left shared scratch space and the network (the answer files are
  public on S3) open. `docker_cmd`: gVisor `runsc`, no network, read-only root, only this direction's inputs and
  the code mounted read-only, a 2 GiB tmpfs scratch that dies with it, capped memory/CPU/processes, no
  capabilities, no privilege escalation, no logs, a non-root user. The prediction streams back on stdout (exactly
  rows x columns float32; anything more or less is the candidate's error), so there is no output file to trust;
  the candidate's own prints go to stderr, kept to 64 KiB. Each container is named, killed and removed whatever
  happens, and confirmed gone (only Docker's "no such container" counts), or the job fails. Pinned image
  (python:3.12-slim by digest; numpy 2.5.4, scipy 1.18.1, scikit-learn 1.9.1, PyPI 2026-10-22), host numerical
  libraries pinned to match. `tools/sandbox/check.sh` installs gVisor from its apt repository and runs canaries
  before any round, and in the final workflow before the shot is reserved: no network, read-only mounts (on
  world-writable probes), scratch, process and memory limits, and a known prediction streaming back; the network
  canary was seen going red without a container. gVisor is one accepted option for LLM-written code, not a
  settled consensus: guides split, some defaulting to Firecracker/Kata microVMs for all untrusted code (deep-search
  2026-10-22; kumori's work ask --research run 20261022T032225101775Z_codex). Codex AGREE after four rounds.
  Proven on the runner by smoke 39718520624 (every canary green; gVisor's pids limit bounds host tasks, not guest
  threads, so a thread explosion is bounded by the memory cap, checked by its own canary).
- **Leave-one-site-out comes before any test scoring: a protocol amendment, frozen before its canary (task #477).**
  Shot 1 passed site-1 validation and lost Pearson on site 4, and the organizers' paper names per-site scale as the
  reason. So the honest-selection rule gains a second check, still on training data only, motivated by an observed
  test result (disclosed as such). Policy loso-v1, fixed now and not tuned afterwards: every training site held out
  in turn, both directions, the candidate in its own gVisor container; it must beat `knnr_chunked` (seed 0) on that
  site on rmse (lower) and Pearson per cell (higher), strictly, at every site, with no execution error; mean and
  worst-site Pearson deltas are reported beside the verdict. `openproblems_qualify.yml` writes
  `ledger/openproblems/qualify-<run>.json`, bound to the candidate's code hash and the policy; `reserve` and
  `final()` refuse a candidate without a passing receipt for its exact code, recomputing the verdict from the rows.
  It supplements the site-1 validation gate, which still selects candidates. Canary: shot 1's candidate (evolve
  39538429513 round 12) must fail on its metrics; a crash or timeout would be an execution failure, not a pass.
- **The seeded brief's first run (evolve 39713090991): one candidate with a real Pearson lead, short on swap rmse.**
  Round 1 (kernel ridge on input and output SVDs, from the Guanlab-dengkw starting point) reached validation
  Pearson per cell 0.8072 vs knnr_py's 0.7857 (+0.021, interval +0.0207 to +0.0223; shot 1 had +0.002) and rmse
  0.9228 vs 0.9686, and led on swap Pearson (0.7568 vs 0.7494), but swap rmse was 0.3768 vs 0.3230, so it fails
  the bar's swap check and is not selected. Its "per-cell z-score" was StandardScaler, which standardizes columns:
  the recipe's per-cell step is still untried. 14 of 20 rounds crashed (7 broadcasting a statistic of one set's rows
  against the other's, 3 TruncatedSVD has no dtype, 1 KernelRidge has no fit_intercept, 1 centring a sparse matrix);
  each is now named in the brief, with the row-wise z-score written out. Runner proof is a smoke run; real candidates only after it.

## 2026-10-20

- **Leanstral's token cap 40,000 -> 120,000, and a cut-off answer is not a try.** The lane went idle at
  2026-10-20 04:13 UTC with all 20 of its problems at 8 tries, and 117 of those 160 tries had stopped at the cap
  (`finish=length`) before writing a proof; over the lane's whole ledger 129 of 225 answers did, and every one was
  rejected (all 11 accepts finished on their own). Decomposition hit the same wall: 25 of 65 asks in run
  39288256126 came back empty at 40,000 tokens. Mistral's model card gives 128k max output (docs.mistral.ai,
  Leanstral 1.5, read 2026-10-20), so the cap is 120,000; at the measured 177 tokens a second a full answer takes
  ~11 minutes (HTTP timeout 600 -> 1200 s, job 180 -> 240 min). `leanstral.owed` counts only finished answers
  toward the 8 tries, with 24 calls a problem in all as the stop. Still $0 (Labs endpoint). The three head-to-head
  runs of 2026-10-19 ran at 40,000; a later head-to-head runs at 120,000 and is reported apart from them.
  Decomposition likewise no longer counts a goal as tried when every ask for it came back with no answer
  (`decompose.tried_by`): 45 of the 83 goals Leanstral had "tried" get asked again.
- **The TPU carries real work (task #479).** Its smoke batch (tpu-smoke-20261018T2210, read 2026-10-20) queued
  ~27 h, loaded in 25 minutes, then wrote 24 answers in 94.5 s at 821 tokens a second, none cut off (the T4 x2 ran
  72-78 on long answers; not like for like). From today `prover.yml` runs two legs one after the other: the T4 x2
  as before (bar, plan and goal batches) and the TPU on every open problem outside the bar's 50 (20 today, 32
  samples each, batch ids `tpu-`), sized to the TPU's own weekly hours (`prover.py hours --tpu`: a session of at
  most 8.5 h, none under 2.5 h, generation stopping 1.5 h before the end for the load and a last chunk). Same model,
  prompt and judge, so its rows are the prover lane's, with `TPU v5e-8` in their request config. `prover_tpu.yml`
  and `smoke-tpu` are retired: a smoke push would take the lane's kernel and its one queue slot.
- **The openproblems.bio task: predict_modality (task #477, roadmap row 10).** Seven tasks scouted the same day
  (GitHub API, the public S3 bucket, the website repo). Picked for the two steps after reproduction: its results
  were re-run three times in three weeks (S3 `results/run_2026-10-10_07-15-14`), so a contributed method gets
  scored, and outside method PRs merged in 4 to 8 days (#72 sciPENN, #81, #68). First target:
  `openproblems_neurips2021/bmmc_cite/normal` (~0.8 GB), the deterministic baselines `lm` (rmse 0.7553, mean
  Pearson per cell 0.6919) and `knnr_py` (rmse 0.7233, 0.7707), reproduced within 1% on a GitHub runner.
  Runner-up label_projection (re-run 2026-09-21, cheap knn, but outside PRs 11 to 64 days and three open 1 to 7
  months). Out: perturbation_prediction (no push since 2025-07, top methods 22-52 GB), denoising (published rows
  are 2023 datasets the repo no longer ships), dimensionality_reduction (no outside method PR ever merged),
  batch_integration (outside PRs waited 2 to 12 months), grn_inference (quiet since 2026-06, not on the website).
  The cost: no cancer data. GRN's cell-line screens (HCT116 colorectal, K562 leukemia) are the cancer-adjacent
  door after this one.
- **Reproduced the same day, within 1% (roadmap row 10).** `tools/openproblems.py`: the task's own `knnr_py`
  and `mse` scripts at a pinned commit, only their VIASH block swapped, on the public `log_cp10k` data, scored
  against the maintainers' `score_uns.yaml`. rmse 0.7238 against 0.7233 (+0.07%), mae 0.5260 against 0.5255
  (+0.09%), 80 s on a laptop (ledger/openproblems/). A first run gave +0.15% and +0.18%: upstream's TruncatedSVD
  is unseeded, so runs differ by ~0.1%. Canary: the script's example parameters (4 components, 5 neighbors) miss
  by +17.7%, so the gate fails what it should. Not yet run: the R correlation metric and the R `lm` baseline.
  Next: a method of our own, written by free models with our tools, scored the same way (row 11).
  *The whole metric set, 2026-10-21:* the task's R correlation script, run unchanged (VIASH block only) in its own
  image (`openproblems/base_r:1` with its config's CRAN packages), on a fresh `knnr_py` run: all 8 metrics within
  0.17% (rmse +0.12%, mae +0.17%, Pearson/Spearman per cell, per gene and overall +0.05% to +0.11%;
  ledger/openproblems/predict_modality-knnr_py-20261021.json). A final candidate is scored the same way.
- **The bar for "a useful method", written before any method of ours is scored (roadmap row 11).** The
  leaderboard on `bmmc_cite/normal` (run 2026-10-10) has two tiers: the three NeurIPS 2021 winners at rmse
  0.656-0.663 (senkin_tmp 0.6561, ss_opm 0.6576, guanlab_dengkw_pm 0.6634; mean Pearson per cell 0.786-0.812),
  then everything else from 0.7233 (knnr_py, 0.7707) down. Its test set is 1,000 cells, 72% from site 4, which
  training never sees.
  - **Useful:** better than knnr_py, the best method outside the winners, on both rmse and mean Pearson per cell,
    with a paired bootstrap over the 1,000 test cells (10,000 resamples) whose 95% interval for each difference
    excludes zero; and no worse than knnr_py on `bmmc_cite/swap`, so a win on one direction is not a fit to it.
  - **Competitive:** rmse at or under 0.6634 with mean Pearson per cell at or over 0.7857, i.e. among the
    winners. Reported if reached; not the bar.
  - **Honest selection:** every choice (features, model, settings) is made on a validation set cut from
    training the way the test set is: all of site 1 (s1d1-s1d3, 14,669 cells) held out. The test set scores a
    candidate only when it is final, at most 3 candidates in all, and every test score is published, not the
    best. Scored by the task's own metric scripts through `tools/openproblems.py`.
  - **Who writes it:** free models through our tools write and repair the code (the headline); any frontier-model
    help is labeled with its drafter and reported apart. Compute: a GitHub runner or Kaggle, $0.
  - What a miss means: the numbers are published as they came out, and the method is not opened as a PR.
  - *How the swap check is scored (2026-10-21):* the candidate on bmmc_cite/swap through the task's scripts,
    against knnr_py's published swap scores (run_2026-10-10). A fresh knnr_py on swap needs ~10 GB (a dense
    66k x 13,953 RNA matrix and a 1,000 x 100 x 13,953 neighbor array) and was killed on a 16 GB runner; the swap
    check compares scores only, and our knnr_py runs matched the published ones within 0.2%. The normal
    direction's bootstrap still uses a fresh knnr_py run.
- **Validation now sees both directions, as the bar does (2026-10-21).** The first candidates past knnr_py on
  validation (evolve-39527523508 round 6: rmse 0.9423 vs 0.9684, Pearson 0.7981 vs 0.7857; evolve-39533744774
  round 19: 0.9393 vs 0.9692, 0.7922 vs 0.7858) open with TruncatedSVD(150 or 200), which cannot run on swap's
  134 protein features, and clip predictions to +-2: each would have spent one of the 3 test scorings to fail the
  swap check. No test scoring was spent. The loop had only ever shown the normal direction. Now the brief says
  predict() must work both ways, every candidate is scored on a swap validation split too (site 1 held out), and
  a candidate qualifies only if it is also no worse than knnr_py there. The swap reference is `knnr_chunked`,
  knnr_py's algorithm with the test rows in chunks (the upstream script would need ~82 GB); on the normal test
  set it matched the published knnr_py (rmse +0.10%, Pearson +0.01%).
- **The evolve brief names the pitfalls that crashed earlier candidates (2026-10-21).** 14 of 34 candidates over
  3 runs crashed, nearly all on library misuse (MultiOutputRegressor's module, random_state on Ridge/PLS, sparse
  .std(), StandardScaler centering a sparse matrix, a dense 14,669 x 51,506 matrix, n_neighbors > rows). One
  line each in the brief; the crash rate is measured on the next runs.
- **The method loop is built (`tools/openproblems.py evolve`, `.github/workflows/openproblems.yml`).** The writer
  (Leanstral by default; any router lane) sees the brief, the best candidate so far with its validation scores, and
  the last outcome, and writes `predict()`. Each candidate runs as the sandbox user with an emptied environment,
  13 GB and 20 minutes, on the validation inputs only; the answers and the downloaded test data are not readable
  to it. Validation scores use our Python metrics, which match the task's scripts on the same prediction (rmse and
  mae exact, Pearson per cell 0.7706 against the R script's 0.7707). Reference on validation: knnr_py rmse 0.9682,
  Pearson per cell 0.7854 (site 1 is a harder shift than the test set's site 4: 0.7238 there).
- **Kaggle's weekly hours are spent on an even line (Andy: plan the quota over its window, not in one sitting).**
  This week 29.45 of the GPU's 30 hours were gone by Monday night (three batches in three days), then five idle
  days; the TPU's 20 sat at 0.40 until today. `prover.py hours` now caps each batch at an even line through the
  week, at most a day ahead: total x (hours since Saturday 00:00 UTC + 24) / 168, less what is used. About 4.3 GPU
  and 2.9 TPU hours a day; a missed day carries forward. The GPU's floor rises from 1 to 2 hours so a share is not
  cut into batches that each pay the ~9 minute model load. What is not paced, because nothing runs out: GitHub
  Actions on this public repo and Leanstral's Labs API (38 requests and 5M tokens a minute); their limit is work
  to give them. The plan batch (25 problems, ~5.3 h) is cut by the first day's share and carried over by
  `plan_owed`.
- **What a strong prover is known to reach (`tools/reachable.py`, `ledger/reachable.json`).** DeepSeek-Prover-V2-671B
  and Kimina-Prover publish their miniF2F solutions; checked statement for statement against ours (pinned commits),
  186 of our 244 test targets have a published proof of the same theorem and 32 were proved only as a different
  one: ours is usually the corrected statement (IsLeast where they proved a bound, set equality where they proved
  one side, no hypothesis that leaks the answer). Of the 51 open on 2026-10-20, 20 were reachable that way (15 in
  the bar's rungs); Leanstral solved one of them (`induction_prod1p1onk3le3m1onn`) the same night, leaving 19. The
  rest are the corrected statements or unsolved by both. Goedel-Prover-V2's own miniF2F matches ours on 201 of 244.
- **The 32B on the free TPU, rules written before it runs (task #534).** Goedel-Prover-V2-32B fits the TPU v5e-8's
  128 GB in bf16 (65.5 GB of weights; one 80 GB GPU would need an untested FP8 conversion). Its own lane
  (`kaggle-goedel-prover-v2-32b`, try mode `prover-32b`), the 8B's prompt, sampling and 16,000-token cap so the
  model is the only change, 32 samples a problem, judged by the same kernel, fixer and loop. Targets: the reachable
  open problems; the bar's rungs only once the plan arm (#433) is judged, so the 32B never takes problems out of it.
  It runs after the 8B's TPU batch is judged. What we may say: "the 32B reaches problems the free lanes did not"
  only with at least 3 first-time solves on those targets within 7 days of its first batch's judging; otherwise
  the numbers, no claim. Expected from the paper's pass@32 gap (88.0% against 84.6%) and our open set: about 4 to 6.
  Unknowns the first batch settles: whether the TPU VM's disk holds the 65 GB download, and vllm-tpu on the 32B.
  The paid fallback (prepaid GPU, ~$3 a pass, sized in #534) only if the TPU queue passes 24 hours, and only with a
  cost disclosure and Andy's yes.
  *Disk preflight (2026-10-21):* the TPU kernel records free disk on every candidate mount in timing.json, sends
  the model download to the roomiest one (never /kaggle/working, whose files become the kernel's output), and
  stops in seconds with the reason if none holds the weights plus headroom (8B ~27 GB, 32B ~83 GB), instead of
  failing mid-download after a ~27 h queue. Canary: a 900 GB model is refused, the 8B passes.
- **Axle (axle.axiommath.ai, Axiom's free Lean engine; lean-4.33.1 + Mathlib, our toolchain): `disprove` on every
  open statement, anonymous, $0.** It proves the negation with grind and searches counterexamples (Plausible). A
  planted `2 + 2 = 5` was disproved; none of our 50 open miniF2F statements was, and all elaborated. So no open
  problem is a cheaply false statement eating tries; the 31 unreachable are hard, or false in a way grind and
  Plausible cannot show. Its `repair_proofs` is shallow (insert `sorry`, trim trailing tactics, `grind` at open
  goals, option fixes): our fixer and loop already do the useful part, and the dossier near misses it would take
  are ones they already failed, so no head-to-head is scheduled. The "switch to Rocq" in its changelog is dated
  April 1, 2026; every later release is Lean.
- **formal-conjectures, the first upstream door (task #478, roadmap row 9).** google-deepmind/formal-conjectures pins
  Lean v4.33.1 (ours), takes short proofs of solved and test items inline and longer ones as a `@[formal_proof]`
  link to a hosted proof, checks claims with `#print axioms` (PROOFS.md), and writes guidelines for AI agents
  (AGENTS.md). At commit 90d18f6: 101 textbook and 38 test declarations still at `sorry` (and 2,426 research
  solved, 1,512 research open). First step, $0 and read-only toward them: `tools/fc_sweep.py` and fc_sweep.yml run
  our loop's closers on those 139 in their own build, two canaries first (2+2=4 must pass, 2+2=5 must not).
  Anything sent to their repository needs Andy's yes on the exact diff and his signed Google CLA.
  *Sweep result (run 39528990264, 2026-10-21):* 0 of 139 closed by the closers in their build; both canaries
  held (2+2=4 proved, 2+2=5 open), no timeouts, ~45 s a declaration. What is left there is not one tactic deep:
  the easy ones are already proved. Next: a prover writes whole proofs for them in the same build.
  *The prover stage (fc_prove.yml):* Leanstral gets each declaration with its file's context up to it and writes
  a proof; only the proof body is spliced under their statement (a restated, weakened theorem in the reply never
  reaches the file), checked in their build as the sandbox user with the canaries first. Each run takes the next
  40 declarations without a row.
  *Cut-off answers (2026-10-21):* the probe's 6 of 8 that spent all 120,000 tokens are not done: each is asked
  once more, first, with `reasoning_effort: "none"`, recorded per row; asked both ways, it is done.
- **Leanstral: streaming works, and a problem that runs out twice is asked without long reasoning.** Round
  20261021T0100, the first streamed: 15 of 15 answered, 0 errors (the two before lost 12 of 20 and 12 of 17). But 7
  of the 15 spent all 120,000 tokens reasoning with no proof (128k is the model's maximum). A problem whose answers
  hit today's cap twice now gets `reasoning_effort: "none"` (the model card's only other setting; untested on
  proving), recorded in each row's request_config so its answers are measured apart. Caps under the old 40,000
  limit do not count.
- **Leanstral (and decompose) get the bar's problems once the plan arm is judged, reachable ones first.** It ran dry on 10-20 with
  19 problems; the bar's open problems were kept from it for the stage-3 measurement. Same gate as the 32B
  (`prover.plan_owed()` is None), so no lane takes problems out of the plan-arm test. Its queue goes from 15 to 47,
  with the 18 a published prover reached as stated (tools/reachable.py) first. Decompose's goals follow the same rule (`decompose.pick_goals`): 115 of the 208 queued goals sit on reachable
  problems and go first.
- **Leanstral streams its replies.** Round 20261020T2158, the first at 120,000 tokens: all 8 answers that came
  back finished on their own (none cut off), one first-time solve (`numbertheory_fxeq4powxp6powxp9powx_f2powmdvdf2pown`,
  loop-closed), but 12 of 20 calls were dropped ("Remote end closed connection without response") while the long
  reply was being written. Streaming (Mistral's documented `stream`) keeps bytes on the connection; a whole JSON
  reply still reads, and a drop is still retried once.

## 2026-10-19

- **The head-to-head, rules written before its first run (Andy: prove the tools make a model better, and
  cheaper per result).** `tools/headtohead.py`, `.github/workflows/headtohead.yml`. Leanstral alone (the whole
  proof, the raw answer judged) against Leanstral with our tools (decomposition on the whole theorem: steps,
  fixer, the loop's automation, recursion), 4 calls per arm per problem, the same 30 problems (15 open in the
  open list's order, 15 solved from math-L4, math-L5, amc12, aime, imo and custom, picked by a fixed seed), the
  arms in a seeded random order per problem, the same day. What we may say afterwards, and nothing else:
  "better" only if the problems solved by the tools arm alone outnumber those solved by the alone arm alone and
  a two-sided sign test on those disagreements gives p < 0.05; "cheaper per result" only if the tools arm's
  Leanstral calls per solve (every call it spent, over its solves) are lower; otherwise the run is reported as
  it came out, numbers and intervals, with no claim. 30 problems can miss a real difference: a miss is a
  finding about this run, not about the tools.
- **The head-to-head's first run: better and cheaper per result, by the rules above (run 39271052543,
  2026-10-19).** Solved of 30: tools 12 (95% CI 24.6–57.7%), alone 5 (7.3–33.6%). Disagreements: 8 solved by
  the tools arm only, 1 by the alone arm only (induction_nfactltnexpnm1ngt3); a two-sided sign test on those 9
  gives p = 0.039. Leanstral calls per solve: tools 5.8, alone 22.2; tokens per solve 69K against 364K. How
  far it reaches: one flipped disagreement (7 to 2) gives p = 0.18, and 11 of the tools arm's 12 solves were on
  problems already solved; on the 15 open ones the tools arm solved 1 (mathd_numbertheory_277), the alone arm 0.
  What it shows, as of this run: a lift on problems the model can already reach, not reach into new ones.
- **The reach run, rules written before it runs (Andy: yes, 2026-10-19).** The same head-to-head (same arms, 4
  calls per arm, same kernel) on every problem open at dispatch (60 on 2026-10-19), none solved, in two jobs
  (`--slice 0/2`, `1/2`, by a hash of the name, 32 and 28, so a solve between them moves none) because one would
  run near the job's 340-minute limit (run 1 spent 77 minutes of wall time on 15 open problems). What we may say,
  on the two jobs together: "reaches new problems" only if the problems solved by the tools arm alone outnumber
  those solved by the alone arm alone and a two-sided sign test on those gives p < 0.05; otherwise the numbers
  and intervals, no claim. Expected before it runs: at run 1's rate (1 tools-only solve in 15 open) about 4,
  and 4 to 0 is p = 0.125, so a miss is the likely outcome and says the next lever is more calls or a stronger
  prover in the tools arm. Every first-time solve is recorded and published like any other try.
- **The replication, rules written before it runs (2026-10-19).** Run 1's "better" rested on 9 disagreements, 7
  of its 8 tools-only solves on already-solved problems, and one flip takes it from p = 0.039 to 0.18. So the same
  head-to-head again, after the reach run: 30 solved problems from the harder rungs that no earlier head-to-head
  measured, drawn by a new seed (`--seed headtohead-replication-2026-10-19`, 9 custom, 7 amc12, 6 math-L5,
  5 math-L4, 3 aime as previewed on 2026-10-19), 0 open, 4 calls per arm. What we may say, on this run alone:
  "replicated" only if the tools arm's own solves outnumber the alone arm's and a two-sided sign test on those
  disagreements gives p < 0.05; "cheaper per result replicated" only if its calls per solve are lower again.
  Otherwise the numbers and intervals, and run 1's "better" is reported beside them as not replicated.
- **Plan plus prover, rules written before it runs (task #433, Andy: yes, 2026-10-19).** Does a plain-math plan
  help Goedel-Prover-V2-8B on the problems it missed? Hilbert (arXiv 2509.22819) and Draft, Sketch, Prove (arXiv
  2210.12283; model-written drafts 20.9% to 39.3%) say plans help provers; DSP reports human and model drafts as
  separate arms, and so do we. The design, paired: every bar-rung problem still open when the batch is built (37 on
  2026-10-19, before batch 3 was judged), each in two arms in the same Kaggle batch, the model card's prompt
  unchanged in both: `alone` (the statement as it is) and `plan` (the same file with the plan as a Lean comment above
  the theorem, `prover.with_plan`). 4 answers an arm: power comes from the problems (exact McNemar counts only the
  disagreements), not the tries, and 6 problems solved by the plan arm alone against 0 is the smallest pass
  (p = 0.031); 10 problems could not pass short of 6 of 10. Judged raw, no fixer and no loop, identically for both
  arms, each arm stopping at its own first accept (`prover.judge_plan`), rows in ledger/plan-arm/. The plans are
  drafted with Claude Opus in the session that set this bar, written before any plan-arm answer exists, and
  committed (ledger/plan-arm/plans.json) before the batch is pushed; they are kept off the problem threads and
  dossiers so no other arm reads them, and are published with the result. What we may say: "a Claude plan helps the
  prover" only if the plan arm's own solves outnumber the alone arm's and the two-sided sign test gives p < 0.05;
  otherwise the numbers, no claim. Never "our tools" or the free models: a frontier model's plan for a known
  competition problem may carry a remembered solution, so every plan-arm solve is labeled `prover+plan`, its own
  column. The first push after Kaggle's reset (2026-10-24 00:00 UTC) builds it before any goal batch, about 6.3 of
  the week's 30 GPU hours at 94.9 s an answer.
  **What happened (2026-10-20):** the batch pushed early, 2026-10-19 23:57 UTC, into the hours batch 3 left, and
  the budget stop cut it at 7 problems (0 vs 0, p = 1.0). The old `plan_owed` then counted the whole plans file as
  done, so the full test would never have run. Fixed: a problem stays owed until both arms are judged under the
  plans id, and the verdict pools every batch's rows for that id (`prover.plan_verdict`). The remaining 25 open
  problems push after the 2026-10-24 reset; the pre-registered test is all of them together, never the 7 alone.
- **Stage 3 passed, graded early (Andy: grade now).** The bar: at least 5 first-time solves from the prover lane on
  its 50 open problems within 7 days of 2026-10-17 18:30 UTC. Result: 10 in 2 batches; the 5th at 2026-10-19
  05:28 UTC, about 35 h in (batch 20261017T1830: mathd_algebra_17 by fixer+loop, mathd_algebra_275,
  mathd_numbertheory_227, mathd_algebra_289; batch 20261018T1609: amc12b_2021_p3, amc12b_2020_p13,
  amc12a_2009_p7, amc12a_2020_p10, amc12b_2020_p6, amc12b_2020_p21). Verdict posted on #23, which is closed. What
  waited on it, released the same day: the held `grind` proof of aime_1990_p4 published (amc12b_2021_p3, the other
  one held, the prover solved itself in batch 2, which is what holding it protected); `grind` joined the loop's
  closers (`subgoals.AUTO_TACTICS`), so the speed receipt re-runs every frozen week on the new chain; repository
  variable `PROVER_MODE=goals`, so the push after batch 3 is a goal batch, under the goal closer's bar (at least 3
  first-time solves through goals within 7 days of its first batch).

- **Kaggle GPU hours are used exactly (Andy).** Each push reads the week's quota from Kaggle itself (`kaggle quota`,
  CLI 2.2.4; 20.57 of 30 h used at 01:38 UTC) and sizes the session to what is left less 15 min, at most 11.5 h;
  under an hour left, it waits for the reset, Saturday 00:00 UTC (Kaggle staff, product-feedback 173129; the CLI
  reported 2026-10-24T00:00). The kernel starts a chunk only if the measured seconds per answer (103 s from batch
  20261017T1830, or the slowest chunk so far) say it still fits, and chunks are 2 problems, not 4: a 4-problem
  chunk is ~3.7 h and could run past the quota, which Kaggle ends and the workflow treats as a failed batch.
  Sampling (model, temperature, tokens, 32 per problem) is unchanged, so the bar's measurement is too.
- **`grind` on the one-step goals: 2 problems solved, held until the bar is graded.** Lean's `grind`, tried as the
  whole proof of each of the 352 readable goals the loop's automation had left (`tools/goal_closer.py tactic`,
  Lean only, $0), closed 4 and solved 2 problems whole, kernel-accepted twice: minif2f/test/aime_1990_p4 and
  amc12b_2021_p3. Both are among the prover's 50, so publishing them now would take two first-time solves away
  from the bar's measurement; they are kept on Kumori task #461 and published after 2026-10-24 18:30 UTC, when
  `grind` also joins the loop's closers and the speed receipt measures it on the frozen weeks. The other 347 goals
  stopped at the goal itself: one tactic alone is not what most of them need.
- **The tactic sweep, with a back-check on solved problems (Andy: our new tools must prove themselves on our own
  earlier work, timed and logged).** `.github/workflows/tactics.yml`, dispatched by hand, 10 jobs at most: every
  recipe on every one-step goal of the open problems (352) and of the solved ones (95 on 25 problems), one Lean
  run per goal for all recipes, then the kernel's full judge and splice on each recipe that passed. Rows land in
  `ledger/tactics/` with Lean and judge seconds per goal, as measurements (`outcome`, `at`), not tries, so no try
  count or daily log moves; no proof text, so a held bar solve stays held. Canary 2026-10-19: on the two goals
  `grind` had solved and one it had not, the sweep solved exactly the two, in 67 s for 12 recipe-goal pairs
  where one Lean run each takes ~13 min.
  First run (39187801772, 10 jobs, 447 goals x 6 recipes): `grind` solved the two held bar problems again and
  re-solved 7 goals of solved problems; `field_simp; ring_nf; nlinarith` solved minif2f/test/
  algebra_absapbon1pabsapbleqsumabsaon1pabsa, outside the bar, published as a `lean-tactic-recipe` goal-closer
  solve; `bound` re-solved 1 solved-problem goal; `norm_num at *; nlinarith`, `simp_all; omega` and
  `field_simp; linarith` solved nothing. Kernel judge 10 to 16 s median per solve. From the next run on, the
  sweep records its own solves outside the bar (`--publish`).
  Second run (39190138269), recipes built per goal from its own variables, as our verified proofs use them:
  `@nlinarith-sq` (sq_nonneg hints over the real variables, 119 goals) and `@interval-cases` (the first natural or
  integer variable, 208 goals) solved nothing. `grind`, `field_simp; ring_nf; nlinarith` and `bound` repeated
  the first run's solves and back-checks. Finding: one-shot tactics, plain or hinted, have closed what they can
  of these 352 goals (3 problems); what is left needs a step a recipe does not write, which is the goal batches'
  job (a prover per goal, after the bar).
- **What the 223 real-step goals need: steps, not a lemma (diagnosis, `goal_closer.diagnose`).** Kinds, from each
  goal's text: inequality 58, divisibility 57, sets and extremes 48, functional 22, sqrt/log/trig 16, other 15,
  complex 7, so no one specialist tool. Lean's `apply?` found a mathlib lemma that applies for 208 of 223, but
  the ones it names are restructuring (`Set.ext`, `Eq.symm`, `and_or_right`, `refine fun ...`), and a lemma
  closed a goal outright for 1 of 223. So lemma retrieval alone would not close these; it is a later aid to
  whatever writes the steps. The next tool is decomposition: a model writes `have` steps into a goal, the
  closers and recipes take the small ones, and what is left goes round again (roadmap #8), on Leanstral (free)
  and on problems outside the bar first. Found on the way: that one "closed" goal, amc12b_2002_p4's, was
  extracted without its ℚ types (`1 / 2 + 1 / 3 + 1 / 7 = 1 / 42`, true in ℕ where each fraction is 0); the
  splice failed, so no false solve, but a goal that lost its number types is a different statement, and a prover
  given it spends tries on the wrong thing. (Goals extracted since 2026-10-09 print their number types; this one
  is an older row still in the queue.)
- **Decomposition, built (`tools/decompose.py`, `.github/workflows/decompose.yml`).** Leanstral is asked for a
  goal as short `have` steps; the kernel judges; on a reject the loop's Lean-only pass makes the failing steps
  holes and closes what automation can (its closers plus `grind`, which meets only problems outside the bar
  here); each step left goes one level down, 2 levels and 8 asks per goal at most; a proved goal is spliced
  into its problem by `goal_closer.close`. Outside the bar's 50 only until 2026-10-24 (158 goals on 28 problems,
  108 real steps). Each goal is one measurement row in `ledger/decompose/`; a solve is a goal-closer try under
  lane `leanstral-decompose`. It shares the `leanstral` concurrency group, so the two Mistral callers never
  overlap (Labs: 38 requests a minute for the org, each paced to 30). Here the key sits in the step that runs
  Lean, unlike `leanstral.yml`: Lean runs as the sandbox user with a cleared environment, as in `attempt.yml`.
  First run (39199785953, 40 goals, 68 asks, $0, 69 min): **4 problems solved for the first time**: imo_1960_p2,
  algebra_amgm_sum1toneqn_prod1tonleq1, algebra_apbon2pownleqapownpbpowon2 and algebra_ineq_nto1onlt2m1on (by 3
  of its goals), published as goal-closer solves and re-checked by tools/check.py. 28 of 40 goals went two levels
  down; on 6, Lean's automation closed every step Leanstral wrote; 1 goal was proved but did not splice. The
  leak: 24 of 68 asks returned nothing (16 empty, 8 dropped connections), a third of the budget before Lean saw
  an answer. Smoke run before it (39198848367, 3 goals): 0 solved, three different first-level stops, each fixed.
- **GitHub Actions: real project work only, never filler.** GitHub's terms allow hosted runners only for "production,
  testing, deployment, or publication of the software project associated with the repository", and nothing that
  places a burden "disproportionate to the benefits provided to users"; the Free plan runs 20 jobs at once, 6 h a
  job (docs.github.com, read 2026-10-19). Unlike Kaggle there is no weekly allowance to spend, so idle runners are
  not waste. The last 24 h used 77.8 runner-hours, all of it Lean checking this repository's proofs, peaking at 10
  of 20 jobs; the headroom goes to work like the tactic sweeps, on demand and capped.

## 2026-10-18

- **Plan as if nobody helps (Andy).** We are nobody until we deliver, so the plan stops depending on outside
  volunteers: math and biology are ours, with the work shown, and helpers are a bonus. Receipt: no outside
  volunteer has posted as of 2026-10-18; every volunteer-path solve was the maintainer's own sessions.
  `kumori_agents.md` and the volunteer path stay open. The goal becomes solving faster with our tools, shown as
  a weekly speed receipt: each week's problem set frozen, every earlier set re-run by this week's tools, compute
  to first accept charted in public (task #191, built on the tool scoreboard #463). Recruiting posts become
  shipping posts (#458), the weekly tool challenge is parked (#460), and lab outreach becomes finding a first
  user, after a reproduced biology result (#465, roadmap row 15). Users still matter: a lab using a result and a
  benchmark listing a score are doors, not help.

- **The road is now a tool, not a table (Andy, task #470).** The roadmap lives in kumori's `kumori_roadmap`
  table: dated, gated milestones on three tracks (the engine, science with a judge, doors to researchers), each
  with the measured bar that says it happened, a window that is an estimate and never a promise, and a
  visibility per row, so what we show and what we hold back sit in one place (task #473). The public rows open
  https://sparebrains.kumori.ai/next and are served as `/roadmap.json`; partner-lab names stay private. PLAN.md §7
  now points there. Windows move when gates are missed, and a missed gate is published as a finding.
- **The goal closer's bar, written before its first goal batch (Andy, task #461): at least 3 first-time solves
  through goals within 7 days of the first goal batch.** A solve counts when the prover's proof of a one-step goal
  is accepted alone, spliced into that goal's sketch, and the whole problem is kernel-accepted (`goal_closer.close`,
  try mode `goal-closer`). 8 tries per goal on the same Kaggle prover; goals come from `ledger/goal-queue.json`,
  only those whose own file Lean can read, real steps before restatements. It starts only when the repository
  variable `PROVER_MODE` is set to `goals`, after the stage-3 bar is graded, so the prover's measured week is
  untouched. The comparison is the prover's own rate on whole problems.

- **The Leanstral lane's bar, written before its first run (Andy, task #476): at least 3 first-time solves within 7
  days of its first job, on the open problems outside the prover's 50, at 8 tries a problem.** That is 36 problems
  on 2026-10-18 (18 IMO, 17 miniF2F custom, 1 MATH L4), the hardest of the open list; the first version of this entry
  said 32, a miscount corrected the same day before any run. Mistral's open Lean
  prover Leanstral 1.5 (`labs-leanstral-1-5-1`, 588 of 672 on PutnamBench against 86 for Goedel-Prover-V2), on
  Mistral's Labs API at $0 (LiteLLM's price table, checked 2026-10-10). Its limit is its own line on the kumori_team
  org's Limits page, 38 requests and 5,000,000 tokens a minute, separate from Kumori Chat's models; we pace at 0.5
  requests a second or less. Labs needed the org admin's switch (on, 2026-10-18; training on the org's other API calls
  was switched off the same minute), and Mistral may train on Labs inputs and outputs, which are public here anyway.
  Its own key, `SPAREBRAINS_LEANSTRAL_KEY` (shared-connectors-only scope, expires 2027-10-18). The probe on a solved
  problem: `mathd_algebra_17` proved on the first try, kernel-accepted, 45 s, about 7,800 tokens. Kept off the
  prover's 50 until its bar is graded on 2026-10-24, so neither lane's count includes the other's solves; its own try
  mode `leanstral`. The comparison: the prover made 4 first-time solves in its first day on its 50.
  *Round 1 (run 39160239781, 2026-10-18 19:46 UTC):* 36 tries, one per problem; **`imo_1981_p6` solved**, accepted
  after Lean's automation closed 3 failing steps in Leanstral's proof (`fixer+loop`; miniF2F's statement covers only
  the problem's recurrence, per the 10-17 audit). 27 answers had no proof because all 27 hit our 16,000-token cap
  mid-reasoning (`finish: length`, empty text): our setting, not the model. Raised to 40,000 from round 2; the bar
  is unchanged and the round-1 rows stay in the ledger as run.

- **What the science and math tracks can stand on, as of 2026-10-18** (three scouts with the rebuilt deep-search,
  checked against primary pages where noted):
  - **No cancer DREAM challenge is open.** dreamchallenges.org lists four (a cell map, a digital pen, two
    drug-hit challenges), none on cancer; the last cancer ones (CTD2, Anti-PD1) closed in 2019-2020.
  - **No cancer drug-response leaderboard re-runs outside work.** NCI's IMPROVE is a framework without a
    leaderboard (core repo last pushed 2025-09-30); TDC takes self-reported scores by form; Polaris scores
    automatically but has no oncology task. So stretch 5 starts with a partner lab, as the 10-17 scout said.
  - **openproblems.bio is the science door that is open:** maintainers re-run every method on their own cloud,
    repos active this week, but pull request to merge took 11 days to about 14 months (2025-2026 history), and
    scores come later in maintainer batches. We reproduce a task's metrics ourselves first (task #477).
  - **PutnamBench is no longer a gate for us:** four systems solve 672 of 672, and its rules ask that proofs stay
    private, which this project cannot honour. google-deepmind/formal-conjectures accepts proofs and
    misformalization fixes after human review (task #478).
  - **A stronger open prover is in reach for free:** Mistral's Leanstral 1.5 (119B, 6B active; 588 of 672 on
    PutnamBench, against 86 for Goedel-Prover-V2) is listed on kumori's free Mistral key as
    `labs-leanstral-1-5`. Its rate limits are unknown until it runs. It starts after the 10-24 bar, with its own
    bar first (task #476).
  - **Stage 3 so far:** the prover made 4 first-time solves by 2026-10-18 12:00 UTC (`mathd_algebra_17`,
    `_275`, `_289`, `mathd_numbertheory_227`), one of them only after the fixer and loop repaired its answer; the
    bar (5 in 7 days) is graded 2026-10-24 18:30 UTC and nothing in the prover lane changes until then.

## 2026-10-17

- **The goal closer's groundwork (task #461): which goals, and how a proved one goes back.** `tools/goal_closer.py`
  reads the loop's sketches from the ledger and keeps the open problems' one-step goals: as of 2026-10-17, 395
  distinct goals on 83 of 86 open problems (deduplicated by text; the earlier count of 241 used a different
  dedupe). 140 of them restate the theorem, since the sketch kept nothing but `sorry` (aime_1987_p5's is a comment
  and a `sorry`); they are flagged and go last. The other 255 are real steps; imo_1962_p2's goal is one direction
  of its set equality, the hard part, not a restatement. A proof of a goal is judged alone, then spliced into each
  sketch it closes and judged as the whole problem. Checked with Lean on the first five real goals: all ten
  spliced sketches compile with `sorry` in the hole, but one goal file in five does not elaborate alone
  (amc12a_2020_p15: `‖a - b‖` printed with untyped `a`, `b`), so goals are checked first (`list --check`) and only
  those whose own file compiles go to a prover. The prover's goal batches (Goedel-Prover-V2-8B on Kaggle, own
  try mode) start after the 2026-10-24 bar, so the bar's runs are untouched; then Hilbert-style splitting of
  the goals the prover misses. Anyone can try a goal today: `goal_closer.py try --goal SHA --proof FILE`.
- **The tool scoreboard grades each tool by leaving it out (task #463).** `tools/toolscore.py` takes every stored
  cold reject the chain touched (a fixer pass, a closer, or a turn: 4,730 of the ablation's 10,433 rows as of
  2026-10-17), runs the whole chain again, then once per tool that run used with that one tool removed. Same
  answer, same code, so the difference is the tool's: *needed* (the chain turned it, the chain without the tool
  did not) minus *spoiled* (the other way round) is its net, shown on the loop page in points over the same cold
  answers as A, B and C. Leave-one-out was chosen over add-one-in because the chain's tools overlap (when `omega` is
  gone, `linarith` may close the step), and the question a tool builder asks is what is lost without it; the
  cost of that choice is that overlapping tools score low though the chain uses them, and the page says so. A
  closer is re-run only where the chain turned the reject (removing a closer cannot close a step), a fixer pass
  either way (it rewrites the proof, so it can spoil one). Rows are tied to a hash of the chain's code, so a
  changed tool is graded afresh, never mixed with old rows. Held out: odd attempt ids are the report half the
  site shows (2,408 rejects); even ids are the tune half, for building and tuning a tool against. Model-call arms
  (the dossier on or off with the goal closer, #461, Andy's arm) go in the same table under their own arm names.
  The retro now runs the same chain function, so there is one copy of it. It runs nightly after the retro, in
  the time the retro leaves (a local smoke on 2026-10-17 took 1 to 7 minutes a reject, so the first pass takes
  several nights), and on dispatch (`attempt` workflow, `fixer_target=toolscore`, sliced). That smoke, three
  real rejects: without `omega` the chain still turned its reject (`linarith` closed the step), and on another
  reject `exact?` and `aesop` were each needed while the `names` pass was not.
- **The north star, made concrete: verified pieces of work that cancer researchers can use, delivered through
  doors they already trust (Andy).** This refines the entry below ("cancer research as the flagship"). A scout on
  2026-10-17 found that outside contributions reached cancer researchers through a named lab, a published paper
  or a benchmark with a metric, and found no example of an unsolicited AI-generated hypothesis being used; Google's
  Co-Scientist (Nature 2026-05) works because labs ask it their own questions (Nature feature, 2026-09-21), and an
  unvalidated AI biology claim was called "preliminary" by experts (CNN, 2026-10-08). Precedents that used donated
  tumour tissue (Cell Slider, Reverse the Odds: 4.5 million slides) show that patient-derived data can be used
  legitimately. The project's "no personal data" filter (TARGETS.md) is a working choice as of 2026-10-17, not a
  law, and it is challenged here: much open cancer data is patient-derived but de-identified and published for open
  use (TCGA's open-access tier, the NCI Imaging Data Commons' public collections), so the real constraints are
  consent, de-identification and each dataset's terms, decided per dataset. Candidates for the science
  stretches, scouted, not chosen: (1) openproblems.bio, single-cell benchmarks where anyone contributes a method that
  is re-run and scored automatically (14 tasks, 127 public datasets; the tools idea in another field); (2) DREAM
  challenges on Synapse with no patient data (each one's terms checked first); (3) cancer drug response on public
  cell-line data (DepMap, GDSC) with our own held-out split and scorer, which needs a partner lab before anyone uses it.
  Finding one named cancer lab willing to receive the work is a milestone of its own. Kumori tasks #459, #465.
- **The north star and how we get there (Andy, with Claude).** Sparebrains exists to show that people plus
  freely available AI, coordinated and judged by machines, can solve hard problems in the open, aiming at science
  and eventually cancer research; the labs' math results of 2024-2026 (IMO golds, Erdos problems) came almost
  entirely from the labs or people with frontier access, and a 2025-10 claim that GPT-5 "solved 10 Erdos problems"
  was walked back. The road and its judges are in `PLAN.md` §7. Settled today:
  - **Free and open models are the headline; frontier models are the coach, not the player.** Claude or Codex
    write plans and outlines (disclosed, "drafted with ___"); free models write the proofs. A frontier model
    solving directly is kept for problems the free swarm has exhausted, labeled, and counted apart. Every problem
    we solve directly is one the free swarm can never solve first. Volunteers bringing their own AI quota is the
    pitch, and the ledger keeps it in its own column (`volunteer`).
  - **Tools over prompts.** Every measured gain came from tools around the models (the loop: +11.3 points, tiny
    lanes 6.0% to 30.2%), none from re-prompting (the relay: 3 accepts in ~2,682 answers from 10-09). New ideas
    are tried as tools first, each with a bar written before it runs.
  - **The wall, measured:** 5,203 loop repairs on the 86 open problems; 1,384 stopped with one goal left, which
    is 350 distinct sketches and 241 distinct goals across 83 problems (some goals are the whole problem
    restated, e.g. `imo_1962_p2`). The sketches and goals are kept in the ledger (`tools.sketch`,
    `tools.subgoals.goals`) for the lemma queue. Free chat lanes proved 0 of 176 such goals.
  - **The next recipe is APOLLO's and Hilbert's.** APOLLO (arXiv 2505.05758, 84.9% on miniF2F under 8B) sends
    leftover goals to a small Lean-trained prover, not a chat model; Hilbert (arXiv 2509.22819, 99.2% miniF2F,
    462/660 PutnamBench) has a reasoner split the goals the prover misses, recursively, with lemma retrieval.
    After the stage-3 bar (2026-10-24): the 241 goals to Goedel-Prover-V2-8B on Kaggle as their own try mode,
    then recursive plans. Kumori task #461.
  - **A weekly retro and tool challenge**: the bot posts where the swarm got stuck and one tool to build, with
    its scorer and bar; a Kumori Code session builds candidates; the next week grades it in public. Coders who
    are not mathematicians can help there. Kumori task #460.
  - **Two doors for helpers, in this order (Andy).** First, solve one open problem with your own agent
    (`kumori_agents.md`): it works end to end today, and a first-timer gets an unambiguous win in minutes. Second,
    the weekly tool challenge (#460): higher leverage per helper (one tool lifts every model on every problem) and a
    bigger pool (people who code, not only people who do olympiad math), still on their own spare compute. The tool
    door opens only once the tool scoreboard (#463) can grade a contribution objectively, so it is built before the
    recruitment post (#458, after the 2026-10-24 bar).
  - **The durable asset is the toolbox and the map, not the models (Andy).** Free models come and go weekly; the
    tools in `tools/` and the measurements of which models use them well stay, and work on next year's models
    too. So every model is graded on two numbers: raw skill (cold accepts) and **tool lift** (accepts with the
    tools minus without, from the ablation's paired arms; tiny lanes 6.0% to 30.2%). Every tool is graded too: the
    ablation's arms become any tool in the chain, scored on stored rejects with a held-out half. New tools are
    named for their job (`goal_closer.py`, not `cancer_researcher_1.py`). The counterargument is on record: Sutton's
    "bitter lesson" (2019) says general methods with more compute win in the long run, which is the labs' bet;
    tools are the lever a project without a datacenter can pull, and they route the parts tools cannot do to the
    model best at them (Hilbert's reasoner, APOLLO's prover). Kumori tasks #462 (tool lift), #463 (tool scoreboard).
- **We show our work on GitHub too (Andy): every open problem gets a thread, and every judged try reaches it.**
  The threads had gone quiet since 10-09 while the relay kept making 450 to 750 tries a day: most went to
  problems with no thread, and GitHub fired the `issues` workflow for only 22 of 60 attempt runs from 10-16
  (self-chained `workflow_dispatch` runs do not reliably raise `workflow_run`), so 12 relay runs on threaded
  problems were never posted. Now `issues.yml` also runs hourly and `tools/problem_issues.py --catchup` posts
  every judged try (any mode: relay, cold, the loop, the prover, volunteers) that no bot comment has reported,
  found by a run marker in each digest; threads open for every open problem, 25 a run at most; a `log`
  issue gets a daily roll-up of tries, accepts, first-time solves and Actions runs; the prover posts what
  Kaggle said on the stage 3 gate issue at every check, running or not; and the bot can open gate and plan
  issues (`--open`). Every post says what the project is trying to do and points to `kumori_agents.md`.
  Writes are paced 1 s apart and capped at 150 digests a run, under GitHub's 80 a minute and 500 an hour
  (its REST rate-limit docs, read 2026-10-17). Machine output is authored by kumori-ai[bot]; a person's
  solve carries that person's login.
- **Stage 2's verdict: more tries stopped helping (Andy and Claude, from the ledger).** Measured on the
  committed ledger as of 2026-10-17: 27 first-time solves since 2026-10-06 (290 of 378 targets solved,
  88 open, all `minif2f/test`). Where they came from: 15 `fixer+loop` (Lean's automation on stored near
  misses, no model call, all on 10-08), 5 `volunteer` (agents, 10-08), 1 `relay+thread` (#11), 6 `relay`
  alone (3 on 10-08, then 10-09, 10-10, 10-14). From 10-09 the relay made about 3,600 calls for 2,682
  rejects, about 930 errors and 3 accepts, about 0.1% of answered tries; the lanes still answering went
  from 14 to 9 or 10. Every open problem already has 149 to 257 answered tries (median 189). Published
  results put general models' miniF2F numbers at thousands of tries a problem (Kimina-Prover's 80.7% is
  pass@8192, arXiv 2504.11354), which the free pool cannot reach. The loop's shape matched APOLLO
  (arXiv 2505.05758): large gains for weak general models from fixing form and filling holes, little from
  asking the model for the rest. No sign that the dossier made the models better: relay accepts did not
  rise, and the one dossier that clearly helped (#11) carried a hint that laid out the proof. The analysis
  in this entry was done by Claude (Opus) reading the ledger and the papers, with Andy.
- **Relay rounds open only on news from outside the relay.** A lane's new round needed 5 answered tries
  by others since its last, and relay tries counted, so the relay's own tries kept reopening rounds and
  it never ran out (`tools/relay.py` `NEWS_MODES`: cold, repair, volunteer tries, a person's comment, or
  a new model behind the lane). Cold intake and the nightly retro are unchanged.
- **A lane whose last 6 relay calls were all empty or timed out sits out the relay for 3 days.**
  `openrouter-dots-3-note` timed out (HTTP 504) on 33 of 33 relay calls from 10-11 and
  `openrouter-laguna-s-2-1` on 50 of 54, a few a day, too spread out for the 24-hour failing rule.
  The Mistral lanes timed out on 11 to 30% of calls and mostly answered, so they stay.
- **The stages are renumbered (Andy).** Stage 3 is now stronger provers and plans on free cloud compute;
  stage 4 our own spare machines (kumori task #426); stage 5 is the outside-volunteer design written as
  stage 3 (`STAGE5.md`, its done-line unchanged); then real problems, unsolved mathematics and the
  record, as before (`PLAN.md` §7). Entries above this one that say "stage 3" mean the old one.
- **Stage 3, the bet: a specialized open prover where general free models stalled.** Goedel-Prover-V2
  reports 84.6% (8B) and 88.1% (32B) on miniF2F at pass@32 (arXiv 2508.03613); Kimina-Prover-Distill-8B
  77.9% at pass@32 (its model card). Run on a free cloud GPU (Kaggle, 30 GPU hours a week per its own
  GPU docs, 2026-10-17; GitHub's hosted runners are kept to one benchmark job, because GitHub's Actions
  terms bar a "burden ... disproportionate to the benefits" and llama.cpp's own CI keeps real models off
  them), 32 tries on each open AMC 12, MATH L5 and AIME problem, every answer judged by `tools/check.py`
  as its own try mode. Then, on about 10 problems it misses, a strong model's plain-math plan in the
  dossier and the prover again (Hilbert, arXiv 2509.22819, found the reasoner mattered more than the
  prover). What a solve would show: that a specialized prover does what the general free models did not,
  not that free general models learned; these provers were trained on competition Lean, and no
  decontamination audit against miniF2F was found.
- **The bar, written before the prover's first job: at least 5 first-time solves from the prover lane on
  those open AMC 12, MATH L5 and AIME problems within 7 days of its first job** (50 problems; the
  statement audit below removed none). The comparison: the relay made 2 first-time solves in 2026-10-10..10-16.
  Missing it is a finding too: the leftover problems are past what this prover does at 32 tries, and the
  plans or bigger models are next.
- **The prover lane, as built (`tools/prover.py`, `tools/prover_kernel.py`, `.github/workflows/prover.yml`).**
  Kaggle (account `kumoriai`, Andy's choice, its "personal, non-commercial" clause read first) runs
  Goedel-Prover-V2-8B on GPU T4 x2 under vLLM, 32 samples a problem at temperature 1.0, top-p 0.95, up to 16,000
  tokens, the model card's own prompt, our target file as the statement. The workflow (every 2 h) keeps one batch
  going, downloads a finished one, and judges it here as the sandbox user; a problem stops at its first accept, and
  a failed batch is never re-pushed on its own. Measured by a canary on 2026-10-17: vLLM needs Kaggle's torchaudio
  removed (CUDA 12.8 against vLLM's 13.0); the model loads in 5.6 minutes; 8 samples of `mathd_algebra_478` came
  back in 67 s (108 tokens/s together, 810 to 1,076 tokens each). Known risk, not a reason to move the bar: the
  model was trained on Lean 4.9's mathlib and the judge pins v4.33.1, so a proof can fail on a renamed lemma
  alone; each rejected answer (up to 6 a problem) gets the fixer's name repair and Lean's automation, recorded as
  `fixer+loop` beside the raw `prover` row. The answer's last complete block is judged, never the earlier
  `sorry` sketch the model also writes (the old extractor took the longest block, which was the sketch). **The
  bar's 7 days start at the first batch's push**: batch `20261017T1830` (50 problems, 1,600 samples) was pushed 2026-10-17 18:30 UTC (11:30 PT) by prover run 39058392786, so the bar is graded at 2026-10-24 18:30 UTC.
- **The 88 open statements against miniF2F-v2s: none found false.** v2s (github.com/roozbeh-mohit/miniF2F_v2,
  `datasets/miniF2F_v2s.jsonl`, read 2026-10-17) labels our 244 as its `valid` split, not `test` (243
  shared names). 31 of the 88 are identical to v2s, 14 differ only in form (parentheses, hypothesis names,
  `Real.pi`), and the other 43 were read one by one by a Claude reviewer with numeric checks: 36 say the
  same as the problem, 7 are true but differ from it (`algebra_ineq_nto1onlt2m1on` drops n = 1,
  `amc12a_2019_p12` drops x, y > 0 and still holds, `amc12a_2020_p7` encodes the solution's arithmetic,
  `imo_1962_p2` is the real IMO problem where v2s's informal text is not, `imo_1981_p6` proves only the
  recurrence, `imo_1983_p6` only the inequality, `mathd_numbertheory_227` an abstracted model), none
  vacuous. This is a careful reading, not a proof; the kernel is still the only judge of a solve.

## 2026-10-09

- **The loop's verdict; the ladder back to full (Andy).** As of 2026-10-09 the ablation covered 9,848 of
  10,374 stored cold rejects. Arm A (accepted as written) 44.8%; C (plus the fixer, holes and Lean's
  automation, no model call) 56.1%; C turned 25.1% of rejects (95% CI 24.3 to 26.0). By tier the smallest
  gain most: tiny 6.0% to 30.2%, low 15.2% to 32.1%, frontier 66.6% to 73.1%. Arm D, the strongest free lanes
  asked to prove the steps left open: 0 real steps in about 200 answered asks (the one "proved" step was the
  artifact below). 23 problems got their first accepted proof on 2026-10-08, 17 through the loop (2 of them
  on fresh relay tries). So the free half is worth running on everything, and the model half is not yet
  worth the free pool's quota: the ladder's 30-call test-window cap ends, the retro gives every cold reject
  the free half, and open steps are left for stronger provers (volunteers' agents, stage 3).

- **The first "proved" lemma was our tool's mistake, not a model's step (Andy).** The lemma queue's first
  kernel-accepted step (amc12b_2002_p4, groq-gptoss, row 51257) was `1/2 + 1/3 + 1/7 = 1/42` read in ℕ,
  where every term is 0: `extract_goal` had printed the real-number step without its type. True, accepted,
  useless. `tools/subgoals.py` now prints numeric types (`pp.numericTypes`), so a lemma keeps ℝ or ℕ; the
  row stays public as a transcript and is kept off the site's verified-steps panel. Arm D's honest count as
  of this morning: 0 real steps proved by free models in about 200 answered asks.

## 2026-10-08

- **The loop's ablation, and its free half on every try from now on (Andy).** Stage 1 stored 10,334
  rejected cold tries with their proofs. `--retro` re-runs each with Lean only: B = the fixer (form),
  C = the fixer plus holes and Lean's automation, results in kumori's `sparebrains_ablation`, shown live
  at /loop. B and C post-process the very answers A judged, so the comparison is paired. As of
  2026-10-08 evening, about halfway: B turned about 1% of rejects, C about 28%; by tier the tiny lanes go
  from 6% accepted as written to a projected 39%. Twelve open problems fell to the loop that day
  (among them imo_1959_p1, aime_1997_p9, amc12a_2002_p13, amc12b_2002_p19 and the Mersenne condition),
  every one by Lean's automation on a model's near miss, none yet by a model proving a lemma (the lemma
  queue, arm D, runs at the free pool's pace). The free half is now a nightly job (3:17 PT, 6 slices):
  every cold reject the day added gets it, the ladder's own verdict stays the clean A, and an open problem
  it solves is recorded as a normal solve.

- **The loop, not the hole filler: APOLLO's pipeline on every rejected relay try (Andy, after a
  deep search).** The papers put Lean's hole filling alone at 0.4 to 6 points and the loop at the rest:
  APOLLO's paper reports general-purpose models (o3-mini, o4-mini) going from 3-7% to over 40% on miniF2F
  by taking a failed proof apart and sending only the failing steps back (abstract, checked 2026-10-08). `tools/subgoals.py` does that: the fixer first (form), every step
  Lean rejected becomes `sorry` (the accepted steps stay), one Lean run tries `omega`, `linarith`,
  `nlinarith`, `positivity`, `decide`, `norm_num`, `simp`, `aesop`, `exact?` on every hole, `extract_goal`
  prints each hole still open as a standalone lemma, and the same lane is asked for that lemma alone
  (one retry carrying Lean's error, 4 asks a try at most, counted against `--max-calls`). A proved lemma's
  tactics are spliced into its hole and the whole file is judged again; nothing counts until the kernel
  accepts it. Each lemma ask is its own row (`try_mode relay-subgoal`, verdict `lemma-accept` /
  `lemma-reject`, outside every accept/reject count), and a partial result hands its sketch to the next
  lane. The fixer pass now runs the loop with Lean's automation only (`fixer+loop`, once per near miss).
  Measured as of 2026-10-08, automation only, on the closest misses of 15 open problems: 2 solved
  outright (mathd_numbertheory_435 and 233, both apodex's, each re-checked by `check.py`), 9 taken
  down to 1 to 3 open steps a model would be asked for, 4 too broken to take apart. A demo with a scripted
  model (wrong lemma, then a right one after Lean's error) went through to an accept. The relay's rows
  carry `tools.subgoals`, which is how this repo will measure its own number.
- **Every hand-off carries its run, cost and machine as parseable lines (Andy).** As of 2026-10-08 the
  hand-off asked for model, tool, wall-clock, attempts and tokens, and `tools/volunteer.py` read only
  model and tool onto the row; tokens never reached it. The fixed format now has run lines (model, tool,
  tool_version, effort, mode, tools_used), cost lines (tokens_in/out/total, turns, seconds, check_runs,
  attempts) and opt-in, coarse machine lines (os, arch, cpu, cores, ram_gb, gpu, vram_gb, load,
  local_model_runtime, quant), kept as `- key: value` lines because pipes render as Markdown tables in
  a GitHub comment. The parser keeps only those keys, stores `unknown` as null, reads the old
  `wall-clock` (minutes) and `tokens` names, and puts the result on the ledger row and kumori's
  `sparebrains_attempts.agent_metrics` (JSONB), so time, tokens and hardware against solves can be read
  across agents and models over time. Nothing is posted without the person seeing the exact text and
  typing yes, every post on its own (v1, no approve-ahead).

- **One set of Lean tools for every surface: `tools/lean_tools.py` (Andy).** Four agent volunteers
  (Claude, Codex, Haiku) each solved an open problem on the first check, problems the free models had
  failed 100+ times; the agents could compile, read Lean's error and look up real lemma names, and the
  free models' commonest failure was an invented lemma name. So the tools volunteers use are the tools
  the free models get: `check` (the judge), `names` (real mathlib names closest to a guess),
  `suggest` (`exact?`/`apply?` on every `sorry`), `auto` (Lean's closers on a statement, no model). The
  relay now lists the real names next to every invented one, including names a try in the same run
  just invented. A hosted check bench (`bench.yml`, an issue labelled `bench`) runs the same tools for
  anyone without Lean, 10 checks a person a day, the cap counted in a step that never runs Lean. The
  agent file is now `kumori_agents.md` (so a volunteer saving it never overwrites their own
  `AGENTS.md`, which here only points to it), with tools local, hosted, or copied. `auto` on three
  open problems (numbertheory 296, 353, 150) solved none: Lean's closers alone are not the gap.

- **Stage 2 is a swarm: rounds reopen on news, breadth-first, until each problem is solved or rests
  (Andy).** A lane's three relay tries on a problem are a round. It earns another round when there is
  news since its last try: 5 answered tries by others (another lane, a volunteer's agent), a person's
  comment on the thread, or a different model behind the lane; every round reads everything earlier
  rounds left in the dossier. The relay takes a problem a person just spoke on first, then the one
  with the fewest relay tries (every open problem gets a round before any gets another), then the
  stage-2 order. A problem rests only after 1,000 relay tries since a person last commented (Andy: assume
  nobody ever shows up; the point is models working as a swarm), and a comment wakes it. With no people at all the free pool keeps going until each open problem is solved or
  resting; the only stage-2 solve so far (#11) came from a person's hint, which is why a comment
  always wakes a problem. Person comments are read in their own workflow step, so the step running
  untrusted Lean never holds the GitHub token.
- **The relay is a wide swarm: the 15 strongest live lanes, 45 calls a job.** Measured 2026-10-08: 31
  lanes have hard solves from stage 1, but the relay asked the strongest 5 live ones, and with two of
  those parked a job (minutes of Lean setup) made one call. More distinct models on each problem is
  the point of the swarm; three tries per lane per round is unchanged.
- **Volunteer hand-offs are checked automatically (pulled forward from stage 3).** A hand-off comment
  (`AGENTS.md` format) on a problem thread triggers `volunteer.yml`: only the proof in its ```lean
  block is used, spliced onto the target's exact statement, judged by `tools/check.py` as the sandbox
  user, recorded as `volunteer:<login>` (`try_mode: volunteer`), an accept written to `verified/`, and
  the bot replies with the verdict. Submitting needs a GitHub account (identity, credit, blocking);
  reading needs nothing. `AGENTS.md` gains a loop mode and a line on local models.

- **Stage 2 runs non-stop, and the ladder stops asking a lane where it runs dry (Andy: "fix it so
  we're moving").** Measured 2026-10-08: sparebrains made 464 pool calls in 24 h and 81 were answered.
  The ladder had one lane left owing cells, `openrouter-apodex-1-1-mini`, which ran out of 16,000
  tokens mid-thought on amc12 and MATH L4/L5 (kumori's log: "ran out of tokens mid-thought (16000
  max, 54585ms)"; 119 of its 143 calls that day were empty) while solving 34 primer targets in one
  night. The relay only started after each ladder job, so the solving end ran every few hours with
  1 to 13 calls. Two changes: the relay chains itself after any run that made calls (a run with none,
  every lane gated, does not, so it cannot spin; the cron and the ladder restart it), and the ladder
  skips a lane on a rung where its last 20 calls there were 60% or more empty, for 3 days, while still
  asking it on every other rung (`relay.ladder_dud`). A longer timeout would not help: the lane ran
  out of tokens, not time.

- **The problem threads stay at 5 open, refilled as they are solved (Andy).** The pilot (#7 to #11)
  was to run about a week before Andy decided on more threads. Two days in, no one outside had
  commented (every comment on #7 to #11 was the bot's or Andy's; 1 star, 0 watchers), so waiting
  would show nothing: the gap is that nobody has heard of the repo, not how many threads it has. The
  point of stage 2 in public is the threads themselves: models working each problem in the open,
  with an invitation to join. After every attempt run the issues workflow now tops the open threads
  back up to 5 (`problem_issues.py --refill 5`) from the stage-2 order, skipping any problem that
  already had a thread; a closed thread is never reopened, so no run opens more than 5. Every digest
  that is not a solve ends by inviting a comment, pointing at #11 (a person's hint the next models
  read, and the first stage-2 solve). Threads for all 114 open problems were ruled out: a wall of
  bot issues reads as noise to the first real visitor.

## 2026-10-07

- **Thinking models get 16,000 output tokens in every mode, the ladder included (Andy).** On
  2026-10-06/07 `openrouter-apodex-1-1-mini`, the one live lane still owed ladder cells, hit 120
  empty calls in 24 hours on MATH L4/L5 cells, each logged by the router as "ran out of tokens
  mid-thought (4000 max)". Lanes the router flags `is_reasoning_model` now get `relay.MAX_TOKENS`
  (`attempt.lane_max_tokens`); every row's `request_config.max_tokens` records the budget it
  actually had, so stage-1 results can still be split by budget. Correction to the same evening's
  read: those calls did not close cells. The client reports them as `HTTP 502 : unknown`, without
  the router's "returned no text", so `error_scope` calls them router failures, which never close a
  cell; the cost was the same cells re-asked every job, not cells lost.
- **Thinking models are asked for medium reasoning effort, in every mode.** At 16,000 output tokens
  `apodex-1-1-mini` still ran out mid-thought on 31 of 40 ladder calls (~60 s each) and
  `dots-3-note` after up to 185 s. A bigger budget does not stop a model that thinks until it runs
  out, so kumori's router gained an opt-in `reasoning_effort` (kumori e5df172), sent as each
  provider documents it (read 2026-10-07): OpenRouter's `reasoning: {effort}` object, translated per
  model; Groq's `reasoning_effort`, low/medium/high, on GPT-OSS 20B and 120B only; other providers
  untouched. Lanes flagged `is_reasoning_model` ask for `medium`; each row's
  `request_config.reasoning_effort` and `inference.reasoning_effort_mode` record what was asked and
  what the adapter did, so results split cleanly by condition.
- **Every relay call counts toward a lane's three tries, an empty one included.** Overnight the
  relay asked `mil_c05_s01_ex03` in all 6 runs (29 calls, 3 answers): `dots-3-note` and
  `gptoss-20b` came back empty almost every time (the router: "ran out of tokens mid-thought" at
  16,000, after up to 185 s), those calls are router-scoped, and the old rule counted only answers
  and lane errors, so both stayed "owed" forever and the line never moved. `relay.spent()` now
  counts every call. Same night, at 16,000 tokens `apodex-1-1-mini` answered 9 of 40 ladder calls
  (4 of 45 at 4,000) and proved one; the other 31 still ran out after ~60 s of thinking.
- **The fixer (#3) now repairs form in three passes, with no model** (`tools/fixer.py`): layout, Lean 3
  to Lean 4 (begin/end, commas between tactics, `λ x,`, `assume`, `cases ... with`, lowercase
  namespaces), and invented names, each swapped for the closest real mathlib name from an index built
  out of mathlib's sources on the runner (same final name in another namespace first, then a close
  spelling in the same namespace; never guessed without the index). The kernel judges every repair;
  rows record which passes changed the proof (`fixes`). It reads the dossier's new `form_misses` as
  well as its near misses, runs first on each relay problem, and `fixer_target=all` sweeps every open
  problem. Measured before shipping, 2026-10-07: the `lean3_syntax` label mostly catches Lean 4 syntax
  errors ("unexpected token", a stray `...`), not Lean 3; on 400 such rejects on open problems only 10
  were really Lean 3. The first draft stripped trailing commas everywhere, which would have broken
  Lean 4 lists split over lines; commas now go only when a proof is Lean 3 and the line closes its
  brackets. Still form, so the 61% figure stands; the label name overstates Lean 3.
- **Correction: the #11 hint was drafted with Claude Opus, so the solve is thread-assisted, not
  person-assisted.** Andy posted both thread hints (#11 and #8), but Claude drafted their text, and
  the record called #11 "a person's hint". CONTRIBUTING asks every contributor to disclose AI help;
  the project holds itself to the same line. Everywhere it was called person-assisted it is now
  thread-assisted (`relay+thread`, the label the data always carried) and the site has a correcting
  field note (old notes are never edited). The two posted comments stay as they are (Andy); the
  disclosure lives in this record, the site and the article. From here on a hint names its drafter
  inside the comment itself, so thread help can later be split into person-written and
  AI-drafted. The entry below keeps its words; this one corrects them.
- **Lanes that keep coming back empty get less thinking, and a relay bench (Andy).** Medium effort
  reached the providers (rows record `groq_reasoning_effort` / `openrouter_reasoning_object`) but on
  hard problems most thinking-model calls still came back empty: in relay run 37637898616,
  `dots-3-note` 3 of 3 (211-234 s each), `apodex-1-1-mini` and `openrouter-free` 2 of 3, and
  `gptoss-20b` every time. Two rules, measured from the ledger at the start of each job, so they
  adjust themselves: a thinking model whose last 10 calls were at least 60% empty is asked for `low`
  effort (`relay.running_dry`); a lane whose last 6 relay calls were all empty sits out the relay
  for 3 days after the latest, then is measured again (`relay.relay_benched`). On 2026-10-07 that
  benches `dots-3-note` from the relay and asks it, `gptoss-20b` and `apodex-1-1-mini` for low.
- **Models are classed by what they prove here, not by the router's label (Andy).** The router's
  tier is a size prior (kumori `rebander._capability_tier`: 100B+ frontier, 30B+ high, 13B+ medium,
  6B+ low, one step up for thinking models, weekly on Sunday) because its six-question canary is too
  easy to separate models; a model with no public size stays unrated (16 of 81 lanes, apodex among
  them while it led the board). kumori `utilities/sparebrains_class.py` now measures a class from
  **cold tries only**: the highest rung cleared (at least 50% over at least 3 cold tries) mapped
  AMC 12 and up to frontier, MATH L4 and up to high, L2 and up to medium, mil or L1 to low, primer
  to tiny; unproven under 30 cold answers across 3 rungs. Cold only, because counting repair tries
  (accepted ~6% of the time) read gpt-oss-120b as "medium"; on cold tries it clears MATH L4.
  The sparebrains site shows the measured class everywhere and lists, at `/lanes#disagree`, lanes
  two or more steps from the router's label, for a person. The Sunday rebander fills a blank tier
  from it (a model of unknown size with no tier at all) and never re-tiers anything else: the first
  preview would also have pushed `free` and two `ministral-14b` lanes from low to tiny, out of
  Kumori Chat's low-and-up pool, so the rule is blanks only. Preview of the next Sunday: one move,
  `apodex-1-1-mini` none -> frontier; nine disagreements listed. Math is one skill, and the
  router's tier also steers ordinary chat, so nothing writes the ladder over a size tier.
- **Statements checked by hand before the relay reaches them: every miniF2F problem through
  position 10 of the stage-2 order is true as written.** `mathd_algebra_276` (ab = 10 and
  3a - 8b = -1 force a = 5, b = 2, so ab + b = 12); `mathd_numbertheory_353` (2,009 terms summing
  to 2009 x 3014); `mathd_numbertheory_296` (a cube and a fourth power is a twelfth power, least
  above 1 is 2^12 = 4096); `mathd_numbertheory_435` (k = 1, 2, 3 make a gcd equal to 6n + k, k = 4
  makes gcd(6n + 4, 6n + 2) = 2); `mathd_numbertheory_150` (7 + 30n is prime for n = 0..5, and
  187 = 11 x 17); `mathd_algebra_362` (a^3 = 8, so a = 2, b^3 = 8/27, b = 2/3; b = 0 is ruled out
  because a / b^3 = 27/4 is not 0). Plus `mathd_numbertheory_5` and `mathd_algebra_756`, checked
  2026-10-06. Each was read against its informal source; none needed a misformalization report.
- **The site shows answers, not empty calls (Andy: "error" read as the site being broken).** The
  live box and the last-30 table list accepted and rejected answers only; an empty call reads "no
  answer" with a plain reason wherever it still appears (run pages, transcripts), and the ledger
  keeps every row as before.

## 2026-10-06

- **The stall rule tripped: 5 first-time solves on `minif2f/test` in 2026-09-22..09-28, floor 7.**
  Graded eight days late (issue #1 sat open). Two independent counts agree on 5: the committed
  ledger (first `accept` per target by `ts`, the same in UTC and PT) and the site's Postgres
  figure at `/about#stall`. All five landed on 09-27, all from `openrouter-space-bunny`, two cold
  and three repair (`mathd_numbertheory_99`, `mathd_algebra_452`, `_175`, `_541`, `_314`). The
  baseline recounted from the ledger is 31 first-time solves in 2026-09-05..09-18 PT, not the 30
  written on 09-21; the one-row gap was not chased because no baseline from 30 to 33 moves the
  verdict. After the window: 2 on 09-29, 3 on 09-30, 0 in October to date.
- **Context the rule did not measure: lanes ran out of work as well as out of ideas.** Weekly
  live lanes went 57, 32, 23, 16, 5, 2 (weeks of 08-31 to 10-05) and answered calls 16,278 to 201.
  About 20 lanes finished every cell (1,134 answers = 378 targets x 3 tries); others stopped
  answering mid-pass. Correction to a same-day reading: `attempt_no == 1` does not mark a cell's
  first try in the ledger (`dots-3-note` has 1,134 answers but 266 rows tagged 1), so "first
  tries owed" cannot be counted from that field.
- **Stage 2 starts: the relay.** Models and people build on each other's work. Order is the one
  written 2026-09-21 (cross-lane repair, fixer pass, blocks, per-problem issues), merged into one
  try mode family: `relay` (the dossier of every prior attempt) and `relay+thread` (the dossier
  plus human comments from the problem's issue), each beside `cold` and `repair` on the site.
  **Harness first, on one problem: the top of the stage-2 order**, which is computed, not picked:
  rung, has a kernel-accepted reference (`targets/<set>/reference/`, never in a prompt, so the
  statement is known provable), share of rejects that are near misses, fewest lanes tried. As of
  2026-10-06 that is `mil/mil_c05_s01_ex03` (103 tries, 38 lanes, 46 near misses = 45%). Corrected
  the same day: this entry first named `mil_c05_s02_ex02`, a hand pick by unsolved-goals count
  that the written order ranks third (24 near misses = 25%); the live order is `/targets#open`.
  miniF2F statements are checked against miniF2F-v2's corrections before entering the relay.
- **Cold solving stays on as intake, not paused (Andy).** Each job runs the ladder for newly live
  lanes first, then the relay. Every new lane keeps a clean cold baseline, which the relay's
  numbers are compared against.
- **Per-problem GitHub issues: a pilot of 5, posted by a GitHub App, then Andy decides the rest.**
  Standing exception to "Andy says yes to each public issue", scoped to bot-generated problem
  issues on this repo only: the bot opens, edits and closes those; anything else public still
  needs his yes. The identity is a GitHub App on the kumori-ai org (posts as `<app>[bot]`,
  issues-only permission on this repo, one-hour tokens), not Andy's account and not a machine
  user. Issues stay the surface for people, never the machine queue. The mathlib AI-contribution
  policy (`PLAN.md` §6) was read before the pilot opened (leanprover-community.github.io,
  `contribute/index.md`, "Use of AI", read 2026-10-06): it governs pull requests to mathlib and
  comments in mathlib's own GitHub and Zulip ("Using an LLM when writing comments on GitHub or Zulip
  is not allowed"; AI use disclosed with an `LLM-generated` label; code needs a Lean expert who
  understands it). So the bot writes only on this repository, nothing of ours is ever posted to
  mathlib's spaces by a model, and an upstream pull request stays a human's (`AGENTS.md`).
- **The judge runs candidates with no secret in reach.** Found while planning stage 2: Lean runs
  IO while it elaborates (`#eval`), `tools/check.py` ran it inside the attempt step that holds
  `KUMORI_API_KEY`, and `lean_output` is public at `/attempts/<id>`. Clearing Lean's environment is
  not enough on Linux: a process can read `/proc/<pid>/environ` of any process of its own user.
  So in Actions Lean now runs as a separate user (`tools/judge_sandbox.sh`, `SB_JUDGE_USER`) with
  an allowlisted environment, and the attempt checkout no longer leaves a push token in
  `.git/config` (publish writes it after the loop). Proved by a canary in `check.yml`
  (`tools/judge_isolation_canary.py`): the probe must find a planted secret when Lean runs as the
  job's user, and must not as the judge user. As of 2026-10-06 none of the 7,522 accepted proofs
  in `verified/` contain `#eval`, `getEnv`, `/proc` or `IO.Process`; rejected candidates live only
  in Postgres and have not been searched. It became urgent once human text could reach a prompt.

- **The relay's first day, four runs on `mil_c05_s01_ex03`, 0 accepts: what each run fixed.**
  37520440995: 0 calls, the dossier fetch died on Cloudflare error 1010, which refuses Python's
  default `Python-urllib` agent (requests, curl, Go and Node pass); the relay now names itself.
  37521229581: 5 calls, 1 answer; the router logged "ran out of tokens mid-thought (4000 max)" for
  the other four, so reasoning lanes get 16,000 output tokens in relay mode, and the relay asks for
  only the proof instead of the whole file. 37522262314: 7 calls, 3 answers; a lane the router
  parked for seconds after a reply lost its 2nd and 3rd try, so parks are now waited out (up to
  180 s) and a mid-ask defer retried. 37524420987: 11 calls, 5 answers. `openrouter-dots-3-note`
  timed out at the router's 140 s pinned-call deadline every time; the LiteLLM gateway retry that
  deadline was sized for is gone since 2026-09-21, so it is one attempt, and at ~75 tokens/s a
  16,000-token answer needs ~210 s. Andy approved an opt-in `long_call` (kumori 42d1df8): one
  attempt up to 240 s for `sparebrains.write` keys only, under gunicorn's 300 s, holding at most
  one of 32 request slots because the relay asks one call at a time; every other caller keeps 140 s.
  Still open: `groq-gptoss-20b` runs out of tokens even at 16,000.
- **A layout slip hid a real gap: the fixer pass (#3) starts with it.** Three of the problem's five
  closest misses put the first tactic at one indent and the rest deeper, so Lean stopped at
  "unexpected token" before reading the mathematics, and the site labeled them `unsolved_goals`.
  Proof extraction now aligns that shape (`tools/proof_text.py`, never when the first line opens a
  block), and `--fixer` re-judges stored near misses with no model call, recorded as `try_mode`
  `fixer`, credited to the lane that wrote the proof, `prev_id` its row. Run 37528786885 repaired
  #47356: Lean then followed it to line 14 and stopped on a type mismatch, so the gap was real,
  and the dossier now shows the true complaint. A fixer row is nobody's ladder or relay try.
- **Stage 2 runs on its own.** A second cron (:30 every 2 h, its own concurrency group) takes the
  first problem in the stage-2 order (`/targets.json`) that a live relay lane still has tries on,
  runs the fixer, then the relay, at most 15 calls; the issues workflow follows every attempt run
  with a digest, a refreshed first post and the comment sync. The ladder keeps its :00 cron.
- **The pilot threads are open: #7 to #11**, the top five of the order, posted by `kumori-ai[bot]`.
  Both miniF2F statements in it were checked by hand first (`mathd_numbertheory_5`: a square and
  a cube in ℕ is a sixth power, so ≥10 forces ≥64; `mathd_algebra_756`: a = 5, b = 3, 3^5 = 243).
  Andy decides on threads for the rest after about a week of watching who shows up.

- **The first stage-2 solve: `mathd_algebra_756`, person-assisted (`relay+thread`).** Andy posted a
  hint on its thread (#11): take logs instead of the injectivity lemmas 35 earlier tries invented,
  using `Real.log_rpow`, `Real.log_pos` and `Real.rpow_natCast`. The issues workflow synced it into
  the dossier, and in run 37551253071 all four relay tries read it. `openrouter-dots-3-note`
  (dots-studio/dots-3-note) was accepted on its third try in 148 s of model time, a proof that
  follows the hint step for step (`verified/minif2f/test/mathd_algebra_756/`). Before it: 92 answered
  tries by 34 models, all rejected. kumori-ai[bot] replied on #11 quoting the hint, with every try's
  model and verdict, and closed the issue. What it shows: the whole chain (comment, dossier, relay,
  kernel, thread) works. What it does not: a better rate. It is n = 1, a MATH level 1 problem with a
  known solution, and the hint laid out the proof; it is labeled person-assisted, never "the models
  learned". The model that solved it needed the 240 s long call approved the same evening.

## 2026-09-21

- **The repository moved to `github.com/kumori-ai/sparebrains` (Phase D step 12, done early).**
  Andy: "I want to have as much as I can be in that kumori-ai repo." The gate in `PLAN.md` was a
  verified result, and the ledger holds 253 of 378. Transferred by API after pausing the attempt
  chain and letting run 35620604994 publish. Verified after the move: the `KUMORI_API_KEY` secret,
  all three workflows, the run history and the old-URL redirects all survived (GitHub's transfer
  doc promises secrets and redirects; it is silent on run history, which held). **Never create a
  repository named `tillo13/sparebrains`:** that permanently deletes the redirects. Same day:
  `CONTRIBUTING.md`, the Contributor Covenant and three issue forms (community profile 42% to
  71%), Discussions on, and the org profile README at `kumori-ai/.github`. Dated mentions of the
  old path in this file and `BRAINSTORMS.md` are left as written.
- **A router failure is not an attempt, and may never close a cell.** Measured on the committed
  ledger that day: 4,813 error rows, of which 4,134 were the router's (404 unknown backend, 502
  with no body, 503 gates, network) and 679 were a lane's own (504 did not respond in time, 502
  returned no text). The three-error rule counted them all alike and had closed **407 cells on
  errors alone, with zero answers**; 171 of those sit on targets nobody has solved. Reading the
  same ledger with `ladder.error_scope` leaves 11 closed and reopens 396. The ledger was not
  rewritten: it is the public record, and this only changes how `owed_history` reads it.
- **A lane's own error counts only if the lane was alive.** It must have answered something
  (accept or reject, any target) within 30 minutes of the error (`ALIVE_WINDOW_S`). A dying
  upstream returns "no text" for every target, which says nothing about any one of them.
- **Inside a job:** a lane the router 404s is dropped for that job (its cells stay owed); three
  failures in a row park a lane for 60 s, doubling to 30 min, the same ladder refusals already
  climb. Receipt: run 35481806786, 2026-09-20 03:00-06:15 UTC. One lane's upstream died at
  04:20, the router demoted it at 05:00, and the job sent it 1,702 calls across 377 targets
  (458 x 502, then 1,244 x 404). Days 09-19 and 09-20 PT show 0 first-time solves with 77% and
  69% of attempts being router errors, so those two days measure the plumbing, not the lanes.
- **The stall rule, written before the week it judges (Andy: let them try on their own for a week).**
  From 2026-09-22 to 2026-09-28, fewer than **7** first-time solves on `minif2f/test` means cold
  solving has hit its ceiling and the build-on-work steps start (`PLAN.md`: the measured swarm,
  §11 try modes, §12 the per-problem folder, §14 one issue per problem). Why 7: the clean days
  2026-09-05..09-18 (PT) produced 30 first-time solves on `minif2f/test`, 30 ÷ 14 = 2.1 a day, so
  under one a day for a week is less than half the measured rate and not noise. Order when it trips: cross-lane repair first (a lane
  repairs any lane's near miss, its own try mode), then a fixer pass for form, then proofs in
  blocks (kernel-checked skeletons, each open part its own small target), then the per-problem
  issue for people. Inputs the day this was written: 122 of 123 unsolved tried targets have a
  near miss; 52 of 253 first-time solves came from a repair try (21%); 5,629 of 9,207 rejects on
  unsolved targets were no-proof, invented-name or Lean 3 syntax (61%). The site prints the same
  figures live at `/about#stall`. GitHub issues are the surface for people, never the machine
  queue: the ledger and `sparebrains_attempts` stay the queue.
- **Unknown errors default to 'router'.** A failure nobody has classified must never cost a
  target its try. New lane-side failure shapes get added to `_LANE_ERRORS` when seen.

## 2026-09-02

- **The record is Apache-2.0; Cohere and the NVIDIA trial endpoints leave the caller (evening; Andy: "you
  tell me, what's best practice here?").** Every provider's current terms read clause by clause today.
  - **License: Apache-2.0 at the root**, covering `tools/`, `ledger/`, `verified/`. Receipts: mathlib4,
    google-deepmind/miniF2F, formal-conjectures, equational_theories, erdosproblems, NuminaMath-LEAN,
    Lean-Workbook, OpenR1-Math-220k and SYNTHETIC-1 are Apache-2.0 (STP is MIT); both target sets carry
    Apache-2.0 upstream (`targets/*/LICENSE`); a proof that goes to mathlib has to be Apache-2.0 already.
    The general-ML convention (NVIDIA's four post-training sets CC-BY-4.0, WildChat ODC-BY, Dolly
    CC-BY-SA) was not taken: CC-BY is not a software license and `verified/` is Lean code.
  - **Terms, as read (each at the provider's own URL, 2026-09-02).** Mistral Commercial ToS 3.1: the
    customer owns all Output, Mistral assigns any interest; 3.3 restricts only image outputs; 6(d)(e) bar
    using Output to reverse-engineer. Groq Services Agreement 4.2: the customer retains all IP in Inputs
    and Outputs; Groq may not train on them. OpenRouter ToS §5: output ownership follows the serving
    provider's terms; §3: account-level prompt logging, if on, gives OpenRouter a perpetual commercial
    license (not checked on our account; does not bind the record). GMICloud, serving MiniMax M3 and
    M2.7: a website T&C with no output clause; the MiniMax licenses govern weights and are silent on
    outputs. Novita 10.1: license to Novita only to provide the service. Poolside EULA: no ownership
    clause on output. Google Gemini API terms: we may not use the service to develop competing models;
    Google trains on unpaid traffic; Gemma ToU 3.3: "Google claims no rights in Outputs". OpenMDW 1.1
    (Nemotron Ultra, Lightning, Content Safety, Poolside Laguna): "no restrictions or obligations" on
    outputs. NVIDIA Nemotron Open Model License and Open Model Agreement: no ownership claim on outputs.
    Llama 3.2: a model trained on its outputs must carry "Llama" in its name. gpt-oss, ALLaM,
    North-Mini-Code, dots-3: Apache-2.0; Ling-3.0: MIT.
  - **Cohere leaves** (11 direct lanes plus `cohere/north-mini-code:free`; 56 answers, 2 accepts). Cohere
    Terms of Use: "You may not access the Cohere Solution for … any other benchmarking or competitive
    purposes"; "Content", defined as anything provided through the Cohere API, may not be published or
    distributed. A public scoreboard is a benchmark.
  - **NVIDIA trial endpoints leave** (OpenRouter `nvidia/*:free`, the direct `nvidia` lanes, OpenCode's
    Nemotron free; 8 lanes, 130 answers, 21 accepts). NVIDIA API Trial ToS 1.2: access "for limited trial
    purposes only and without use of the API Service or Generated Content in production"; 4.12: "You will
    not use (or allow others to use) the API Service including Generated Content to develop or improve
    products or services that compete with the API Service." 6.3 makes the output ours, but "allow others"
    cannot be squared with an Apache-2.0 grant, and a loop that runs around the clock is not a trial. The
    same weights sit under OpenMDW or the Nemotron license with no output restriction; if a non-trial free
    host serves them, the lanes come back (`tools/attempt.py`, `public_record_ok`).
  - **Everything else stays**: Mistral (32 lanes), Groq (4), MiniMax via GMICloud (2), Gemma via Google AI
    Studio (2; the compete clause binds this project, not the record), Poolside, Novita, AtlasCloud,
    OpenCode MiMo. Rows already produced by the two departing groups stay where they are, carved out of the
    grant in `README.md`; nothing deleted or moved. Precedent: Alpaca went CC-BY-NC whole over one
    generator's terms; WildChat and NVIDIA's sets keep a permissive license and name the generator per row.
    This record does the latter, with the two groups also removed from the caller because the enforcement
    surface is the account, and the account is the shared kumori router.
  - Vercel AI Gateway (four lanes onboarded 2026-09-02, the same MiniMax, Laguna and Ling weights): read the
    same evening. Vercel's Terms of Service define "Your Content" as what you submit, say nothing about output
    ownership beyond your responsibility for it, carry no benchmark or compete clause, and hand the models
    themselves to "the applicable third-party provider" and its terms. On a Hobby or trial Pro plan Vercel may
    use Your Content for model training and share it with providers (its right, not a restriction on the record);
    `disallowPromptTraining` routes only to non-training providers. Stays, same footing as GMICloud and Novita.
  - Community read (deep-search, 4 threads, two on topic): r/LocalLLaMA 17vbg1f (49 comments) and
    r/MachineLearning 123oovw (32 comments) both land on "enforceable? no; can they ban the account? yes",
    and on companies refusing NC-tainted sets. Neither changes the decision.

- **"How we got here" sits under the ladder, never above it.** Andy: reference kindness_social and
  pilgrims_world "as the baseline for how we started / still track / use the LLMs", after the main
  spot. Matches the 2026-08-31 ordering rule (the engine leads; the apps are provenance). The
  section names kumori.ai as the router, kindness.social as the first steady user and the pool's
  canary (its replies graded into the router's quality catalog), pilgrims.world as the benchmark
  that plays like a game, and prints live numbers from `kumori_llm_daily_caps` and
  `kumori_llm_quality_samples`: calls yesterday, today and ever per app, graded replies, and each
  app's share of today's pool as an equation. Nothing retired; both sites linked.
- **Defect, found by the first ladder job: the client package did not export the new functions.**
  `kumori_api_client/__init__.py` re-exports names explicitly and listed only `sparebrains_attempt`
  and `sparebrains_summary`, so the loop's guarded imports of `sparebrains_heartbeat` and
  `sparebrains_previous` fell through to their stubs: run 33652466778 posted 146 attempts in its
  first 18 minutes and not one heartbeat, and its repair tries in later jobs would have run cold.
  The harness could not see it because it monkeypatched the functions after import. Fix: both names
  exported; the loop now prints a WARNING at start and into the step summary whenever a checkout's
  client lacks a function, so a silent degradation of this kind is loud next time. The running job
  keeps its old checkout; the next chained job has the fix. Also seen in that job's first minutes:
  `openrouter-minimax-m3`, an untiered lane the old floor excluded, at 68 accepts in 137 answers
  across primer, MIL and MATH L2–L3; primer 38 of 60 answered so far, MIL 26 of 65.
- **Beyond the solved problems: the shape of Phase C (evening, `PLAN.md` §7 items 9–15).** Andy's
  thread: the donation line is premature (parked); our lanes will not solve open problems on their
  own; the value is showing the work so a mathematician can pick it up, feed it to their own agent
  and their own brain, and validate what a non-mathematician cannot; ingest others' solved work so
  nothing is reinvented; a registry of where that work lives; a web-and-formal scout via kumori.
  Precedents checked (deep-search): the Equational Theories Project (Tao, 2024; per-problem status,
  issues claimed and merged by PR, amateurs contributing modular pieces, machine results dominant
  but humans finding special cases first, standards fixed early), formal-conjectures (2,615
  statements, about 1,029 open, explicit warning on formalization accuracy), and the Erdős
  problems since October 2025 (GPT-5's "10 solved" were literature finds; about 100 problems moved
  to solved with AI help by February 2026; first credited novel AI solution January 2026;
  erdosproblems.com runs an AI-contributions wiki). Three rules fixed now: a known proof of X never
  enters a prompt for X, and every assisted condition is a labeled try mode; the per-problem folder
  standard is set before the first open problem lands; the scout is link-first and its summaries
  count as nothing. Timing: nothing in Phase C starts before pass one is graded.
- **Repair tries: the second and third try of a cell talk to the checker.** Andy, asked what he
  would want next, "ok do it". A cell's first try is *cold* (the file and nothing else). When it
  was rejected, tries two and three are *repair* tries: the lane is shown its own proof and the
  kernel's output (or told its reply had no code block) and asked to fix it; after an accepted
  try the next try stays cold, so consistency is still measured. What a repair try is told comes
  from the loop's own memory within a job, else from `sparebrains_attempts` through
  `/api/v1/sparebrains/previous`. Rows carry `try_mode` and `prev_id`; the curve draws first
  tries dashed beside all tries once repair rows exist, so the gap is what feedback is worth.
  Built before any second try exists (pass one of the ladder runs every first try first), so the
  first pass stays a clean cold measurement. Harness: only the rejected lane got repair prompts,
  the accepted lane's second try stayed cold, every repair row points at its previous attempt.
- **Receipts for the bottom rungs (targets runs 33646682214 and 33647799296).** Primer: 74 of 74
  statements well-formed, 74 of 74 reference proofs accepted by the kernel (one proof rewritten
  after the first run: `Nat.mul_eq_one.mp` is not a name at mathlib v4.33.1). Mathematics in Lean:
  60 of 60 well-formed, 60 of 60 references accepted. Both sets are in the scheduled ladder.
- **The site explains itself to someone who knows no mathematics.** Andy: "every chart, every
  phrase, every number must be told what it is; assume nobody knows anything about math", then
  "a glossary like kindness_social that tooltips the words". Done the kindness way: 55 plain-language
  entries in one dict, inlined as JSON, a page script underlines each defined phrase the first time
  it appears in any paragraph, list item, heading or table cell and shows the meaning on hover or
  tap, the full list sits at the bottom of the home page with anchors, verb-like words (run, try,
  ask) are not auto-matched. Verified in a headless browser: 192 underlined phrases, 35 distinct
  terms, none inside code, links or the chart, no console errors. The home page also opens with a
  six-step walkthrough and a "Right now" box: the cells each worker is asking about at this moment
  (the loop pulses them on every call), the last six graded answers, and links to the problem file,
  the transcript and the live GitHub Actions log, refreshed every 6 s from `/now.json`.
- **The ladder is the product, and it runs around the clock.** Andy: "I'm down", then "it should
  run 24/7 nonstop … use them all up is fine with me", then the headline on sparebrains.kumori.ai
  is "the chart/graph of who is solving what, with a timeline clock". Built today, receipts below.
  *Rungs are provenance, never our own results* (`tools/ladder.py`): the Natural Number Game
  restated over Mathlib's ℕ (`targets/primer/`, 74 of NNG4's 79 levels, Apache-2.0; the FLT joke
  level and three duplicate statements skipped), Mathematics in Lean chapters 2–6 (`targets/mil/`,
  60 exercises at commit `dd6d752`, Apache-2.0), then miniF2F's 130 `mathd_*` items labelled by the
  MATH dataset's own Level 1–5 (`targets/minif2f/levels.json`: 130 of 130 matched by docstring,
  129 at ratio 1.000; L1 25, L2 25, L3 25, L4 25, L5 30; Hendrycks et al. 2021, MIT), then AMC 12,
  the miniF2F custom items, AIME and IMO by source. *Every primer and MIL rung ships a reference
  proof* the targets workflow must see the kernel ACCEPT, so a rung nobody clears is provably
  clearable. Published sets searched first (deep-search, 9 primary sources): nothing formalized
  exists below olympiad level (FormalMATH, Lean Workbook, NuminaMath-LEAN all start there; GSM8K
  has no Lean form), which is why the bottom rungs are restated from the game and the textbook.
- **The loop, third version: `--ladder`.** Every lane (66, the tier floor is gone and untiered lanes
  are in), every target of every set, three tries per (target, lane) cell, the whole ladder's first
  try before anyone's second, owed cells computed from the git ledger, benched lanes left owed
  rather than recorded as skipped, a wall-clock budget per job, and each job dispatches the next
  (`actions: write`, `gh workflow run`); the two-hourly cron is the backstop. Every row carries its
  rung and, for a reject, a `failure_kind` (`no_fence`, `lean3_syntax`, `unknown_name`,
  `unsolved_goals`, `tactic_failed`, …) so the scoreboard says "syntax", never "cannot add". The
  prompt now shows one complete example file, so a miss on 2 + 2 = 4 is a Lean-4 miss, not a
  format guess. Proven on a stubbed harness (accepting, prose, benched and parked lanes) before
  shipping. Full matrix: 318 targets × 66 lanes × 3 = 62,964 cells; 62,166 owed at first plan.
- **The pool is sparebrains'.** Andy: "sparebrains gets 75% and the others then split. kindness and
  pilgrims can be on drip." Router: `_POOL_CALLER_SHARE_OVERRIDES` gives `sparebrains` 0.75 of
  every shared pool per day and the two sim keys 0.10 each (eval variants capped the same); their
  Mistral pacing cutoffs went to 0.15 and 0.10. The production reserve (15%) and every human key
  are untouched. Crons: pilgrims tick + burn every 2 h (were 2 min this morning), kindness's five
  chat crons every 12 h (were 15–60 min). "Nights" is retired: caps are per UTC day, so the loop
  drains each pool to its cap and parks until midnight.
- **The site leads with the chart, and shows every equation.** Home page: a clock strip from a
  per-job heartbeat (`sparebrains_jobs`; cells done of owed, pace = answered in 24 h ÷ 24, ETA =
  owed ÷ pace, this job's verified / calls) with the equations and their live inputs written out
  beneath, and the list of what the ETA does not model; the survival curve (a lane clears a rung
  at verified ÷ answered ≥ 0.5 over ≥ 3 answered; a point is lanes clearing ÷ lanes asked); the
  leaderboard (highest rung cleared, then verified, then the ratio); the lane-by-rung heatmap
  (verified / answered per cell, shade = ratio, hover = most common kind of miss). Everything is a
  query over `sparebrains_attempts`; nothing hand-entered. Andy: "show your work, verbosely, and
  always with every thing we do" — now a rule in `CLAUDE.md`. Old rows were backfilled with rung
  and failure kind by the same functions the loop uses.
- **Expected shape, on record before the data.** Medium and high lanes near 100% on the primer;
  tiny and low a third to a half, missing on syntax; some frontier reasoning lanes failing 2 + 2
  by not finishing inside the token cap; the strong lanes' knee between MATH Level 3 and AMC;
  IMO empty. Written down so the first full pass can be graded against a prediction.
- **The daytime sims are turned down to minimal; the shared pool is the engine's by night.**
  Andy: "if we need to cut pilgrims and kindness_social down to minimal to open this lane to do
  work, then do it." Needed, by the numbers. Chunks A and B (`PLAN.md` §2) made 70 and 81 calls
  in two runs of 80 and 112 minutes because Mistral, the source of 220 of sweep 1's 241 accepts,
  was parked on the router's daily pacing gate (the pool at 1,127,264 tokens against a 1,000,006
  allowance; sweep 1 itself 595,422 of that) and every other provider was benched. Seven-day
  means from `kumori_llm_daily_caps`: the pilgrims tick engine 992 router calls/day (the largest
  caller: 448/day of openrouter's 1,000 cap, 324 opencode_zen, 172 groq, 29 Mistral) and the
  kindness key 620/day (206 direct + 414 eval-tagged; 101 Mistral, 302 openrouter). The two sims
  together were roughly half the Mistral pool's daily tokens and three quarters of openrouter's
  cap. Cut, both through `cron.yaml` (deployed with `deploy`, commits `2bf7dd9` pilgrims,
  `31e12ae` kindness): pilgrims tick and burn every 30 min, were every 2 (about 7% of
  the firings; the ward lane keeps its own key and cadence, revive makes no LLM calls); kindness's
  five chat-bearing crons (generate-thread, agent-responses, agent-reflect, scrape-topics,
  revisit-old-threads) every 4–6 h, were every 15–60 min (224 firings/day → 22; the non-LLM crons
  untouched). Verified on the pilgrims request log: the 2-minute cadence stops at 14:03 UTC.
  Not blinded: the router's tier ordering reads only `heuristic_v1` canary rows (2026-09-01
  entry), and kindness's live samples feed nothing routing reads. Reverting is one `cron.yaml`
  edit per repo. Left alone: the router's Mistral pacing cutoffs (`_POOL_PACING_CUTOFFS`) and
  the sims' hardcoded per-firing batch sizes; if a night still gates, those are next.
- **The pacing gate's wording is wrong for what it does.** `api_v1_llm_bp.py` answers the
  Tier-0 daily rest with "is gated: its provider pool spent this month's free token budget" and
  a retry-after to the first of next month. The gate that fires is the per-day allowance, which
  resets at 00:00 UTC. The loop parks the provider per run, so nothing broke, but the transcripts
  now say "month" for a one-day rest. kumori cleanup, logged in `PLAN.md` §6; not this repo.
- **Sweep 2 (run 33594952834) cancelled after 46/46 Mistral "returned no text"; root cause is
  the router's fair-share gate, and it was doing its job.** Server log, verbatim: `shared_pool
  'mistral': caller 'eval:sparebrains' spent its share (560/432 of 2880) — refusing …`. The
  router classes any `eval:`-prefixed caller as test traffic with a 15% slice of a provider's
  daily pool; an ordinary caller gets 35%, and 15% of every pool is always held for production.
  Sweep 1 had spent 560 of the 432. Pilgrims and kindness were never at risk: this is the
  protection Andy asked about, already built into the router. Fixes: (1) runs carry the caller
  name `sparebrains` (35% = 1,008 Mistral calls per UTC day); `eval:sparebrains` only for
  throwaway checks; (2) the router answers a spent share with an honest 503 and `retry_after_s`
  to UTC midnight instead of a generic 502 (`api_v1_llm_bp.py`); (3) the loop parks a provider
  for the rest of the run on that 503 and skips its remaining pairs without spending calls;
  (4) `--unattempted` counts a target as swept only once 8 lanes actually answered it; (5) a cap
  of lanes per provider per run (`--max-per-provider`, 8 on the schedule), highest tier first,
  because the 28 Mistral lanes are mostly the same few models under different names and two
  chunks a night must fit in one UTC day's share. Also seen: the two `mistral-large` lanes 403
  on the primary key every call (paid models in the free pool); logged in `PLAN.md` §6.
- **Loop, second version (before the first scheduled run).** Andy: "I want it to work super
  well." Four changes, all in `tools/attempt.py`: bench state re-checked before every attempt
  (cached 30 s) and benched pairs deferred to the back of the queue up to three times, then
  recorded as `skipped` with no call made; consecutive calls interleaved across providers so 28
  Mistral lanes are never walked back to back; a per-provider lock so two workers never hit one
  provider at once; the router's retry-after honored once on a rate limit instead of counting a
  dead attempt. Sweep mode is now a work queue with daemon workers rather than a fixed map.
  Proven on a stubbed harness (benched, mid-run bench, rate limit, prose reply, accept path)
  before shipping; the real proof is the 22:00 run's error count against sweep 1's 479.
- **Sweep 1 closed: 241 verified proofs on 17 of 30 targets, 1,050 attempts, $0.** The
  per-lane number exists now: the best free lanes return about one accepted proof per two
  answered asks on this exam paper (`PLAN.md` §2). Nearly half of attempts were lost to
  lanes benched mid-run; re-checking bench state per attempt moves up to the next loop change.
  The 13 unsolved are the IMO items, late AMC/AIME problems, and a few algebra identities:
  the "not yet" list. Ledger commit `ce7df0e`. 20 of 244 targets verified across all runs.
- **Unsolved means not yet, never never.** Andy: "the ones that'll never be solved — that's
  exactly my challenge and hope here, that we WILL solve them at some point … saving
  thoughts/theories/equations that are close or help others learn from them or iterate on
  them. That's EXACTLY my hope, not a 'never' thing." The planning docs said "honestly
  discarded" (README, TARGETS.md §Tier-1 mechanics, BRAINSTORMS.md §6); that phrase is now
  "honestly recorded as a miss, in full." Mechanically nothing changes: every attempt was
  already kept whole in `sparebrains_attempts`. What changes is the framing on the site and
  in the digest, and the priority of Phase B (Lean's error fed back, more tries, a closeness
  signal so the nearest misses surface first).
- **Runs on the roadmap need no per-run go.** Andy: "why would you need a go from me? of
  course go, that's the whole point." Deploys and outward changes still get the disclosure
  line first.
- **Do them all: the nightly schedule.** Andy: "do them all to see if we can solve all them,
  it's free, and no reason not to." The one constraint is the shared pool's per-provider daily
  caps that pilgrims and kindness lean on by day, so the full pass runs at night: the attempt
  workflow fires at 22:00 and 03:00 Pacific (Actions' timezone cron), each firing a sweep of
  the next 30 targets no sweep has touched (`--unattempted`, alphabetical), lanes from medium
  up, benched lanes skipped, two attempts in flight, cap 1,400 calls. About four nights for
  244. Sweep mode runs (target, lane) pairs in parallel; ladder mode stays sequential because
  its early stop depends on order. First chunk launched by hand: run 33586743955 (30 targets,
  seed 2).
- **Run 3 closed: 4 kernel-verified proofs on 5 sampled targets, 137 attempts, $0.** Three by
  `mistral-devstral` (medium), one by `openrouter-openrouter-free` (low, on its 14th lane).
  Tiny and low tiers: 1 accept in 70 attempts. High and frontier: 0 in 35, but 21 of those 35
  were benched-lane errors on the one unsolved target, so their yield is unmeasured, not zero.
  Numbers and the ledger commit (`045c9b2`, sparebrains-bot, `Generated-by:` trailer) in
  `PLAN.md` §2. Next per §7: the sweep run.
- **The first verified artifact exists.** Run 33582595117, target `amc12_2000_p12` (AMC 12,
  2000, #12), accepted by the kernel from lane `mistral-devstral` (medium tier) after eighteen
  tiny/low lanes failed it. 3.1 s model reply, 6.3 s Lean check, $0. This opens the storefront
  gate in `PLAN.md` §7: the site and the org transfer are no longer blocked.
- **The public site is sparebrains.kumori.ai, served by the kumori app, read-only.** Andy:
  "all this documentation on how it works and what to click must be written on
  sparebrains.kumori.ai so everyone knows everything about it." Pages: overview (totals,
  latest verified proofs, runs), how it works (the full explainer), lanes (verified per 1,000
  calls), targets (cheapest tier that solved each), a page per run, a page per attempt with the
  full transcript. Rendered from `sparebrains_attempts`; aggregates cached 60 s. Extends
  kumori's own `base.html` (nav, theme toggle, fonts, main.css) per Andy: "keep the style css js
  like the current kumori.ai page." Code: `kumori/blueprints/sparebrains_site_bp.py`,
  `kumori/templates/sparebrains/`, `kumori/static/css/sparebrains.css`.
- **Subdomain plumbing.** DNS: CNAME `sparebrains` → `ghs.googlehosted.com` (TTL 600) on
  kumori.ai's GoDaddy zone, written by the new `kumori/utilities/godaddy_utils.py` (creds
  `GODADDY_API_KEY`/`GODADDY_API_SECRET` in kumori-404602 Secret Manager; the API answered 200
  for this account). App Engine domain mapping created, managed certificate pending on DNS.
  A WSGI middleware in kumori `main.py` maps the subdomain onto the blueprint's `/sparebrains`
  prefix so URLs stay clean; the same pages also answer at kumori.ai/sparebrains/.
- **Git keeps the verifiable half, Postgres keeps the whole story.** Failed attempts' transcripts
  live only in the table by design (size); the site is the only place a human reads them.
  Publishing raw model outputs is a provider output-use question; math with no PII is the easy
  case, flagged, not yet read clause by clause.
- **Step 3 shape: the loop is a GitHub job that is one more caller on the kumori router.**
  Shared client vendored via deploy.json `shared_files` like pilgrims; key in the repo secret
  `KUMORI_API_KEY`, which the client reads first. Caller attribution `app_name=eval:sparebrains`.
- **Router key minted for `sparebrains`:** `kumori_api_keys` id 62,
  scopes `llm.chat, llm.read, catalog.read, sparebrains.write`, owner key, tier experiment,
  cap 2000 (telemetry only for owner keys). Plaintext lives only in kumori-404602 Secret Manager
  as `SPAREBRAINS_KUMORI_API_KEY` (same naming as PILGRIMS_/KINDNESS_) and in the repo secret.
- **Lanes are walked by quality tier, Andy's ladder.** The router labels every lane
  tiny/low/medium/high/frontier. `--order asc --stop-on-accept` asks the cheapest brains first
  and stops a target at its first kernel-verified proof, so the ledger records the lowest tier
  that solved it. `--order desc` reverses; without `--stop-on-accept` every lane gets every
  target (the per-lane yield measurement). Both are the same script.
- **Show your work: every attempt's full transcript goes to Postgres.** Table
  `sparebrains_attempts` on the shared instance, owned by `kumori/blueprints/sparebrains_bp.py`,
  written through `POST /api/v1/sparebrains/attempt` (scope `sparebrains.write`), because the
  runner must never reach Cloud SQL directly. Columns include prompt, response, extracted proof,
  the exact file handed to Lean, and Lean's output. Git keeps the compact ledger
  (`ledger/<set>/<run_id>.jsonl`) and every accepted proof whole (`verified/<set>/<target>/<lane>.lean`).
  The DB post is fire-and-forget so a telemetry outage never stops a run.
- **Ledger commits carry the `Generated-by:` trailer** (lanes, verifier, cost $0) per the
  attribution-inversion rule; the workflow commits as `sparebrains-bot`.
- **Hard guards on the loop:** `--max-calls` stop, one progress line per call in the job log,
  1 s pacing between router calls, 180 s per call, 300 s per Lean check, first run watched.

## 2026-09-01 (evening)

- **Nothing runs locally. All cloud.** Arm B (a prover model on the ROG GPU) is dropped and the
  ROG leaves this project entirely. Andy: "I don't want anything to run locally." The local
  prover stays a question for `kumori/code/PLAN_local_llm_lane.md`, not here.
- **The verifier is GitHub Actions on the public repo.** Standard runner for public repos:
  4 vCPU, 16 GB RAM, 14 GB SSD, free minutes with no cap, 20 concurrent jobs, 6 h per job,
  10 GB Actions cache per repo. Private repos on the Free plan get 2 vCPU, 8 GB and 2,000
  min/month. Receipts: docs.github.com runner specs + Actions limits pages, 2026-09-01.
  `leanprover/lean-action` v1.6.0 installs elan and pulls the mathlib olean cache, which comes
  from mathlib's own server, not the Actions cache. Built: `.github/workflows/check.yml`.
- **Attempts are ledger commits, not PRs; the ledger lives in git.** PRs opened by
  `github-actions[bot]` run no workflows until a human approves (changelog 2026-06-11), so a
  bot-opened attempt PR never self-verifies. From 2026-10-01 workflow runs, checks and statuses
  expire on the 90-day retention default (changelog 2026-08-27), so run history is not a ledger.
  Verification happens inside the job; the result is committed. This is
  `tillo13/mr_beast_puzzle_private`'s `daily_sources.yml` shape, which already existed.
- **Public under `tillo13/sparebrains` from day one.** Supersedes "private until the first
  artifact" above. Reason: the runner and minutes table. The transfer to kumori-ai after the
  first verified artifact is unchanged; an org holding one CI hello-world is the storefront trap.
- **"Verified" means, mechanically:** `lake env lean` exits 0, no `declaration uses 'sorry'`,
  and `#print axioms` for every theorem in the file is a subset of
  `{propext, Classical.choice, Quot.sound}` (this catches `sorryAx` and smuggled `axiom`s).
  Implemented in `tools/check.py`; exercised by `checks/accept/*` (must pass) and
  `checks/reject/*` (sorry, a smuggled axiom, a false statement; all must be refused).
  Statement byte-identity to the target is added when targets exist (step 2).
- **Lane one is math: Lean-checked proofs, miniF2F as the calibration floor.** Science and
  space fail `TARGETS.md`'s fit filter (methods you build, not LLM calls); code bounties need
  a human gate; forecasting is verified by reality weeks later and was already out of v1.
  Lean over the counterexample hunt because the artifact is unimpeachable, a target list and
  published baselines exist, and the Actions+mathlib setup is reused by every later math lane.
- **Pins: Lean `v4.33.1`, mathlib `v4.33.1`** (commit `0df444a3`), the same pin
  `google-deepmind/formal-conjectures` carries on 2026-09-01, so its statements load without a
  toolchain bump. `lake-manifest.json` was derived from mathlib's own manifest at that tag.
- **GitHub Models is retired (2026-07-30).** No free LLM exists inside GitHub; the kumori router
  is the only propose side. Three sources: changelog 2026-07-01 and 2026-07-30, docs landing
  page. Four router lanes still point at it (kumori cleanup, logged in `PLAN.md` §6).
- **GitHub Agentic Workflows is an intake tool, not the engine.** Public preview 2026-06-11,
  `github/gh-aw` v0.87.10. Every engine accepts a custom base URL (`ANTHROPIC_BASE_URL` /
  `OPENAI_BASE_URL`), so it can run against code.kumori.ai at $0. Deferred until strangers file
  targets. The propose→check loop is plain Python.
- **Two live kumori API keys were scrubbed from `PLAN.md` §1** before the repo went public.
  They had been pasted as caller labels; `kumori_free_llms.py:235` shows they are keys.
- **Step 1 is green.** `tillo13/sparebrains` run 33577335558: 2 min 47 s end to end, 4.6–7.1 s
  per check with `import Mathlib`, 6.6 GB peak RSS, 6.5 GB mathlib cache, $0. Two accepts
  accepted; a `sorry`, a smuggled `axiom`, and a false statement all refused for the stated
  reasons. Numbers in `PLAN.md` §2. Steps 2–4 remain gated.
- **Step 2 is green: the target set is google-deepmind/miniF2F, Test split, 244 statements.**
  Chosen over yangky11/miniF2F-lean4 (unmaintained, original misformalizations) and
  miniF2F-v2 (jsonl only, no Lean project). All 244 type-check under mathlib v4.33.1 with
  `sorryAx` as the sole hole; zero edits needed. One file per theorem in
  `targets/minif2f/test/`, Apache-2.0 with license and change list in `targets/minif2f/README.md`.
  Valid split excluded: 204 of its statements use `answer(...)` from formal-conjectures.
  `tools/check.py --expect wellformed` is the gate; run 33578810121.
- **The judge reads `sorryAx` from the kernel's axiom audit, never the warning text.** Lean
  v4.33 prints "declaration uses `sorry`" with backticks; a text match on the old quoting let a
  `sorry` proof through on run 33578565414. The reject suite caught it. Now the only sorry
  signal is `#print axioms`.

## 2026-09-01

- **Name: `sparebrains` / `sparebrAIns`.** Machine identifiers lowercase: App Engine and Cloud
  Run require it, PEP 8 expects it, the fleet has zero capitalized project folders, and GitHub
  resolves repo URLs case-insensitively (verified: `TILLO13/KUMORI` → `tillo13/kumori`), so a
  mixed-case repo name would be a permanent paper cut on a case-insensitive APFS volume.
  Stylized form wherever a human reads it. Rejected: sieve, nightshift, idlehands, sparecycles,
  proofhound, crucible, lemming, spareai.
- **Name clearance (deep-search, 2026-09-01).** One US mark ever existed: SPAREBRAINS, serial
  75945170 / reg. 2423507, SLSoftware and Consulting Services LLC, class 9 "information
  management software for computers", registered 2001-01-23, **cancelled 2007-10-27 under
  Section 8** (two sources: Justia, Bizapedia). Exact-string search of Justia's USPTO index
  returns that one record only. Not checked: EUIPO/WIPO, state marks, USPTO directly (its API
  needs a key; its search is JS-only). Common-law users, none in software or AI: Spare Brains
  Games (board-game publisher, BGG 5644), a WordPress placeholder, gaming/art handles, a 2012
  album. Domains: `.com` registered 2023-05, parked for sale (Afternic); `.org` registered
  2023-07, serves nothing; **`.ai` and `.io` unregistered**; `.dev` unknown. GitHub: user
  `sparebrains` and org `Sparebrainss` both created 2017-10, zero repos, dormant; no repo by the
  name anywhere. npm and PyPI names free. Reddit: zero on-topic threads across three harvests.
- **Home = `~/Desktop/code/sparebrains/` on the Mac; its own top-level project.** kumori is the
  private infra hub (`tillo13/kumori`, isPrivate=true); a public repo cannot be a folder inside
  it. pilgrims_world and kindness_social are the pattern: apps on the substrate, each its own
  repo with `cron.yaml` + `deploy.json`, consuming a synced `kumori_api_client`. The ROG holds a
  pointer stub only (`Q:\studio_dev\20260831_ai_for_good_free_lane\PLAN.md`), the same pattern
  as the local-LLM lane. The one piece that belongs INSIDE kumori: the live lane-health
  dashboard route, because only kumori sees pool health.
- **Repo posture: private under tillo13 until the first verified artifact exists, then a
  GitHub transfer to kumori-ai** (transfer keeps history). Git via `deploy --git-only`, never
  raw git. Why: an empty plan-only repo on the public org is the storefront-before-product trap.
- **Milestone 1 is a yield measurement, not the engine.** `PLAN.md` §2. Every downstream
  choice (substrate, turn-down, lane order, org shape) depends on verified-per-1,000-calls,
  which nobody has measured.
- **kindness_social and pilgrims_world stay as they are.** Live 7-day numbers (`PLAN.md` §1):
  pool ≈2,300/day, not 5,400; self-play ≈1,500/day, not 3,600; OpenRouter ≈570 of its 1,000.
  The provider-exhaustion case for a turn-down was built on a pool that no longer exists, and
  the bots are currently the only steady canary traffic. Revisit after the yield gate.
- **quality_judge pre-check: answered.** Router tier ordering reads only
  `judge_kind='heuristic_v1'` canary rows
  (`kumori/shared/kumori_free_llm/kumori_free_llms.py:1618`). kindness (`kindness_live_v1`,
  `kindness_rerank_v1`, `kindness_imgembed_v1`) and pilgrims write into the same
  `kumori_llm_quality_samples` table under their own judge kinds, which the router ignores.
  A turn-down cannot blind routing. (BRAINSTORMS.md §3 assumed kindness never wrote to the
  catalog; wrong in detail, right in conclusion.)
- **Docs moved, not copied.** `plan.md` → `BRAINSTORMS.md` (verbatim), `bounties.md` →
  `TARGETS.md` (verbatim, renamed to the public vocabulary). Byte-exact on arrival
  (34,213 / 12,541), then a provenance header added to each.

## 2026-08-31 (carried from `BRAINSTORMS.md` §16–17)

- **github.com/kumori-ai org exists.** Created 21:54, org id 323345833, free plan, `tillo13`
  admin, 0 repos. The only real-world artifact so far.
  **⚠ Pending Andy click: set the org's Copilot per-user budget to $0** so the free org has
  zero billable surface.
- **GitHub is the product; kumori.ai is the narrative.** Issues = target queue (Issue Forms),
  PRs = attempts, Actions CI = the oracle at PR granularity, README scoreboard regenerated
  nightly, Discussions = the forum, Projects board = state. Landing = org profile README or
  GitHub Pages with `good.kumori.ai` CNAMEd to it. No separate website.
- **Money posture (README sentence, never revisited):** no money flows through the project;
  contributors keep their prizes; anything paid to the org's own accounts is donated to a
  named recipient and logged; the org never funds bounties itself. Recipient: OPEN.
- **Attribution inversion (scoped exception).** The global no-AI-attribution rule stays intact
  for product repos. In THIS repo every engine result or attempt must disclose model / lane /
  method / cost via the ASF `Generated-by:` commit trailer, not `Co-Authored-By`. Written into
  `CLAUDE.md`.
- **Vocabulary:** never "bounty" in public unless money is attached. "Open problems",
  "targets", "scoreboard".
- **Contribution policy:** issues-only for strangers first; PRs later, CI-gated;
  `CONTRIBUTING.md` modeled on the allowed + disclosure-required + human-in-loop cluster
  (Airflow, Arrow, Django, cilium DCO). Lines to steal: curl's "worth more than the review
  time"; Ghostty's "not anti-AI, anti-unqualified".
- **Ordering on the org page:** the engine leads; pilgrims / kindness / kumori.ai appear below
  as provenance, never as the lead.
