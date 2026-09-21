# DECISIONS — the settled ledger

Dated, with receipts. Re-open one only with new evidence; otherwise it stands.
Everything NOT here is open and lives in `PLAN.md` §6.

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
