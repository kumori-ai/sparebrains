# PLAN — sparebrAIns

**Status 2026-09-02 (evening): the ladder runs around the clock.** Three target sets (primer 74,
Mathematics in Lean 60, miniF2F 244 with MATH levels on the 130 mathd items), every lane, three
tries per cell, jobs chained every two hours; sparebrains holds 75% of every shared pool; the site
leads with the survival curve, the clock and the leaderboard, every equation shown
(`DECISIONS.md` 2026-09-02). Earlier the same day: §2 steps 1–3 built, first verified proof, sweep 1.
Point-in-time: every number here was measured on the day stated; re-derive before acting.

## Immediate follow-up (2026-09-04)

Kumori release receipt: commit `38d4f21`, App Engine `version-36iv8izn02` deployed
2026-09-04 PT. Production `/llm/backends` returned 70 chat endpoints, including the
corrected 21 reasoning endpoints with provenance. One eligible Groq `HELLO` call
returned `openai/gpt-oss-120b`, `finish_reason=stop`, requested 32 / effective 1500
tokens and a 60s adapter ceiling; provider effort remained honestly unreported.
Validation: 20 offline tests, nine read-only SQL contracts, and the deployment gate's
11 rendered pages / 842 live repository links passed. First updated workflow result
and the next daily digest remain the production close-out checks below.

Deployment-tool follow-up: the central GCP deploy automatically removed one older
version (`version-3shfk88uc2`) and image while retaining three versions. Its automatic
cleanup conflicts with the preservation rule; resolve that policy before another
GCP deploy. Source is retained in Git; Sparebrains' git-only publication does not
run this GCP cleanup.

- [x] **Implement reliable ledger publishing (2026-09-04; production verification pending).**
      Run 33881328961 produced 485 calls / 121 accepts, then failed rebasing nine proof files.
      Serialization already existed. Its queued event SHA was older than the ledger at job start;
      this is the likely source of repeated work. The workflow now checks out current `main`,
      uploads only this run's changed ledger/proof recovery artifacts before publication (avoiding
      repeated backups of the whole history), and publishes onto fresh main
      with at most three attempts. Different accepted proofs are preserved under content-addressed
      sibling names; same-run ledger overlaps append only new rows. The next job chains only after
      successful publication. Offline git tests cover stale checkouts, concurrent pushes,
      idempotence, and exhausted retries preserving the source outputs.
- [x] ~~Verify the first deployed publication and next daily digest~~ done as of 2026-09-23: chained publication confirmed on main (kumori task #187).
- [ ] Design a measured proof-search swarm (after the lane baseline): tracked publicly as [#2](https://github.com/kumori-ai/sparebrains/issues/2), cross-lane repair being its first measured form (2026-09-24).
- [ ] Volunteer compute: leftover paid-AI quota, pointed at open problems (issue #6): tracked publicly as [#6](https://github.com/kumori-ai/sparebrains/issues/6) (2026-09-24).
- [ ] Measure reasoning lanes as a separate cohort before swarm routing: moved to the kumori task queue as #190 (project `sparebrains`), 2026-09-23.

## 0. Root

Idle free-tier compute → machine-verified public artifacts. The free pool cannot out-think
frontier models; its only edge is massive cheap parallel generation, which is worth something
ONLY where a mechanical verifier separates right from plausible-wrong. Pool proposes, oracle
disposes, only truth survives. Machinery already owned: the kumori router (multi-model
fan-out), crons + workers (the kindness / pilgrims pattern), web/PDF/image input, GitHub as
the interface.

Two invariants. **Free-lane only:** paid Claude "Reserve" is off limits without explicit
written permission each time (kumori `CLAUDE.md`). **No PII:** the math and fact lanes carry
none; that is part of why they were chosen.

## 1. Live capacity (measured 2026-09-01 from `kumori_llm_daily_caps`, 08-26 → 08-31)

| caller | calls/day |
|---|---|
| pilgrims_world tick engine (its own router key) | 850–1,000 |
| kindness_social direct + eval (its own router key) | 440–680 |
| pool self-checks: llm_canary, quality_judge, admin_health, health_probe | ≈600 |
| galactica | ≈98 |
| **total** | **2,200–2,400** |
| OpenRouter pool, of its 1,000/day cap | ≈570 |

Read: reclaimable self-play ≈1,500/day, not the 3,600 in `BRAINSTORMS.md`. A quarter of the
pool is the pool checking itself. Nothing is saturating. 09-01 itself ran hot (3,944 by
mid-afternoon; mistral 1,723 against a 52/day norm all week; the code cites the 07-12 mistral
org death as why monthly token caps exist). Cause unknown, flagged, not chased.

Consequence: this is a hobby-scale engine. Expectations are set against ~1,500 calls/day of
weak models. That is why the yield gate exists.

## 2. MILESTONE 1 — the yield gate (the only thing that gets built first)

**Question:** verified proofs per 1,000 calls, on the target class we would actually run.
Nobody has this number. Every other decision in this file depends on it. `BRAINSTORMS.md` §6
says the checker makes model weakness free; it makes weakness *safe* (nothing false survives),
not free (a near-zero hit rate spends the whole quota on nothing).

**Shape: a measurement, not the engine.**
- **Targets:** the same 20–50 for both arms. Candidate sources: textbook lemmas absent from
  mathlib; `google-deepmind/formal-conjectures` statements (already in Lean 4); miniF2F-style
  items as a calibration floor. Final list: OPEN (§6).
- **Arm A, free pool:** the kumori router as-is, N attempts per target with Lean error
  feedback between attempts. Caller tagged `eval:sparebrains` so it lands in the existing
  caller-share and quality accounting.
- **Arm B — DROPPED 2026-09-01 (evening), `DECISIONS.md`: nothing runs locally.** Kept for
  the record: local specialized prover on the ROG: a 7–8B Lean-trained prover on the 5060 Ti.
  Candidates from recollection, verify current releases and benchmarks before picking:
  DeepSeek-Prover-V2 7B, Goedel-Prover-V2 8B, Kimina-Prover 8B. Same targets, same attempt
  budget. Runs under the studio's ROG rules: visible window, telemetry sidecar, no timeouts.
- **Verifier:** Lean 4 + mathlib, resident checker (§4). A proof counts only if the kernel
  accepts it with no `sorry` and the statement is byte-identical to the target.
- **Metric:** verified per 1,000 calls per arm; wall time per verified proof; the $0 receipt
  (no paid lane touched). The kernel is the judge; nobody grades proofs by eye.

**Decision table (the outcome gets written into `DECISIONS.md`):**

| outcome | what it decides |
|---|---|
| A clearly > 0 | the free-pool Lean lane is real; build the generate-verify cron on the router |
| A ≈ 0, B > 0 | proof search is a ROG GPU job; the free pool does statements / ensemble / forecast; the local-prover lane merges here (§6) |
| both ≈ 0 on known lemmas | Lean is not lane one; the counterexample hunt with plain checkers (`TARGETS.md` Tier 1) is the next thing to measure |

With Arm B dropped only rows 1 and 3 remain. Step order (2026-09-01 evening): (1) prove the
checker in Actions, (2) the miniF2F Lean 4 target set, pinned to the same mathlib, (3) the
propose→check→ledger loop in the same job, (4) nightly schedule for a week.

**Step 1 measured (run 33577335558, 2026-09-02 00:56 UTC, public-repo `ubuntu-latest`):**

| item | measured |
|---|---|
| whole job | 2 min 47 s |
| elan + mathlib cache (8,690 files, 6.5 GB) + `lake build` | 2 min 17 s |
| one check (`lake env lean` incl. `import Mathlib`) | 4.6–7.1 s |
| peak RSS of one check | 6.6 GB |
| runner | 4 vCPU, 15 GiB RAM, 145 GB disk (75 GB free after mathlib) |
| verdicts | 2 accept, 3 reject, all as expected; `sorryAx` and a smuggled `axiom` both caught |
| cost | $0 |

Read: ~5 s per check means a few hundred attempts per job without a resident Lean server.
The 6.6 GB peak rules out the private-repo 8 GB runner; public was the right call.

**Step 2 measured (run 33578810121, 2026-09-02 01:17 UTC):** `targets/minif2f/test/`, 244
statements from google-deepmind/miniF2F `f0a20e1` (their pin mathlib v4.27.0), all 244
well-formed under mathlib v4.33.1 with `sorryAx` as the only hole. 3.4–3.8 s per statement,
two in parallel, 9 min for the split, 6.6 GB peak. Zero statements needed editing. Valid split
not imported (204 statements use formal-conjectures' `answer(...)`). Also found on the way: the
judge's first version keyed on Lean's `sorry` warning text, which v4.33 quotes differently; it
now reads `sorryAx` from `#print axioms`, and the reject suite is what caught it.

**Step 3 measured (run 33582595117, 2026-09-02 02:18→03:07 UTC, ladder-asc, 5 targets, 66 lanes):**

| item | measured |
|---|---|
| attempts | 137 (58 router errors = benched lanes, 16 replies with no proof, 58 Lean rejects) |
| kernel-verified | 4, on 4 of 5 targets; `mathd_algebra_320` unsolved after all 66 lanes |
| who solved | `mistral-devstral` (medium) ×3; `openrouter-openrouter-free` (low) ×1 |
| by tier, accepts/attempts | tiny 0/10 · low 1/60 · medium 3/24 · high 0/26 · frontier 0/9 · untiered 0/8 |
| per attempt | 21.4 s model call (non-error), 7.5 s Lean check |
| yield | 29 verified per 1,000 attempts; 51 per 1,000 calls that got an answer |
| cost | $0; ledger commit `045c9b2` carries the `Generated-by:` trailer |

Read: the ladder found a solver for 4 of 5 targets inside the medium tier, so high and
frontier lanes were only ever asked the hard one, where 21 of their 35 attempts were router
errors (benched). Per-lane yield for the strong tiers is therefore still unmeasured; that is
what the §7 sweep run is for. Tiny and low produced one accept in 70 attempts.

**Sweep 1 measured (run 33586743955, 2026-09-02 03:23→05:12 UTC, sweep-asc, 30 targets, seed 2,
lanes medium and up, benched skipped at start, 2 in flight, cap 1,400):**

| item | measured |
|---|---|
| attempts | 1,050 (479 router errors = lanes benched mid-run, 12 no proof, 318 Lean rejects) |
| kernel-verified | 241, on 17 of 30 targets |
| by tier, accepts/attempts (errors) | medium 65/240 (59) · high 153/630 (296) · frontier 23/180 (124) |
| top lanes, verified per 1,000 answered | ten Mistral lanes at 500–520; the medium `mistral-devstral` equals the high ones |
| per attempt | 10.3 s model call (non-error); 2 in flight → 1 h 49 min for the chunk |
| unsolved by every lane | `aime_1990_p4`, `aime_1999_p11`, `amc12a_2008_p25`, `amc12a_2021_p12`, `imo_1959_p1`, `imo_1985_p6`, `imo_2001_p6`, `mathd_algebra_215`, `mathd_algebra_293`, `mathd_numbertheory_435`, `mathd_numbertheory_495`, `numbertheory_notequiv2i2jasqbsqdiv8`, `algebra_apbon2pownleqapownpbpowon2` |
| cost | $0; ledger commit `ce7df0e` |

Read: the strong lanes clear the easy contest items broadly (23 of 25 lanes proved
`mathd_numbertheory_517`), and the unsolved list is exactly the shape expected: the IMO items,
the late AMC/AIME problems, and a few algebra identities. Nearly half of all attempts were
lost to benching: high and frontier lanes get benched by the router mid-run (rate limits), so
their answered counts are small. Skipping benched lanes only at the start is not enough;
re-checking bench state per attempt is a Phase B item. Across all runs: 24 of 244 targets
have a kernel-verified proof.

**Chunks A and B measured (loop v2.1; A = run 33596793464, 05:59→07:19 UTC, by hand; B = run
33613500311, 09:21→11:13 UTC, the first scheduled firing; each sweep-asc over the next 30
unswept targets, lanes medium and up, 8 per provider, 2 in flight, cap 1,400):**

| item | A | B |
|---|---|---|
| rows | 600 (70 calls, 530 skipped) | 630 (81 calls, 549 skipped) |
| kernel-verified | 3 | 2 |
| skipped: Mistral parked on the router's daily pacing gate | 213 | 240 |
| skipped: lane benched for the whole run | 283 | 290 |
| accepts / answered | 3 / 64 | 2 / 76 |
| median model call, non-skipped | 44 s | 60 s |
| HTTP 502 retries in the client | 37 | 27 |
| targets newly swept (8 lanes answered) | 4 | 0 |
| cost | $0 | $0 |

Read: the engine was throttled, not failing. Mistral lanes gave 220 of sweep 1's 241 accepts,
and both chunks hit the router's Tier-0 pacing gate on the Mistral pool (about 1M tokens per
UTC day pool-wide, 30M per month): at run time the pool stood at 1,127,264 tokens against a
1,000,006 allowance, 595,422 of it sweep 1's own spend under the old `eval:` tag. The API says
"spent this month's free token budget" with a retry-after to October 1; it is a one-day rest
that ends at 00:00 UTC. The other providers were benched by the router after sweep 1's 479
errors. What answered (the openrouter nemotron and minimax family, three groq gptoss lanes)
returned 5 accepts in 140 answers, on the AIME-heavy alphabetical head of the paper. The swept
counter went 217 → 213 → 213, so B re-walked 26 of A's targets. Daytime sims were the other
half of the pool's Mistral spend and most of openrouter's 1,000/day cap; turned down 2026-09-02
(`DECISIONS.md`).

## 2A. Reasoning cohort (separate test bucket)

**Instrumentation implemented 2026-09-04; first production rows pending.** Kumori's backend API,
runtime selection, and canary now include all three capability flags. Each new Sparebrains ledger
and telemetry row records `capability` (flags and provenance, model slug and identity type),
`request_config` (token limit, temperature, client/router/verifier timeout, effort unrequested),
`returned_backend`, and the router's `inference` evidence (effective token floor, adapter timeout,
returned provider model where available, transport, finish reason, and answer field). Unknown
provider effort stays null with `provider_default_unreported`; older rows are not guessed/backfilled.
Gemini adapters that explicitly disable thinking are labeled accordingly. This records the current
baseline; low/medium/high arms still require provider-specific support validation and a distinct
configuration key before launch. Runtime detection is a signal, not proof that a provider accepts
an effort parameter.

Reasoning-capable lanes get their own readout rather than disappearing inside the general
leaderboard. Use the same targets, prompts, verifier, and three-try budget where possible; the
independent variables are lane capability and any provider-supported effort setting.

Track separately: verified per 1,000 calls and verified/answered by rung; cold versus repair yield;
failure kinds; call and Lean latency; output length; provider errors; and whether a reasoning lane
clears a rung no non-reasoning lane clears. Effort variants (low/medium/high) are separate
configurations when the API exposes them. Require matched target coverage and enough answered tries
per rung before calling a reasoning lane better. Once stable, feed its measured specialties into the
proof-search swarm; keep this cohort separate from the cold baseline.

**Reasoning-lane availability proof (next validation step):** do not treat a 503 benched response
as a dead model and do not hammer it. A small smoke job should first call Kumori's status/eligibility
path, record the provider's reset hint and breaker reason, and send one `HELLO` request only to lanes
currently eligible. For benched lanes, schedule the check after the reported UTC reset or pacing
window (with a bounded retry, not a tight loop). Record one row per lane with registry flags,
eligibility, upstream response, latency, and timestamp; classify outcomes as `answered`, `benched`,
`error`, or `empty`, and keep this availability ledger separate from proof-yield data. Acceptance:
every member of the corrected 21-endpoint inventory has either a successful response, a documented
public-record exclusion, or a time-stamped model/provider/breaker restriction after two reset-aware
validation windows. Invalid-model errors have unknown recovery time; a future probe is not a recovery
promise. Track cohort membership changes instead of holding the live denominator at 21 forever.

## 3. Lanes, and the substrate each one fits

| lane | verifier | substrate | status |
|---|---|---|---|
| Lean proof search on known-but-unformalized results | Lean kernel (perfect) | gated by §2; likely the ROG prover | measure first |
| Autoformalization of *statements* (NL → Lean statement) | type-check + expert review | free pool (a language task; diversity helps) | after §2 |
| Counterexample hunt (one finite object refutes a conjecture) | plain checker / SAT-SMT | free pool or ROG | cheapest Tier-1 entry; second thing to measure |
| Ensemble consensus, disagreement as signal | cross-model + sources (weak) | free pool (its natural shape) | v2 |
| Metaculus FutureEval bot | reality, weeks later | free pool | not v1 (§5) |
| OSS bounties | test suites | free pool drafts → Andy reviews | not v1 (§5) |

The free pool's edge (diversity, breadth, web) fits the language-shaped rows. The proof-search
inner loop is a specialist's job. Twenty weak models agreeing is shared bias, not truth, so
there is no row where the pool is its own judge.

## 4. The verifier at two granularities

- **Resolved 2026-09-01 (evening):** GitHub Actions on the public repo is the checker at both
  granularities until the loop outgrows it. Attempts are ledger commits, not PRs (bot-opened
  PRs get no CI without human approval since 2026-06-11). Original text kept below.
- **Inner loop (thousands per day):** a resident Lean server (REPL or Pantograph-style) with
  mathlib loaded once, on the ROG or a worker. Never one `lake build` per attempt, never one
  Actions job per attempt. Where it lives: OPEN (§6). Lean + mathlib is heavy on RAM and the
  olean cache; the ROG has the RAM, but the GPU is exclusive with renders. A CPU-only Lean
  checker coexists with a render; a prover model does not.
- **Outer gate (per PR):** GitHub Actions on the public repo. Standard-runner minutes are free
  for public repos, and `lake exe cache get` makes a check minutes rather than hours. Green
  check = verified; stranger slop fails without human time. This is what `BRAINSTORMS.md` §16
  meant by "CI is the oracle": correct at PR granularity, wrong for the inner loop.

## 5. Not in v1 (decided, so nobody re-discovers them)

- **Metaculus bot.** Contradicts the root: reality-verified, mild public good, lottery ticket.
  Fine as a later daytime-canary lane. Season rules and whether new bots are still accepted
  for Summer/Fall 2026: unverified.
- **OSS bounties.** Human-gate overhead, first-mergeable-PR race, maintainer hostility.
- **mathlib PRs as the deliverable.** Puts us on the wrong side of our own anti-slop policy;
  mathlib's bottleneck is review, naming and placement, not proof existence. The deliverable
  is the public ledger of kernel-checked proofs plus vibemathed entries; a mathlib PR only
  for the rare one a human judged worth a maintainer's hour. mathlib's AI-contribution
  policy: check before any PR.
- ~~**Turning kindness / pilgrims down.** §1 numbers. Revisit after §2.~~ Done 2026-09-02 after
  the yield gate (`DECISIONS.md`): both sims cut to about 7–10% of their firings.
- **Dashboards, org README, CONTRIBUTING, issue forms, the Pages site.** Storefront. After
  the first verified artifact.
- **Any web code.** GitHub's native features plus one read-only route in kumori cover every
  interaction.

## 6. Open (survives this rewrite)

- [x] ~~The 20–50 targets for §2~~ `targets/minif2f/test/` (244, all well-formed). The loop
      picks a fixed sample; "already in mathlib" does not apply to competition statements.
- [x] ~~Where the resident Lean checker runs~~ GitHub Actions (`DECISIONS.md` 2026-09-01 evening). Was: ROG (CPU-only, coexists with renders) or a Cloud
      Run worker (the pilgrims burn/ward pattern). Needs a real RAM and olean-cache answer.
- [x] ~~Prover model for Arm B~~ moot, Arm B dropped. Was: verify current releases and benchmarks; VRAM fit on 16 GB.
- [x] ~~Local-prover lane merge~~ stays in the local-LLM lane; nothing local here. Was: does it merge into sparebrains or stay in the local-LLM lane
      (`kumori/code/PLAN_local_llm_lane.md`)? Decided by §2's outcome.
- [x] ~~Donation recipient for the money-posture sentence.~~ Parked 2026-09-02 (Andy: "way down the
      line"; nothing sends money to a scoreboard). The sentence stays; a recipient only if money ever appears.
- [x] ~~**Provider output-use terms, then a license on `ledger/` and `verified/`.**~~ Done 2026-09-02:
      Apache-2.0 at the root (`LICENSE`); Cohere and the NVIDIA trial endpoints left the caller; rows they
      already produced are carved out in `README.md`. The clause-by-clause read is the `DECISIONS.md` entry.
- [ ] Success metric v2: verified, upstreamed, scoreboard entries: moved to the kumori task queue as #191 (project `sparebrains`), 2026-09-23.
- [ ] mathlib AI-contribution policy: read it before any public issue or PR flow starts ([#5](https://github.com/kumori-ai/sparebrains/issues/5)); formal-conjectures requires it. Metaculus season rules are covered in TARGETS.md (2026-09-24).
- [x] ~~Copilot budget → $0 on the org (Andy click).~~ Retired 2026-09-02: GitHub removed $0 Copilot
      premium-request budgets for team and enterprise accounts on 2025-12-02 (changelog 2025-09-17). The
      rule is simpler: never subscribe the org to Copilot Business; a free org with public repos has no
      billable surface. Deep-search receipt in the session; Copilot adds nothing this project lacks.
- [ ] Explain the 09-01 mistral spike: 1,723 calls vs a 52/day norm: moved to the kumori task queue as #193 (project `sparebrains`, parked), 2026-09-23.
- [x] kumori Tier-0 daily pacing labels/reset hints fixed in code (2026-09-04): the actual gate
      supplies its reason, so daily pacing reports UTC midnight and exhausted monthly budgets report
      month reset. Existing limits and caller shares stay as configured. Deployment verification pending.
- [x] ~~Router: mistral-large-latest and -large-2512 403 on every call~~ done: both lanes idle in the ledger since 09-03 (kumori task #194).
- [ ] Router: four lanes still point at retired GitHub Models: moved to the kumori task queue as #195 (project `kumori`), 2026-09-23.
- [x] ~~Which Lean 4 port of miniF2F~~ google-deepmind/miniF2F (Apache-2.0, corrected, the
      AlphaProof eval set); yangky11's port is unmaintained and carries the original errors.
- [x] ~~Pick the subdomain: sparebrains. vs spare. vs good.kumori.ai~~ done: sparebrains.kumori.ai is live (DECISIONS.md) (kumori task #196).

## 7. The plan from here (2026-09-02; mirrored on sparebrains.kumori.ai/about)

Four phases, in order. Each step names what it produces and what decides the next one.
Nothing is promised on a date; everything is gated on a measured number.

**Phase A: finish the measurement** — superseded 2026-09-02 by the ladder (every set, every lane,
three tries, 24/7); kept for the record.
1. Close the first ladder run (33582595117) → verified-per-lane on the 5-target sample, here in §2.
2. Sweep run: 30 targets × every lane from medium up, 1 attempt, no early stop → real
   verified-per-1,000-calls per lane. Decides the lane roster.
3. Parallel workers in the loop (2–3 in flight, still paced) → a full 244 pass in one job.
4. The full pass → the calibration number, and which row of §2's decision table applies.
5. Nightly schedule with a call cap (step 4 of §2) → yield over time as lanes come and go.

**Phase B: raise the ceiling, for free**
6. ~~Several tries per lane~~ three tries per cell, done 2026-09-02 (`--ladder`); higher temperature and
   pass@k beyond 3 still open.
7. ~~Lean's error fed back for a second attempt~~ done 2026-09-02 (repair tries, `DECISIONS.md`).
8. ~~Skip lanes the router has already benched~~ done: benched cells stay owed; statement identity by construction.

**Phase C: open problems** (rewritten 2026-09-02 evening; each step gated on the one before)
9. **Grade pass one.** When every cell has its first try (about ten days at the 2026-09-02 pace),
   read the primer row and the MATH-level columns against the prediction on record
   (`DECISIONS.md` 2026-09-02, "Expected shape"). Decides whether tiny/low lanes stay in the roster
   and whether the token cap moves. Nothing below starts before this is written down.
10. **Sources page and reference ingestion.** A page listing where solved work lives (mathlib,
    NuminaMath-LEAN's human proofs, the prover labs' released proof sets, miniF2F-v2 when its
    proofs ship). Every public proof of a problem we hold is re-checked under our mathlib pin and
    stored as that problem's reference: proof the rung is provable, and a misformalization tripwire
    (a published proof that fails under our statement means the statements differ).
11. **The no-contamination line.** A known proof of problem X never enters a prompt for X. What may
    enter, each as a labeled try mode on the chart beside cold and repair: retrieved mathlib lemma
    statements; a few of our own kernel-accepted proofs of *other* problems on the same rung; the
    kernel's error (shipped). The retrieval-assisted mode runs only on cells still owed after cold
    and repair, so the clean measurement stays clean.
12. **The per-problem folder, standard fixed before the first open problem lands** (Tao: "much
    easier to modify a standard early"). Per problem: the statement with its informal source and
    a human audit line (who checked the formalization, when); kernel-accepted proofs and lemmas
    extracted from failed attempts and re-checked standalone; attempts complete except for `sorry`,
    with each remaining goal printed by Lean and ranked by how few and how simple; counterexamples;
    a dead-end catalog generated from the ledger (lemma families and tactics tried, how each
    failed, how often); a prompt pack (statement, best partial, remaining goals, dead ends) for a
    mathematician's own agent. Transcripts linked, never featured.
13. **The scout, in kumori.** Per problem, search the informal literature (arXiv, MathOverflow,
    Zulip, the web) and the formal world (mathlib names via loogle/LeanSearch, Lean repos on GitHub,
    formal-conjectures, the Equational Theories Project) together and write a sourced related-work
    page into the folder. Link-first: only things it fetched, every claim linked, summaries labeled
    machine-written and counted as nothing. "Found in the literature" is a folder status distinct
    from "new proof" (the October 2025 Erdős episode is the cost of blurring them). Runs before any
    lane is asked, so lanes and humans start from the same page.
14. **Second target set: google-deepmind/formal-conjectures**, Erdős subset first, because
    erdosproblems.com already runs an AI-contributions wiki to plug the folders into. One GitHub
    issue per open problem, claimable, with misformalization reports as the first kind of ticket.
15. **License the record.** Read each provider's output-use terms (§6), then Apache-2.0 on
    `ledger/` and `verified/`, and the dataset (model, problem, try, mode, verdict, failure kind,
    transcript, repair pairs) becomes the "for good" artifact others can work off.
The counterexample hunt with plain checkers (§3 lane 3) stays the fallback if Lean yield on open
problems is zero after 13. The human-in-the-loop submission paths (vibemathed.com, erdosproblems.com
forum) apply from 14 on; never an automated mathlib PR (§5).

**Phase D: the public product**
12. ~~Transfer the repo to kumori-ai (history intact)~~ done 2026-09-21 (`DECISIONS.md`).
13. Nightly README scoreboard, CONTRIBUTING (allowed + disclosure + human in loop), issue
    forms, restrict-issue-creation kill switch — the mr_beast_puzzle shape, copied.
14. gh-aw intake triage against code.kumori.ai at $0, once strangers file targets.
15. Site: per-target history, lane trends; subdomain cert (pending); provider output-use
    terms before failure transcripts are treated as permanent public content.

Open questions stay in §6. Follow along: the site overview, the repo's commit feed
(`/commits/main.atom`), and `DECISIONS.md` for any change of plan.
