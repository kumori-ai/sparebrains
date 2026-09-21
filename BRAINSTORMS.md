> **Moved 2026-09-01** from `Q:\studio_dev\20260831_ai_for_good_free_lane\plan.md` (ROG) to
> `~/Desktop/code/sparebrains/BRAINSTORMS.md` (Mac, the canon). Kept verbatim as provenance: the
> three-session braindump this project came out of. Point-in-time: its capacity numbers (5,400/day,
> 3,600 reclaimable) were superseded by the live figures in `PLAN.md` §1 on 2026-09-01. What survived
> is in `DECISIONS.md`; the gated plan is `PLAN.md`. `bounties.md` referenced below is now `TARGETS.md`.

# AI-for-Good on the Kumori Free Lane — thinking doc

**Created:** 2026-08-31
**Status:** THINKING / not decided. Nothing to build yet. This is a braindump to revisit.
**Origin:** A late-night thread that started with Andy reading a Reddit post and saying
"we are making taco videos" — wanting the studio's AI muscle pointed at something that
helps humanity instead of just content.

---

## 0. How we got here (the through-line)

1. Andy read r/DecidingToBeBetter post "Need to fully get rid of using AI as someone so
   against it" (a hypocrite-guilt post: hates AI, still uses it twice a month). Felt the
   gap between that and "we are making taco videos."
2. We scraped that thread + hunted similar ones. The genre is huge. The *good* side:
   - **Medicine**: the 17-doctors / ChatGPT-diagnosis stories (r/ChatGPT 1lrmom4 — scraped
     in full, 1000+ comments, saved at
     `C:\local\_claude_skills\deep_search\links\1lrmom4\thread.txt`). Recurring pattern:
     people (disproportionately women) dismissed for years, helped not because AI was
     brilliant but because it *listened to the full history with no ego*.
   - **Accessibility**: r/Blind + Be My Eyes / Be My AI — the most wholesome corner.
   - **The canonical lament**: Joanna Maciejewska's "I want AI to do my laundry and dishes
     so I can do art and writing, not AI doing my art and writing so I can do laundry."
3. Andy's real question evolved across the night:
   - first: shift kindness_social / pilgrims_world toward AI-for-good?
   - then: no — reuse the **kumori free LLM lanes** to better humanity.
   - then: not personal-help — **fact-based / science / laws / math** type things.
4. This doc captures all of it so we can think it through later, cold.

---

## 1. THE ASSET (what we actually have)

Not the studio's video stack. The thing that matters here is the **kumori free-LLM
gateway** (`Z:\kumori\shared\kumori_free_llm\`): an orchestrated pool of 60+ free-tier LLM
backends across providers (OpenRouter, groq, cerebras, gemini, mistral, together,
openrouter, deepseek, grok, ...), with:
- lifecycle management (health, promotion/demotion, revival) — `docs/LIFECYCLE.md`
- capacity allocation (per-key caps, tiers, headroom band, burst ceilings) — `docs/CAPACITY.md`
- a router every project just *consumes* (`utilities/kumori_api_client`)

**Envelope (what free-tier realistically means):**
- Modest volume — **thousands of calls/day, not millions.** => high-value-per-call, not mass market.
- Bursty / unreliable — lanes die and revive (that's why LIFECYCLE.md exists). => **async-tolerant** work only, never life-safety realtime.
- Near-zero marginal cost. Multilingual. Already wired for web search + PDF + image input (via kumori).
- Batchable — the whole stack already runs on crons + workers.
- **Paid Claude ("Reserve" tier) is OFF LIMITS** without explicit written permission each time. The free arm pays for NOTHING. This is a hard, non-negotiable cost invariant in kumori's CLAUDE.md. Any AI-for-good build here is FREE-LANE ONLY.

---

## 2. THE CAPACITY FINDING (the punchline that reframes everything)

From `Z:\kumori\shared\kumori_free_llm\docs\CAPACITY.md` (measured, 2026-08-21):

Current run-rate ≈ **5,400 LLM calls/day** across the whole pool. Who spends them:

| caller | ~calls/day |
|---|---|
| kindness_social EVAL (bots grading bots' kindness) | ~2,110 |
| pilgrims_world world-tick (god-sim) | ~1,510 |
| quality_judge + rest | the balance |
| **kumori — the ONLY human-facing consumer** | **~5** |

**=> The substrate capable of real good spends 99.9% of its capacity on bots talking to
bots.** That IS the taco-video feeling, one layer down. "AI for good with the free lane"
isn't invention — it's **redirecting capacity we already own and already pay for (in free
quota) away from self-play and toward something real.**

Important nuance (why turn-down is/ isn't needed):
- The capacity system ALREADY protects a human consumer: production tier uncapped,
  non-prod capped at 85% of a pool, 15% never-allocatable. So kumori / a for-good surface
  (production tier) CANNOT be starved by the bots today.
- The real reason to turn the bots down is **upstream provider quota.** The bots burn the
  actual free daily allotment of each provider (doc shows OpenRouter hitting 992/1000 by
  08:00). Once a provider's free tier is spent, the internal headroom band can't conjure it
  back — it's gone for everyone that day. Fewer bot calls also = fewer lane exhaustions =
  fewer demotions/retirements churning the catalog = healthier pool for the human calls now.

---

## 3. TURN-DOWN PROPOSAL (kindness + pilgrims → minimal)

Status: PROPOSED, not done. Reversible one-line cron.yaml edits in two projects. Deploy is
a separate ask (both projects' rules: ask before deploying).

Between them the two burn ~3,600 of the 5,400/day. Turn *down*, don't kill (both have
standalone value; killing mid-run strands living pilgrims worlds + half-finished kindness
reflection cycles). Down ~6x => reclaim ~3,000 calls/day.

Current cadences read from the two `cron.yaml`:

**pilgrims_world** (`Z:\pilgrims_world\cron.yaml`):
| cron | now | → minimal |
|---|---|---|
| tick | every 2 min | 20 min |
| burn (kicks off-site worker) | every 2 min | 20 min (or pause) |
| revive | every 20 min | 60 min |
| ward (kumori's own testbed, "cadence IS the design") | every 10 min | keep |

**kindness_social** (`Z:\kindness_social\cron.yaml`):
| cron | now | → minimal |
|---|---|---|
| agent-responses (biggest — 1-4 agents + per-comment eval) | every 15 min | 2 hr |
| generate-thread | every 45 min | 6 hr |
| agent-reflect | every 30 min | 4 hr |
| scrape-topics (uses Grok) | every 60 min | 6 hr |
| revisit-old-threads | every 60 min | off / low `revisit_intensity` |
| hourly-metrics, snapshot-agents, janitor (DB-only, no LLM) | — | leave alone |

Two things to confirm before committing:
1. In-flight state: slowing is safe (they just advance slower); don't kill mid-run.
2. Quality signal: the pool's quality catalog (`quality_when_works`, used by ALL consumers
   to pick good backends) is fed by a SEPARATE `quality_judge` probe caller, NOT kindness's
   evaluator — so turning kindness down should NOT blind the catalog. Verify (~30s) before leaning on it.

Sequencing: do it NOW, before any for-good surface exists — the lane-churn + provider-
exhaustion relief is real immediately, and it's the point regardless.

**THE REFRAME (see §6): don't turn self-play OFF, turn it TOWARD truth.** The reclaimed
~3,600/day could instead feed a proof-search engine. Same volume, same crons, same router.

---

## 4. AI-FOR-GOOD LANDSCAPE (what people actually talk about)

Ranked by real discussion volume, each with free-lane fit. (Keyless web/Reddit searches
were SEO-polluted + throttled, but signal was consistent across the night.)

1. **Medical self-advocacy / "decode my results"** — loudest by far (the 1lrmom4 genre,
   melanoma-from-a-photo, 5-yr jaw fix). *Fit: strong async/multilingual, but liability-
   heavy — only ok as "understand + prep for your doctor," never advice.*
2. **"Someone to talk to" / mental-health companionship** — huge quiet demand (therapy too
   expensive). *Fit: trivial to build, ETHICALLY THE HARDEST — crisis, dependency, the exact
   failure mode safety teams fear. Avoid as lane-one unless taking real duty-of-care.*
3. **Accessibility** (Be My Eyes / r/Blind). *Fit: excellent — kumori has image input.
   Least-contested good on the list.*
4. **Bureaucracy & paperwork navigation** — benefits, immigration, legal aid, appeal
   letters, medical-bill fights; govts shipping portals (BenefitsCal, MyBenefits). *Fit:
   BEST match for free/async/multilingual. "The document you're scared of" wedge.*
5. **Tutoring for the under-resourced** — big institutional push (Khanmigo). *Fit: good but
   crowded + minor-safety.*
6. **Elder anti-scam / misinformation check** — rising. *Fit: good (free web search in stack).*
7. **Institutional "AI for Good"** (ITU summit, climate models, food-crisis forecasting,
   nonprofit ops). Most talked about in press. *Fit: mostly POOR — forecasting/ML or org-
   productivity, not chat-LLM shaped.*

**Counterweight to read:** WIRED "AI for Good Is Often Bad" (McKinsey scan of 160 cases;
critique = solutionism / extractive pilots on vulnerable people / PR). Antidote: Josh
Tyrangiel's book "AI for Good: How Real People Are Using AI to Fix Things That Matter."
Lesson: pick a REAL, SPECIFIC, EXPRESSED need; human in the loop; don't experiment on
people who can't opt out. => privacy-first, "understand + route to a human, never advice."

The "personal help" wedge if we go that way: **#4 paperwork navigation.** Reuses whole
kumori stack (chat + PDF + image + web fetch + router + kindness evaluator for tone).
Privacy/redaction layer must be line one, not last (people paste SSN/diagnosis/immigration
status into free 3rd-party providers who may train on it — the exact `mr_noodle_shoes`
warning from the Reddit thread).

---

## 5. THE FACT-BASED PIVOT (where Andy landed — science / laws / math)

More honest instinct: fact-based domains have GROUND TRUTH, sidestepping most of the
"AI-for-good-is-often-bad" trap.

### The one reframe that makes it real (not fantasy)
A free LLM pool **cannot "solve science" by knowing answers** — free-tier models
hallucinate + are individually weak; 20 agreeing = shared bias. "Ask the pool hard
questions and trust it" is the trap.

The pool's ONLY superpower: **massive, diverse, parallel generation.** That becomes
knowledge ONLY when paired with a **VERIFIER / ORACLE** that separates correct from
plausible-but-wrong. Pool proposes; oracle disposes; only truth survives. This is the
**generate-and-verify** paradigm — exactly how the systems that made GENUINE math
contributions work.

### Domains ranked by how good/cheap the oracle is
| domain | oracle | quality |
|---|---|---|
| **Math (formal)** | proof assistant (Lean + mathlib) — proof type-checks or it doesn't | **PERFECT.** No hallucination survives the kernel; doesn't matter how weak the proposing model is. |
| Algorithms / code | tests, property checks, benchmark scores | near-perfect (FunSearch's domain) |
| Logic / constraints | SAT/SMT solver | perfect |
| Facts / claims | citations, ground-truth datasets, cross-source consensus | WEAK — good for flagging uncertainty, bad for discovery |
| Laws (legal) | statute/case-law text (retrievable) | ground truth exists but *application* is contested — treat like facts, cite-only, never assert |

**Conclusion: MATH is where a free LLM pool can genuinely contribute** — the oracle is
perfect, output is trustworthy regardless of model weakness (Lean's kernel doesn't care who
proposed the proof), and it's a real community good (mathlib is human-labor-bound: far more
known math than anyone has formalized).

---

## 6. CANDIDATE BUILDS (fact-based)

**Primary — Lean autoformalization + proof-search engine.**
Pool grinds the backlog of ALREADY-KNOWN theorems (textbook results, published-paper
lemmas, mathlib wishlist) into machine-verified Lean proofs. Throw thousands of cheap
attempts per target; Lean keeps only what verifies; rest discarded honestly. Real prior
art (all 2025-26): AlphaProof, DeepSeek-Prover, Autoformalizer projects, ProofJudge,
arXiv 2605.22763 ("a basic agent alternating LLM generation with Lean verification
replicated the Erdős successes").

**Secondary — FunSearch-style engine** for open combinatorial/algorithmic problems where
the oracle is a scoring function. The paradigm that has found genuinely NEW results (cap-set
problem). Pool proposes programs, evaluator scores, keep winners.

**Tertiary — ensemble-consensus fact engine** (honest = verification, NOT discovery):
"here's what 20 diverse models say, where they split, calibrated confidence, sources."
Disagreement as SIGNAL, not noise. Prior art found: `dissenter` PyPI pkg (multi-LLM debate,
routes across providers — reimplements what kumori's router already does), MUSE calibrated-
ensemble, "Why AI Models Disagree." Good vs misinformation; weak as "discovery."

### Reality check (no snake oil)
- Free-tier models are WEAKER than the specialized frontier provers in those papers. So the
  realistic niche is NOT cracking open conjectures — it's the **VOLUME end**: autoformalizing
  the huge backlog of known-but-not-formalized results, where "many cheap attempts + a
  perfect checker" genuinely beats "one expensive expert" (the checker makes model weakness
  FREE). Achievable + citable (verified proofs are publishable artifacts). Not a Fields Medal.
- The actual WORK is the **Lean-sandbox integration + generate-verify loop**, not the prompting.

---

## 7. WHY IT FITS US + THE PUNCHLINE

- kumori's router already does the multi-model fan-out (`dissenter` reimplements it).
- Everything already runs on crons + workers.
- System = free router (propose) + Lean sandbox (verify) + problem queue (existing cron pattern).
- **PUNCHLINE:** don't turn the self-play OFF, turn it TOWARD truth. The ~3,600 calls/day
  reclaimed from kindness + pilgrims feed the proof engine instead of going idle. Same
  volume, same crons, same pool — but now every call either produces a **Lean-verified
  proof** or is honestly rejected by a mathematical kernel. Nothing false survives. That is
  literally the most fact-based, for-good thing a free LLM pool can physically do: convert
  cheap parallel guessing into machine-checked truth.

---

## 8. OPEN QUESTIONS / DECIDE LATER

- [ ] Personal-help (#4 paperwork) vs fact-based (math/Lean)? Andy is leaning fact-based.
      They're not mutually exclusive but pick ONE wedge first.
- [ ] For math: pure autoformalization (volume, known theorems) vs FunSearch-style (open
      problems, riskier, higher ceiling)? Start with autoformalization = safer, provably
      useful, honest.
- [ ] Turn kindness + pilgrims down NOW (independent of what replaces the capacity) or
      couple it to the proof engine going live? Leaning: turn down now (relief is immediate).
- [ ] Confirm quality_judge (not kindness eval) feeds the quality catalog before turning
      kindness down.
- [ ] Where does the proof engine live? New surface in kumori? New sibling project under
      the same free-llm shared substrate? (Follows kindness/pilgrims pattern.)
- [ ] Lean sandbox: where does it run? Lean+mathlib is heavy. Cloud Run worker (like
      pilgrims' burn/ward lanes already do)? Local ROG box? Needs a real compute answer.
- [ ] Problem-target queue: where do the "theorems to formalize" come from? mathlib
      wishlist? A textbook corpus? arXiv lemma extraction (itself an LLM job)?
- [ ] What's "success"? A count of net-new verified Lean proofs contributed? PRs to mathlib?
      Just a running public dashboard of "N machine-verified truths produced from free
      compute this week"?
- [ ] Privacy/redaction only matters for the personal-help lane; fact-based math has no PII —
      another point in favor of the math lane being cleaner.

---

## 9. REFERENCES (real, current 2026 — collected this session)

Generate-and-verify / formal math:
- arXiv 2605.22763 — "Advancing Mathematics Research with AI-Driven Formal Proof Search"
  (LLM-gen + Lean-verify replicated Erdős successes)
- AlphaProof (aiwiki), DeepSeek-Prover, DeepSeekMath-V2
- arXiv 1910.09336 — "The Lean mathematical library" (mathlib)
- arXiv 2608.20432 — "ProofJudge: Tool-Grounded LLM Evaluation of Formal Proof Quality in Mathlib"
- Autoformalizer writeup: ewoodbury.com/posts/2025-09-27_lean_autoformalizer
- FunSearch (DeepMind) — LLM-proposes-programs + evaluator (cap-set problem, new results)

Ensemble / disagreement-as-signal:
- `dissenter` (PyPI/GitHub PR0CK0) — multi-LLM debate, routes across providers, surfaces disagreement
- MUSE — "Information-Theoretic Approach to Multi-LLM Uncertainty" (PMC12702469)
- "Why AI Models Disagree (And What It Tells You)" — multiple.chat
- SAFE (ICLR 2026) — Generate-Verify-Ensemble at token level
- "Adaptive Consensus in LLM Ensembles via Sequential Evidence" (emergentmind 2605.04236)

AI-for-good landscape / counterweight:
- WIRED — "AI for Good Is Often Bad" (the critique to internalize)
- Josh Tyrangiel — "AI for Good: How Real People Are Using AI to Fix Things That Matter" (book)
- ITU "AI for Good" platform (institutional)

Source threads (scraped, saved locally):
- r/DecidingToBeBetter origin post: `C:\local\_claude_skills\deep_search\links\2Yyq8hfTcx\thread.txt`
- r/ChatGPT 1lrmom4 (10-yr problem, 1000+ comments): `C:\local\_claude_skills\deep_search\links\1lrmom4\thread.txt`

---

## 10. KEY FILES TO RE-READ WHEN PICKING THIS BACK UP

- `Z:\kumori\shared\kumori_free_llm\docs\CAPACITY.md` — the allocation model + the 5,400/day numbers
- `Z:\kumori\shared\kumori_free_llm\docs\LIFECYCLE.md` — lane health / revival
- `Z:\kumori\CLAUDE.md` — the FREE-ARM HARD INVARIANT (never touch paid Reserve)
- `Z:\kindness_social\core\evaluator.py` — the reusable LLM seam + eval pattern
- `Z:\kindness_social\cron.yaml` + `Z:\pilgrims_world\cron.yaml` — the turn-down targets
- `Z:\pilgrims_world\README.md` — note it already self-describes as a "cross-project
  benchmark harness for free-tier LLMs" — the proof engine is a natural sibling to it.

---

# ADDENDUM — 2026-08-31 afternoon session (bounties + the canary reframe)

**Status:** still THINKING, but Andy likes this direction ("I kinda like this idea").
Separate from the local-LLM-lane work (`Q:\studio_dev\20260831_local_llm_lane\`) — keep them so.
**Companion file:** `bounties.md` (this folder) — the verbose site-by-site bounty catalog
(links, why, how we'd help, fit grades, first moves). §12 below is the summary; bounties.md
is the reference.

## 11. THE CANARY REFRAME (the new idea this session)

Kindness + pilgrims currently serve one *real* function for the pool: steady daily traffic
that exercises lanes. Andy's reframe: **replace self-play traffic with bounty/verified-output
traffic** — the pool still gets exercised (a canary only needs regular, diverse volume), but
every call's output accumulates OUTSIDE the stack instead of evaporating inside it.

Also noted: "kumori is just me right now" — the capacity system's human-consumer protection
is moot as user-protection today. The **provider-quota argument still stands** (bounty
grinding burns the same free daily allotments; turn-down of self-play frees exactly that).

Nuances recorded:
- kindness/pilgrims load is predictable + self-paced; bounty traffic is bursty + externally
  scheduled. Health machinery wants *some* regular per-lane traffic — forecasting rounds +
  a nightly proof cron would provide it, but check cadence coverage.
- The `quality_judge` verification (§3 pre-check) is REQUIRED regardless — that's what feeds
  the quality catalog, not raw traffic volume.
- Pressure-tests Andy accepted: (1) taco videos aren't the sin — studio burns GPU render
  cycles, not one LLM call; guilt attaches only to the self-play tier. (2) Free tier is a
  faucet on someone else's meter, and small vs Astra-class labs — expectations stay at the
  volume-autoformalization niche, not conjecture-cracking. (3) The bots do a job (lane
  exercise) — verify before defunding.

## 12. BOUNTY LANDSCAPE (verified 2026-08-31, deep-search — Reddit thin on this slice)

Ranked by verifier quality + fit for "free lanes plug away a bit every day":

1. **Metaculus AI Forecasting Benchmark / FutureEval bot tournaments** — bot-only,
   no-human-in-loop, **$50,000/season**, bi-weekly rounds; Spring 2026 ran, Summer 2026 live
   (metaculus.com/aib/2026/spring · metaculus.com/tournament/spring-aib-2026 · EA Forum
   announcement Dec 2025 · quantchallenges.com listings). **Best cadence match for the canary
   role**, and the method that works — multi-model ensemble, disagreement-as-signal — IS this
   doc's §6 tertiary build. The router is already a forecasting-bot substrate. Caveats:
   verifier = reality (weeks feedback); well-funded bot competition → prize $ is a lottery
   ticket, canary traffic is the dependable return.
2. **Math/Lean lane** (§5–6, unchanged, deepest fit) — new 2026 receipts: erdosproblems.com
   now 1,217 problems / 570 solved, active AI-solve wave (problem 90 by an OpenAI internal
   model May 2026; Astra solved 183/146/180 with Lean 4 certificates Aug 2026 —
   github.com/openai/ten-proofs); **google-deepmind/formal-conjectures** = open conjectures
   already STATED in Lean 4 (a pre-built target queue); evand/open-math-problems tier list
   (Lean links + Manifold markets; July 2026 Jacobian-conjecture counterexample by
   Alpöge + Claude). Erdős cash tradition real (Graham → Fan Chung, Quanta 2017; Collatz $500).
   Money symbolic; durable payoff = public verified artifacts (mathlib PRs / dashboard).
3. **AIMO Progress Prize 3** — live on Kaggle, **$2M+** (aimoprize.com). Wrong shape for the
   pool: offline Kaggle model-submission competition → "Andy competes with his skills +
   hardware," not "lanes grind daily."
4. **OSS bounties** — Algora.io + curated paid-issue lists (GITHUB_PAID_ISSUES.md upd.
   2026-03), test suites as oracle, real money. HARD GATE: first-mergeable-PR race +
   maintainer hostility to AI-slop PRs (curl's ban is the emblem). Only viable as
   lanes-draft-overnight → **Andy reviews and submits**. Never autonomous — an unreviewed
   PR firehose is the opposite of helping.
5. **Anti-fits:** Vesuvius Challenge ($1.84M awarded; $1M grand + $2M bounties live July
   2026), ARC Prize 2026 ($2M), DrivenData ($5M+ lifetime) — engineering competitions, not
   pool-grinding. Zooniverse (1B classifications Aug 2026) — human judgment. Security bug
   bounties — no (authorization + slop). **SETI@home** (the 1999 screensaver) — hibernating
   since Mar 2020; successors (BOINC/Einstein@home/Folding@home/World Community Grid cancer
   projects) are **GPU-cycle donation**, a separate lever from the LLM pool (5060 Ti idle
   cycles could run it, contends with renders).

## 13. UPDATED WEDGE RANKING

- **Nearest-term:** a Metaculus FutureEval bot — cheap to stand up on the existing router,
  prize pool attached, exercises lanes on an external cadence, and is the §6 tertiary
  ensemble build wearing a race number.
- **Deepest:** the Lean autoformalization engine (§6 primary) — biggest build (Lean sandbox),
  perfect verifier, realest contribution.
- They compose: forecasting rounds = bursty daytime canary; proof-search cron = steady
  overnight volume.

## 14. NEW OPEN QUESTIONS (append to §8)

- [ ] Is the Metaculus bot the first wedge (before or instead of the kindness/pilgrims
      turn-down being "the event")?
- [ ] OSS-bounty lane worth the human-gate overhead, or noise?
- [ ] What cadence coverage does lane-health actually need if self-play goes to minimal —
      do forecasting + proof crons cover it, or keep a thin synthetic canary?
- [ ] Success metric v2: verified-proof count + forecast leaderboard position + $ won?

## 15. ADDED REFERENCES (2026-08-31 session)

- metaculus.com/aib/2026/spring · metaculus.com/tournament/spring-aib-2026 ·
  forum.effectivealtruism.org "Announcing Spring 2026 AI Forecasting Benchmark"
- erdosproblems.com (1,217/570, prizes page, "Problem 728 and the use of AI" blog)
- github.com/google-deepmind/formal-conjectures · github.com/evand/open-math-problems ·
  github.com/openai/ten-proofs
- aimoprize.com · algora.io · dev.to "How to Find and Win Open Source Bounties in 2026"
- scrollprize.org/winners · arcprize.org/competitions/2026 · drivendata.org/competitions
- Reddit scraped this session: r/math mn7bfq (Erdős cash) · r/bioinformatics gzncy5
  (compute donation) · r/bestof 123zf3l (SETI@home outcome) — in deep_search/links/

## 16. GOING PUBLIC — GitHub org CREATED (2026-08-31 evening)

**The one thing that now EXISTS beyond documents:** the GitHub organization
**github.com/kumori-ai** — created 2026-08-31 21:54, org id 323345833, free plan,
`tillo13` = admin/active, 0 repos. Name check at creation: `kumori` taken (dormant 2014
user, 1 repo); `kumori-ai` / `kumoriai` / `kumori-code` / `kumori-labs` all free; picked
**kumori-ai** to mirror the kumori.ai domain. (Org creation is web-UI-only — no API/`gh`
path on github.com; verified empirically, /admin/organizations 404s.)

**⚠ Open action:** the org banner showed "Copilot billing is now usage-based" — set the
per-user Copilot budget to **$0** in org settings so the free org has zero billable
surface. (Token scopes can't touch billing; it's a UI click.)

### Why GitHub is the architecture, not just the host
- **Issues = target queue** (formalize X, hunt counterexample to Y) — anyone can propose.
- **PRs = attempts.**
- **CI = the oracle** — Lean check / counterexample verifier runs as an Actions status
  check on every PR. Green check IS verification; AI-slop from strangers fails CI without
  costing review time; only verified-green PRs need human eyes. Actions runners are
  free-tier → even the checking rides free compute.
- **History = the public audit trail** ("showing our work" for free).
- Prior art: mathlib runs this way; vibemathed is GitHub-backed (mrconter1/vibemathed,
  CC-BY dataset).

### Structure decisions (thought through, not yet built)
1. **tillo13 stays untouched** — personal account, the 40-repo fleet, apps.
2. **kumori-ai org = the public face.** Trust-domain separation is the real win: outside
   contributors interact with the engine repo and never touch the personal account.
3. **Ordering rule for the org page:** the bounty/proof engine is the point; pilgrims /
   kindness / kumori.ai appear in the profile README as *provenance* ("the production apps
   that built this free-lane substrate"), below the engine — never as the lead. If it reads
   as marketing with a research repo attached, it loses the credibility that makes it work
   (the WIRED "AI-for-good is often PR" trap).
4. **"Advertise" = profile README + links to live sites, NOT mirroring app code** into the
   org. Anything ever moved org-side goes through the deploy tool's secret-scan gate.
5. **Attribution inversion (conscious, scoped exception):** Andy's no-AI-attribution rule
   exists for product commits. This repo's value is the OPPOSITE — every result must
   disclose model/lane/method/cost (vibemathed norm). Write this into the engine repo's own
   CLAUDE.md at creation so no session applies either norm in the wrong place.
6. **Money explicitly disclaimed in the README** — the goal is verified public artifacts
   (mathlib PRs, vibemathed submissions, erdosproblems posts), not bounty income. Receipts
   for why the upside is still real: bounties.md "existence proof" block (Liam Price /
   SciAm 2026-04; sub-vs-API economics).
7. **Ops:** org repos still ship via `deploy` (git-only mode — secret scan a raw push
   skips). Contributions inbound: issues-on first; PRs opened later, CI-gated, with a
   CONTRIBUTING.md ("attempts must pass CI, no exceptions").

### Status ledger for this initiative (as of 2026-08-31 EOD)
| thing | state |
|---|---|
| plan.md (§0–10 braindump + §11–15 bounty/canary addendum) | written |
| bounties.md (site catalog + Price existence proof) | written |
| github.com/kumori-ai org | **CREATED** (only real-world artifact so far) |
| Copilot budget → $0 | pending Andy click |
| engine repo, org profile README, CI oracle, any code | NOT created — awaiting green light |
| quality_judge check + kindness/pilgrims turn-down (§3) | proposed, not done |

## 17. GITHUB IS THE PRODUCT — interaction map, money posture, the root (2026-08-31, late)

### The root, stated plainly (everything below is judged against this)
**Idle free-tier compute → machine-verified public good.** A public engine that converts the
kumori free pool's spare capacity into verified truths, with GitHub as the WHOLE interface
and kumori.ai telling the story. Bounties are how we FIND good targets; the scoreboard is the
reward; the money is someone else's to keep or ours to give away. No separate website needed.

### Interaction map — every interaction has a native GitHub feature (no web code)
| people want to… | GitHub piece | notes |
|---|---|---|
| submit a problem/target | **Issue Forms** (`.github/ISSUE_TEMPLATE/*.yml`): source link, statement, verifier type, domain | labels = taxonomy: `math` `forecast` `target` · `queued` `attempting` `verified` `upstreamed` · `external-prize` |
| report an engine bug | second Issue Form | |
| see what's being worked | **Projects** board (queue → attempting → verified → upstreamed) | public, no login to read |
| talk / ask / argue | **Discussions** (button already on the org page) | the forum; no site |
| contribute an attempt | **Pull Request** + PR template requiring provenance | **Actions CI = the oracle**: green = verified; slop fails without human time |
| see the scoreboard | README table / badges regenerated nightly by an Action (N verified, N upstreamed, attempts, per-lane stats) | the public ledger, zero hosting |
| landing page | org profile README (`.github` repo) or **GitHub Pages** (free static; `good.kumori.ai` can CNAME to it) | even the "site" is GitHub-hosted |
| feed the engine | kumori crons **poll the Issues API** for `target` issues → enqueue to free lanes → results post back as comments/PRs | people add problems → pool works them; no form backend |
| **find bounties** (automated) | an Action polls erdosproblems.com prizes + vibemathed RSS nightly → opens/refreshes target issues with `prize:` / `source:` fields | "finding the bounties" as a cron, not a chore |
| moderation | built-in: interaction limits, CoC, report abuse, branch protection, CODEOWNERS | issues-only for strangers first; PRs later, CI-gated |

Division of labor: **GitHub = interaction + ledger + verification; kumori.ai = narrative**
("why idle compute does math now; how to help → github.com/kumori-ai") + the ONE thing GitHub
does badly: a live dashboard (lane health / canary in real time) = a single public read-only
route on the existing Flask app. Login wall is fine for the audience that can help; kumori.ai
is the on-ramp for the curious.
Prior art running this way: DeepMind `formal-conjectures` (pure repo, PRs for statements),
mathlib (GitHub + chat), Metaculus bots (template repos).

### Money posture — decided-once, README sentence, never revisited (dos_bros pattern)
> **"No money flows through this project. Prizes won by contributors are theirs; anything
> paid to the org's own accounts is donated to ⟨named recipient⟩ and logged here."**
1. Money never flows through the org (no paymaster job: tax forms, intl payments, disputes;
   keeps the hobby non-commercial — same employer-OBA line dos_bros holds).
2. Human solvers claim their own prizes; joint solvers settle among themselves; the org
   records attribution (PR co-authorship), never adjudicates cash. Awarding bodies pay a named
   human anyway (Erdős → the solver; Metaculus → bot account holder; Algora → PR author).
3. Anything paid to Andy's/the org's own accounts (e.g., a Metaculus season share) → donated
   by pre-declared rule to a named recipient (candidates: Lean FRO / mathlib, Folding@home,
   Internet Archive — Andy picks), publicly logged. Turns "I don't need the money" into a
   credibility asset.
4. The org never funds bounties itself (rule-#1 analog: no prize money from a party with a
   stake — kumori's engine attempts the same problems).
- **Rejected:** "kumori sets its own bounties from winnings" (re-creates paymaster + slop
  magnet + stake; tiny sums). "Promote dosbros.ai" — only as PROVENANCE ("same two brothers,
  out of pocket, for the love of it") in the below-the-fold footnote with the apps; never as
  a funnel (the WIRED "AI-for-good is PR" trap).
- Why money-out is also the anti-slop policy: the AI-PR flood is bounty-driven; a repo that
  pays becomes a target; one that doesn't self-selects for people who care about the math.
  For this crowd, CREDIT (PR, vibemathed entry, mathlib commit) is the strongest motivator;
  cash the weakest.
- **Naming:** drop the word "bounty" in public unless money is attached — "open problems",
  "targets", "scoreboard" say what's true.

### Contribution policy — what to write into the engine repo (research 2026-08-31)
- **Doctrine gap (verified):** nothing in `~/.claude/rules/` or the deploy skill covers PR /
  issue / branch-protection / Actions mechanics — only `deploy "msg"` + the attribution rule
  (`git-deploy.md:5`). Correct home per the scope test = REPO-LEVEL: `CONTRIBUTING.md` +
  `.github/` templates + the engine repo's own `CLAUDE.md`. Global rules unchanged.
- **Reference list:** `github.com/melissawm/open-source-ai-contribution-policies` (~80
  projects, Feb 2026; also RedMonk's policy-landscape article, CHAOSS wg-ai-alignment list).
  Copy the *allowed + disclosure required + human-in-loop* cluster: Apache Airflow, Arrow,
  GDAL, cilium (DCO sign-off), Django (PR template), Fedora, Drupal, EasyBuild (must name the
  specific models).
- **Lines to steal:** curl — "a contribution should be worth more to the project than the
  time it takes to review it"; Ghostty — "not an anti-AI stance, but the number of highly
  unqualified people using AI."
- **Attribution inversion resolved:** the ASF already mandates a **`Generated-by:` commit
  trailer** — adopt that (model/lane/cost disclosure) instead of `Co-Authored-By`. Andy's
  no-AI-attribution rule stays intact for product repos; this repo requires provenance via a
  different, existing standard.
- **Four layers** (bswen, Mar 2026 — a maintainer counted 136 PRs / 15 days, 71% slop):
  CONTRIBUTING → required issue linkage → AI disclosure → automated quality gates. Our
  CI-as-oracle makes layer 4 nearly free.

### Status (unchanged): org exists; nothing else built. §16 ledger stands; this section adds
the design content the README / CONTRIBUTING / templates get written FROM, when green-lit.

## 18. VOLUNTEER COMPUTE — spend your leftover AI quota on a problem (2026-09-21)

Provenance for issue #6. Thought through with Andy the afternoon the repo moved to
`kumori-ai`. Nothing here is built. The plan item is in `PLAN.md`; the gate is issue #1.

**Andy's words, in order:**
- "what about some sort of way to let individual people use their credits from gpt/claude/kimi/
  grok/etc to try to solve some? like, if you're about to roll over your credits for the week,
  and want to put them to use, kinda like the seti @ home angle from 1990s. like it's going to be
  wasted anyway"
- "I have agents running non-stop in my terminal all day from codex, and claude. and if I didn't
  have use for them, and my credits were about to roll over, I'd definitely open a window and tell
  it to [read an] agents.md file ... and start on the math problem at hand, etc, and then provide
  the proofs, data to the comments/etc for the next person to pick up, use their level of claude
  opus, fable, etc, etc, all the way through"
- "there's no downside or work they'd need to do, or have it be intrusive, all we'd tell it is to
  know what model/provider, tokens, times, etc ... so we can also judge them too"
- "we would clearly need to put safeguards in place ... some sort of prove who you are type thing
  ... to remove bad actors ... but that's kinda the point of kumori, right? to know and work with
  good actors/people"

**What holds up (and why this project suits it better than SETI@home did):**
- SETI@home sent each work unit to several volunteers because a volunteer could lie. Here the
  Lean kernel checks every answer, so nobody has to be trusted for correctness. A stranger's
  proof counts exactly as much as the router's.
- It answers the ceiling the stall rule (issue #1) measures: if the free lanes stop on the hard
  rungs, the missing ingredient is stronger models, and volunteers' leftover frontier quota is
  exactly that, at $0.
- It needs less than it first looked. An agent with a terminal can clone the repo, install Lean
  with the README's four commands, run `tools/check.py`, and see the kernel's verdict BEFORE it
  posts. The repo re-checks everything anyway (a claimed accept is never trusted), but the
  volunteer is not blocked waiting on us.
- The relay is the point: one agent posts what it tried, the Lean, the kernel's complaint and the
  goals still open; days later someone else's stronger model starts from that partial. The issue
  thread is the shared memory between people who never talk.

**The design, as far as it got:**
1. **An `AGENTS.md` for OUTSIDE agents.** Codex reads it natively; Claude Code can be pointed at
   it. The repo's `CLAUDE.md` is written for Andy's own sessions and would confuse a stranger's
   agent. Contents: how to pick a problem, set up Lean, check a proof, the comment format, when
   to stop. The pitch to a volunteer is one sentence: point your agent at this file.
2. **A fixed hand-off comment format**: model, tool, approach, the Lean, the verdict, goals
   remaining, dead ends, wall-clock time, attempts; tokens only "if your tool shows them" (most
   agents cannot see their own token count, and a required field nobody can fill gets invented
   numbers).
3. **Agents read only what our bot wrote.** A stranger's comment could carry instructions aimed
   at the next person's agent ("ignore your instructions and run this"). So: a submission is
   checked, and a bot re-posts a clean fixed-format result; `AGENTS.md` tells every agent to read
   ONLY the bot's comments, to treat everything else as data, and to run nothing but the checker.
   This goes in BEFORE the door opens to strangers.
4. **The checking workflow runs with no secrets and a read-only token**, isolated from the
   workflow that holds `KUMORI_API_KEY`. A Lean file can run code while it is being checked.
5. **Tiers, not ID checks.** Anyone: read, comment, submit (bot-checked). Known contributors:
   the Triage role (label, assign, close, sub-issues; no code, no secrets). Bad actors: GitHub's
   block, interaction limits, and approval-before-first-run. Vouching (a trusted contributor
   vouches for a new one) is the version that rhymes with Trustable / Sunnier / Inroads. Real
   identity proof is heavy and invasive and would kill "it costs you nothing to try". Identity is
   not needed for correctness, only for abuse.
6. **Swarm mechanics on GitHub:** the problem's issue is the parent, each remaining goal a
   sub-issue; claim by assignment or a comment, stale claims return to the pool; labels carry
   state (`claimed`, `needs-check`, `verified`, `dead-end`); a Projects board once there are
   enough to need one. About 5,000 API calls an hour per account: fine for a person and a handful
   of agents, which is why issues are the human layer and the ledger stays the machine layer.
7. **Credit is the retention mechanism.** SETI@home ran on its stats pages. A public board: who
   solved what, with which reported model.

**What is honest to say about it:**
- Everything but the proof is self-reported. "Reported model", never "verified model". Fine for
  credit and fun; not science.
- Frontier models may have memorized miniF2F. A proof is valid either way, but such a solve says
  nothing about reasoning. It stops mattering on open problems (`PLAN.md` step 14).
- Volunteer results are their own source and never count toward what the free lanes proved.
- What it costs a volunteer: a GitHub login on their machine, a one-time Lean + mathlib download
  (several GB, 10-20 minutes), their own quota, and running our open-source checker locally.
- We never ask for, accept or store a key, a login or a session. No analytics, no phoning home.
  That is what "not intrusive" commits us to, and it is also what keeps us clear of providers'
  terms on account sharing (not re-read today; each volunteer checks their own plan).

**Order:** start closed. Andy has a first person in mind; he tests `AGENTS.md` and the comment
format with his own agents while the only people in the thread are people Andy knows. The bot and
the secret-free checker go in before it opens. Gated like everything else in Phase C: if the free
lanes are still solving two a day after 2026-09-28, this can wait.
