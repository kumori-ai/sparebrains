# sparebrAIns

**Idle free-tier compute → machine-verified public artifacts.**

The kumori free-LLM pool (60+ free-tier models behind one router) sits idle most of the day.
sparebrAIns points that spare capacity at competition mathematics written in Lean 4 and lets
the Lean proof kernel, not a person and not another model, decide what counts. Every call
either produces a kernel-verified proof or is honestly recorded as a miss, in full, for the
next attempt to build on. Nothing false survives; nothing learned is thrown away. Cost: $0.

| | |
|---|---|
| Live scoreboard, every run, every transcript | **https://sparebrains.kumori.ai** |
| How it works, in full | https://sparebrains.kumori.ai/how |
| Why, where the problems come from, the plan, how to check every claim | https://sparebrains.kumori.ai/about |
| Code, targets, ledger, verified proofs | this repository |

## The ladder

The engine asks every free lane the same rungs, easiest first, three tries per (problem, lane), and the
site draws who clears what: [sparebrains.kumori.ai](https://sparebrains.kumori.ai). Rungs are provenance,
never our own results:

| rung | problems | source | reference proofs |
|---|---|---|---|
| primer | 74 | the Natural Number Game, Lean 4 edition, restated over Mathlib's ℕ (`targets/primer/`) | yes, kernel-checked in CI |
| mil | 60 | Mathematics in Lean, chapters 2–6, Avigad & Massot (`targets/mil/`) | yes, kernel-checked in CI |
| MATH L1–L5 | 130 | miniF2F's `mathd_*` items, labelled by the MATH dataset's own levels (`targets/minif2f/levels.json`) | upstream's, not shipped |
| amc12, custom, aime, imo | 114 | the rest of miniF2F, by problem source | upstream's, not shipped |

A lane clears a rung at verified ÷ answered ≥ 0.5 over at least 3 answered asks. A reject is
classified (`tools/ladder.py`): `lean3_syntax` and `no_fence` mean the model could not write a Lean 4
file in the required shape, which says nothing about the math. Every number on the site carries the
equation it came from, with the live inputs substituted.

## What is happening right now
- **The exam paper.** `targets/minif2f/test/`: 244 competition problems (AMC, AIME, IMO,
  textbook algebra and number theory) in Lean 4, from DeepMind's corrected miniF2F fork, one
  file per theorem with `sorry` as the only hole. All 244 type-check under this repo's pin.
- **The judge.** `tools/check.py` compiles a file with Lean and audits its axioms. Accepted
  means: compiles, statement untouched, only the three standard axioms. `checks/` must pass
  and be refused, respectively, on every push (`.github/workflows/check.yml`).
- **The loop.** `tools/attempt.py`, run by `.github/workflows/attempt.yml` on GitHub's free
  runners: ask each model lane for a proof, splice it under the original statement, hand it to
  the judge, record everything. Ladder mode asks the cheapest lanes first; sweep mode asks
  every lane so each gets a real score.
- **The schedule.** Two sweep chunks a night (22:00 and 03:00 Pacific) over whatever targets
  no sweep has touched yet, until all 244 are covered. Then the same loop points at open
  problems (`PLAN.md` §7).
- **The record.** Every attempt's full transcript goes to a Postgres table behind kumori's
  API (the site renders it). This repo keeps the compact ledger (`ledger/`) and every
  accepted proof whole (`verified/`), committed by the workflow with a `Generated-by:` trailer.
- **The digest.** One email a day: first-time solves, last night's runs, the lane scoreboard.

## Verified means
A `.lean` file counts only if all three hold, checked by `tools/check.py` on a GitHub-hosted
runner with Lean `v4.33.1` and mathlib `v4.33.1`:
1. `lake env lean` exits 0 (the kernel accepted it);
2. its only hole marker, `sorryAx`, is absent from the axiom audit;
3. `#print axioms` for every theorem is within `propext`, `Classical.choice`, `Quot.sound`.

No proof is graded by eye, and no model grades another model. Unsolved means not yet.

## Check the work
- A run: its line-per-attempt file under `ledger/`, its commit on the commits page (author
  `sparebrains-bot`), its job log under Actions (kept 90 days), its page on the site.
- A proof: the file under `verified/<set>/<target>/<lane>.lean`. Re-check it yourself:
  ```
  git clone https://github.com/kumori-ai/sparebrains && cd sparebrains
  curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y
  lake exe cache get && lake build
  python3 tools/check.py --expect accept verified/minif2f/test/amc12_2000_p12/mistral-devstral.lean
  ```
- A decision: `DECISIONS.md`, dated, with receipts. Open items: `PLAN.md` §6. The plan: §7.
- Secrets: none in this repository or its history. The router key lives in a GitHub Actions
  secret and reaches the loop only as an environment variable.

## Read next
1. `DECISIONS.md`: what's settled, dated, with receipts. Don't re-litigate.
2. `PLAN.md`: the yield gate, the measured numbers, what's not in v1, what's open, the plan.
3. `TARGETS.md`: where machine-checkable problems live (math, forecasting, code, science).
4. `BRAINSTORMS.md`: the original three-session braindump, verbatim, for provenance.

## The name
`sparebrains` in every machine identifier (folder, repo, package, service, caller tag).
`sparebrAIns` wherever a human reads it. Spare AI brains, put to work. The pun is also the
honest part: free-tier models are spare parts, and the verifier is what makes that fine.

## Money
No money flows through this project. Prizes won by contributors are theirs; anything paid to
the org's own accounts is donated to a named recipient and logged here. The org never funds
prizes itself. Every run's commit names the pool, the lane count and the verifier versions.

## License
Apache-2.0 (`LICENSE`): the license of mathlib, of both target sets, and of the Lean proof
datasets this record sits beside. It covers the tools, the ledger and the verified proofs.
Carved out: model outputs from two provider groups whose terms do not allow a public record.
Rows, transcripts and `verified/` files from Cohere lanes and from NVIDIA's trial endpoints
(OpenRouter `nvidia/*:free`, the direct `nvidia` lanes, OpenCode's Nemotron free), produced by
jobs through run 33652466778, stay as published under those providers' own terms, not this
license; those lanes no longer run here. Verdict rows (target, lane, verdict, timing) are this
project's own facts and are licensed. The clause-by-clause read of every provider is in
`DECISIONS.md` (2026-09-02).

## Provenance
Built on the kumori free-LLM substrate (`kumori/shared/kumori_free_llm`) that also runs
pilgrims_world and kindness_social. Those apps are how the substrate got built; this is what
its spare capacity does now. Targets: google-deepmind/miniF2F, Apache-2.0
(`targets/minif2f/README.md`). Verifier: Lean 4 + mathlib via leanprover/lean-action.
