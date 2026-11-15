# Frozen replay cohorts

Inputs for `tools/replay.py`: a lane's stored answers, re-run with zero model calls. Results land here as
`results-<run>-<attempt>-<slice>.jsonl`, fenced from every try reader (`tools/ledger_files.NOT_TRIES`).

## groq-allam-ladder-x3-2026-10-24.jsonl.gz

- What: every answered (accept or reject) attempt by `groq-allam` (allam-2-7b) in mode `ladder-x3`: 1,190 attempts,
  8 accepts, on 378 problems. Fields: id, created_at, run_id, target_set, target, statement_sha, attempt_no, mode,
  verdict, reason, failure_kind, rung, response (the raw reply). 463,864 bytes; sha256 begins ad65d5edb378a7cf.
- From: kumori's `sparebrains_attempts`, 2026-10-24, one read-only query as `adhoc_session`:
  `SELECT id, created_at, run_id, target_set, target, statement_sha, attempt_no, mode, verdict, reason, failure_kind,
  rung, response FROM sparebrains_attempts WHERE backend = 'groq-allam' AND mode = 'ladder-x3' AND verdict IN
  ('accept','reject') ORDER BY id`.
- Public already: every row is served at https://sparebrains.kumori.ai/attempts/<id> with its full reply (the route
  filters nothing; 8 ids sampled 2026-10-24, the first and last included, all 200 signed out).
- Against the git ledger: 1,129 answered ladder-x3 rows in 21 runs match the database row for row; run 33881328961
  (61 rows) is in the database only, its ledger file never committed. Kept: the cohort is not cut to match.
- Exposed: attempts 15335, 15336 and 15354 were read in full during diagnosis; their problems (all on the report
  half by problem hash) are left out of the reported numbers.
- Built against: git 25bb2e81, Lean leanprover/lean4:v4.33.1, closers `subgoals.AUTO_TACTICS`, the judge's own
  timeouts; every result row carries tools_hash and lean_env.

## ministral-ladder-x3-2026-11-09.jsonl.gz

- What: every answered (accept or reject) `ladder-x3` attempt by the Ministral lanes (`mistral-ministral-%`: 3b, 8b
  and 14b, both `-2512` and `-latest`) on the 164 targets baseline 2 (`baseline-2-2026-11-09`, attempt run 42564725514)
  tested and did not prove: 2,835 attempts (2,827 reject, 8 accept, all 8 by 14B), ids 9510 to 46290. Fields as the
  allam cohort plus `backend`. 1,496,958 bytes; sha256 begins f1f0c4bce760eeeb.
- From: kumori's `sparebrains_attempts`, 2026-11-09, one read-only query as `adhoc_session`: `SELECT id, created_at,
  run_id, target_set, target, statement_sha, attempt_no, mode, verdict, reason, failure_kind, rung, response, backend
  FROM sparebrains_attempts WHERE backend LIKE 'mistral-ministral-%' AND mode = 'ladder-x3' AND verdict IN
  ('accept','reject') AND (target_set || '/' || target) = ANY(<the 164>) ORDER BY id`.
- Why (#574): small lanes solve almost nothing off the no-model baseline, and 57% of their rejects there show a
  form or name diagnostic as their first error; this replays them through the existing chain with zero model calls
  to measure what post-hoc repair buys them beyond automation. Read: `replay.py --cohort <this> --report`, per reply
  against its recorded verdict (accepted as extracted, chain rescues, recovery extra kept apart). Design: Codex
  20261109T164835638082Z DISAGREE (attribution), round 2 AGREE.
- Public already: the same rows are served at https://sparebrains.kumori.ai/attempts/<id> (the first and last ids,
  9510 and 46290, both 200 signed out, 2026-11-09), as for the allam cohort.

## repair-open-2026-11-09.jsonl.gz

- What: every rejected `repair` try (the model's second answer after Lean's error) with a proof, on the 18 problems
  open at freeze time (sparebrains.kumori.ai/targets.json, 2026-11-09): 845 rows from 55 lanes, ids 3968 to 101911.
  Fields: id, created_at, run_id, target_set, target, backend, quality_tier, rung, proof, lean_output. 773,912 bytes;
  sha256 begins 00dff2c65955c499.
- From: kumori's `sparebrains_attempts`, 2026-11-09, one read-only query as `adhoc_session`: `SELECT id, created_at,
  run_id, target_set, target, backend, quality_tier, rung, proof, lean_output FROM sparebrains_attempts WHERE
  try_mode = 'repair' AND verdict = 'reject' AND proof IS NOT NULL AND proof <> '' AND run_id NOT LIKE 'smoke%' AND
  (target_set || '/' || target) = ANY(<the 18 open>) ORDER BY id`.
- Why (#574): the nightly retro gives the free chain (fixer, holes, Lean's automation; no model) only to cold tries
  (kumori `_COLD_REJECT`), and the ladder repairs inline only relay tries, so no repair try was ever chained (19,919
  rejects). On the Ministral cohort above, 69 of the 107 chain rescues were repair tries. Run: attempt.yml
  `fixer_target=retro:repair-open-2026-11-09.jsonl.gz`, which records an open-problem solve for the lane that wrote
  the reply and sends no ablation row. Design: Codex 20261109T200739796471Z AGREE.
- Public already: the first and last ids, 3968 and 101911, are served at https://sparebrains.kumori.ai/attempts/<id>,
  both 200 signed out, 2026-11-09.

## all-lanes-ladder-x3-2026-11-14.jsonl.gz

- What: every answered (accept or reject) `ladder-x3` attempt by any lane, created from 2026-11-09T18:00Z (after
  replay run 42663548076 began, 17:22Z) to 2026-11-14T23:59Z, on the same 164 targets baseline 2
  (`baseline-2-2026-11-09`) tested and did not prove: 2,307 attempts (2,197 reject, 110 accept) from 30 lanes on all
  164 targets, ids 101902 to 105917. No Ministral reply is in it (those lanes have none since the first cohort), and
  no id is shared with `ministral-ladder-x3-2026-11-09`. Fields as that cohort. 1,276,140 bytes; sha256 begins
  257a1cf37d71f502.
- From: kumori's `sparebrains_attempts`, 2026-11-14, one read-only query as `adhoc_session`: `SELECT id, created_at,
  run_id, target_set, target, statement_sha, attempt_no, mode, verdict, reason, failure_kind, rung, response, backend
  FROM sparebrains_attempts WHERE mode = 'ladder-x3' AND verdict IN ('accept','reject') AND created_at >=
  '2026-11-09 18:00+00' AND created_at < '2026-11-14 23:59+00' AND (target_set || '/' || target) = ANY(<the 164>)
  ORDER BY id`. No filter on lane or outcome.
- Why: the Ministral replay found 107 of 2,827 rejected replies accepted after the chain, on 17 targets (8 more were
  accepted as extracted; recounted from the result rows 2026-11-14, DECISIONS.md's "0 accepted as written" is wrong).
  That was one model family and a historical set. This asks whether it holds on other lanes' later replies, which
  did not exist when that run was read. Tool changes since 2026-11-09T18:00Z touch no chain file (fixer.py,
  proof_text.py, toolscore.py unchanged; Codex's check and mine); that is no proof nobody read these replies.
- The read, written before the run: per reply, its recorded verdict (the raw answer), accepted after the chain, and
  the no-model baseline (it rejected all 164, so every accept here is off the baseline). Reported per lane, per
  tools and Lean version (this run is not pooled with 42663548076: tools 39dfcb35ec then, 278a8cc155 now), and on
  the report half of the problems (`toolscore.problem_half`) beside the total. **It holds if, on the report half, at
  least 1% of rejected replies are accepted after the chain and at least 5 distinct targets are rescued; otherwise it
  does not.** Judged only on a complete run. For scale, the Ministral run by half: 83 rescues on the tune half, 24 on
  the report half (Codex's recount, to be re-derived with this run's read).
- Not claimed whatever it shows: new mathematics (none of the 164 need be open), independent replies (repeat tries
  on one target are not; targets are the unit), or that no model is needed (the chain keeps the model's structure).
- Public already: the first and last ids, 101902 and 105917, are served at https://sparebrains.kumori.ai/attempts/<id>,
  both 200 signed out, 2026-11-14.
- Design: Codex 20261114T235518274863Z AGREE (f1 follow-up: `--report` has no per-half table yet; the bar above is
  read from the result rows by half).
