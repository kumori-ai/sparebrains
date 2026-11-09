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
