# Stage 3 design: anyone's own AI on an open problem, checked automatically

**Status: design only, 2026-10-07. Nothing here is built.** It starts when the relay's first pass and
the pilot verdict are in (`PLAN.md` §7, stage 3) and Andy says go. The idea and its rules are issue #6.

## What a volunteer does
1. Opens a problem's thread (label `problem`), copies its prompt pack into their own model or agent.
2. Posts one comment in the hand-off format from `AGENTS.md`, with the full `.lean` file in one fence
   and the model named.
3. Within minutes `kumori-ai[bot]` replies with the kernel's verdict. No key, login or data of theirs
   ever reaches us; their quota, their machine.

**Done when** a person outside the project does that and gets a verdict with no maintainer action (#6).

## The one hard problem: a stranger's Lean file is code
Lean runs code while it checks a file (`#eval`, `IO`), and the check is triggered by a stranger's
comment. The community-standard answer is GitHub Security Lab's split (*Keeping your GitHub Actions
and workflows secure*, part 1 "Preventing pwn requests" and part 2 "Untrusted input"): the job that
touches untrusted input holds nothing, and the job that holds something never runs untrusted input.

**Workflow A, `submission-check.yml`** (on `issue_comment`, created or edited):
- `permissions: contents: read` and nothing else; references **no secret at all**.
- Runs only for issues labeled `problem`, a comment under 50 KB, one check per author per issue per
  10 minutes.
- Untrusted text reaches the job only through `env:` (the comment body), never through `${{ }}` in a
  `run:` script, which is how script injection happens.
- Extracts the one fenced Lean block, splices it onto the target statement and refuses anything whose
  statement differs from the target (statement hash, as the engine does).
- Judges it with `tools/check.py` inside the stage-2 sandbox (`judge_sandbox.sh`: Lean as `sbjudge`,
  empty environment, no `/proc` view of the job), with the usual timeout.
- Writes one small JSON verdict (issue, comment id, target, verdict, reason, Lean output clipped, the
  reported model) as an artifact. Nothing else leaves the job.

**Workflow B, `submission-post.yml`** (on `workflow_run` of A, completed):
- Holds the app token and `KUMORI_API_KEY`; never checks out or runs anything from the comment.
- Reads A's artifact as data, validates it against a fixed schema, drops anything malformed.
- Replies on the thread as `kumori-ai[bot]` with the verdict and Lean's complaint.
- Records a row in `sparebrains_attempts`: `try_mode` `volunteer`, backend `volunteer:<github login>`,
  model as reported. On accept: the proof goes to `verified/<set>/<target>/volunteer-<login>.lean`
  through `publish.py`, and the thread closes.

## How it is counted
- Volunteer results are their own source and never count toward what the free lanes proved (#6). The
  site shows them as a separate kind of try, as it does relay and fixer.
- A volunteer's model may have seen a published solution (miniF2F is public): a proof counts either
  way, but it is labeled "volunteer, reported model", never "the pool solved it". Stage 5's open
  problems are where that distinction stops mattering.
- A known proof from elsewhere is welcome as a link and recorded as found in the literature.

## Abuse
GitHub's own tools first: interaction limits, blocking, Triage for known contributors. Plus the per-
author rate limit, the comment size cap, the Lean timeout and the sandbox. A flood of bad Lean costs
free GitHub minutes and nothing else, because nothing in A can reach anything.

## Tests before it goes live (each made to fail first)
- The isolation canary, unchanged: a planted secret must be invisible to Lean in workflow A.
- A comment whose text is a script-injection payload (`${{ }}`, backticks, `$(...)`) runs nothing.
- A comment whose Lean prints the environment shows no secret in the reply.
- A malformed or oversized artifact is refused by B and posts nothing.
- A statement edited by the volunteer is rejected as a different problem, not checked.

## Left open
- Claiming a piece of a problem (sub-issues, from #4's proofs in blocks): a separate step.
- Whether copy and paste is enough, or volunteers want a small command that fetches the pack and
  posts the result (#6 asks; answer it from real use).
- What the scoreboard counts for volunteers: problems, first solves, or pieces.
