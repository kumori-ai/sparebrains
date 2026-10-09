# Results: the loop

Measured 2026-10-09. Every number here comes from public rows (the ledger in this repository and
`https://sparebrains.kumori.ai/loop.json`) and can be re-derived with the commands at the end. These are
measurements with a date, not settled facts; they change as the pool, the problems and the tools change.

## The question

Stage 1 asked every free model for whole proofs and let the Lean kernel accept or reject each one. A reject
was the end of that try. On 2026-10-08 agent volunteers (Claude, Codex, Haiku) solved, on their first
check, open problems the free models had failed 100+ times each; the difference was that they could run
Lean, read its error and fix one step. So: **how many of the free models' rejected proofs were one or two
steps from correct?**

## Method

`tools/subgoals.py`, after APOLLO (arXiv 2505.05758), takes a rejected proof apart without asking any model:

1. **fix** its form (`tools/fixer.py`: layout, Lean 3 syntax, invented library names);
2. turn every step Lean rejected into a hole (`sorry`), keeping the steps Lean accepted;
3. try Lean's own automation on every hole (`omega`, `linarith`, `nlinarith`, `positivity`, `decide`,
   `norm_num`, `simp`, `aesop`, `exact?`);
4. print each hole still open as a standalone lemma (`extract_goal`, with numeric types);
5. optionally ask a model for that lemma alone, and splice a proved one back.

Nothing counts until the kernel accepts the whole file against the problem's exact statement.

The ablation re-ran **every stored rejected cold try** of stage 1 (`python3 tools/attempt.py --retro`),
Lean only, and recorded four arms. B and C post-process the very answers A judged, so the comparison is
paired: a difference is the stage's, not a luckier answer.

| arm | what runs | model calls |
|---|---|---|
| A | the cold try as the kernel judged it | already made |
| B | A plus the fixer | 0 |
| C | B plus holes and Lean's automation | 0 |
| D | C plus the strongest live free lanes on the steps left open | a few per sketch |

## What it found

Over 22,050 answered cold tries, with 9,848 of 10,379 stored rejects re-run (95%; the rest is queued):

| tier | answered | A accepted as written | C with the loop | rejects C turned (95% CI) |
|---|---:|---:|---:|---:|
| tiny | 802 | 6.0% | **30.2%** | 27.1% (24.0 to 30.5) |
| low | 4,350 | 15.2% | 32.1% | 23.7% (22.2 to 25.2) |
| medium | 3,300 | 53.1% | 63.3% | 25.5% (23.3 to 28.0) |
| high | 3,842 | 62.1% | 69.0% | 24.0% (21.6 to 26.6) |
| frontier | 1,543 | 66.6% | 73.1% | 24.4% (20.5 to 28.8) |
| untiered | 8,213 | 48.8% | 59.1% | 26.4% (24.9 to 28.0) |
| **all** | **22,050** | **44.8%** | **56.1%** | **25.1% (24.3 to 26.0)** |

- **About a quarter of all rejected proofs were within Lean's own reach**, at every tier.
- **The smallest models gain the most in relative terms:** tiny lanes go from 6.0% to 30.2%.
- **The fixer alone (B) turned 0.5%** (51 rejects). Form is rarely the whole problem; a bad step usually is.
- **17 open problems got their first accepted proof through the loop on 2026-10-08** (15 from stored near
  misses, 2 from fresh relay tries), among them `imo_1959_p1`, `aime_1997_p9`, `amc12a_2002_p13`,
  `amc12b_2002_p19` and `numbertheory_2pownm1prime_nprime`. Each is listed with its before-and-after diff at
  https://sparebrains.kumori.ai/loop.

## What it did not find

**Arm D: the free models did not prove the steps left open.** Across 176 answered lemma asks to the
strongest live free lanes, 0 real steps were proved. One row reads as proved (amc12b_2002_p4); it was an
artifact of our own tool, a real-number step printed without its type and re-read in ℕ, where
`1/2 + 1/3 + 1/7 = 1/42` is `0 = 0` (DECISIONS.md 2026-10-09). The free models' failures on those small
lemmas were mostly failed tactics, invented library names and Lean 3 syntax.

So, as of this date: the gain is **the models' proof shapes plus Lean's automation**. Finishing the steps
automation cannot close needs a stronger prover than the free pool offers, such as a volunteer's agent.

## Limits

- The stored tries are stage 1's: one prompt shape, one try per answer. A different prompt would give other
  shapes.
- A "turn" can land on a problem already solved; the open-problem count is the stricter headline.
- Tiers are kumori's labels for the lanes at the time of the try; "untiered" lanes had none.
- miniF2F, MIL and the primer are public benchmarks: a model may have seen proofs of some statements. That
  affects A, B and C alike, since B and C only post-process A's answers.
- Not yet run: the same pipeline on a held-out set (miniF2F-valid), which nothing here was tuned on.

## Since then

The relay runs the loop on every rejected try as it happens. Every cold reject is set to get the free half
(B and C) once a day; the daily pass is started by the relay because GitHub's scheduler dropped the first
nightly run, and its first run under that trigger is pending as of this writing. Arm D waits for stronger
provers.

## Reproduce

```sh
# the judge and the loop's tests (Lean only, no key)
python3 tools/lean_tools.py check proof.lean
python3 tools/test_subgoals.py

# the ablation over every stored cold reject (needs a kumori key with sparebrains.write)
python3 tools/attempt.py --retro --slice 0/1

# the numbers on this page
curl -s https://sparebrains.kumori.ai/loop.json
```
