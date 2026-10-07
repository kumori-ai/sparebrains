# Contributing to sparebrains

Thanks for looking. This project asks free AI models to prove mathematics in Lean 4 and keeps
only what the Lean kernel accepts. The same standard applies to anything a person sends in.

## What helps most, in order

1. **A misformalization report.** A Lean statement that does not say what its source problem
   says. One of these is worth more than a hundred proofs, because a proof of the wrong
   statement is worthless and we cannot see it ourselves.
2. **Help on an open problem.** Problems the models could not solve alone have a public thread:
   [issues labeled `problem`](https://github.com/kumori-ai/sparebrains/issues?q=label%3Aproblem).
   Each first post is written by `kumori-ai[bot]` and kept current: the statement, the closest
   attempt with exactly what the kernel said, the library names models made up, and a prompt pack
   (the text the free models are shown). The comments are yours. **The next model that tries the
   problem reads them**, and its try is recorded as `relay+thread`, apart from the models working
   alone, so the help is counted honestly. After every run the bot replies with each model that
   tried, its model name and the kernel's verdict. The first problem solved this way was #11
   (2026-10-07), from a person's hint. What helps: an idea in your own words, a lemma name that
   really exists, a partial proof, a link to your own branch or write-up. To try with your own
   model or agent, start from [AGENTS.md](AGENTS.md); check your Lean with `tools/check.py`, the
   same judge and mathlib pin the engine uses (the README's "Check the work" has the commands).
   Automatic checking of Lean posted in comments is stage 3 and not built yet; until then the
   maintainer re-runs it.
3. **A new target.** Something with a real answer key, stated in Lean 4 against our mathlib pin
   or precise enough that it can be.

Questions and arguments go in Discussions. Issues are for things that can be closed.

## Using AI

AI assistance is welcome here. It would be strange if it were not. Three conditions:

- **Say so.** Name the model and how you used it, in the issue or the commit. Every attempt the
  engine makes discloses its model, lane, method and cost, and contributions are held to the
  same line.
- **Understand what you send.** If you cannot explain your own proof or report, do not send it.
- **No known proofs in, as new proofs out.** If a proof of the problem already exists somewhere,
  link it. "Found in the literature" is a useful result and a different one from "new proof".

The kernel is the judge. A proof counts when `tools/check.py` accepts it, and not before.
Nobody's opinion, including the maintainer's, turns a rejection into an accept.

## What we will not take

- Proofs that use `sorry`, `admit`, `native_decide` or new axioms.
- Changes to a target's statement inside a proof PR. A statement change is its own issue.
- Unreviewed machine output sent in bulk. Repeat senders are blocked.

## Pull requests

Issues first, for now. Open one and say what you intend before writing code for the engine
(`tools/`). Proofs for an open problem are the exception: post them on that problem's issue.

Nothing from this repository is submitted upstream, to mathlib or a problem site, without a
person reviewing it first. mathlib's own guide does not allow LLM-written comments on its GitHub
or Zulip and asks for a human Lean expert behind any AI-assisted pull request (its "Use of AI",
read 2026-10-06); our bot writes only in this repository.

## Conduct

The [Code of Conduct](CODE_OF_CONDUCT.md) applies everywhere in this project.
