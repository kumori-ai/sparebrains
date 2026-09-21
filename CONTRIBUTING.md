# Contributing to sparebrains

Thanks for looking. This project asks free AI models to prove mathematics in Lean 4 and keeps
only what the Lean kernel accepts. The same standard applies to anything a person sends in.

## What helps most, in order

1. **A misformalization report.** A Lean statement that does not say what its source problem
   says. One of these is worth more than a hundred proofs, because a proof of the wrong
   statement is worthless and we cannot see it ourselves.
2. **A piece of an open problem.** When a problem resists the models working alone, it gets an
   issue holding its best partial proof, what is left to prove, and what has already failed.
   Comment to claim a piece, then post your Lean. It is run through `tools/check.py`, the same
   judge and the same mathlib pin the engine uses, and the verdict is posted on the issue. You
   can run that judge yourself first; the README's "Check the work" section has the four
   commands. Automatic checking of contributed proofs is not built yet.
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
person reviewing it first.

## Conduct

The [Code of Conduct](CODE_OF_CONDUCT.md) applies everywhere in this project.
