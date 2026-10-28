"""The ledger's try-row files, for every tool that reads them all. The speed receipt's re-solves (task #191) live
under ledger/speed/ and are a benchmark, not tries: they must never retire a ladder cell, owe a prover sample, close
an issue, or count in the retro, so they are left out here, in one place. A TPU batch's heartbeats
(ledger/prover-beats/, 2026-10-23) are diagnostics, not tries, and are left out the same way. A target set may not
take one of these names (test_ledger_files), or its real tries would be hidden."""
from pathlib import Path

BENCHMARKS = ("speed",)
NOT_TRIES = BENCHMARKS + ("prover-beats", "replay", "lane-repair")   # replay, lane-repair: re-judged stored answers, never new tries (2026-10-24, -28)
LEDGER = Path(__file__).resolve().parent.parent / "ledger"


def try_files(root, name="*.jsonl", recursive=True):
    """Every file matching `name` under `root` (or in `root` alone), except benchmark files: under this repo's
    ledger/speed/ or the root's own speed/, by where the file sits and where it points, so a link into or out of
    one, or a root inside one (retro --ledger ledger/speed), is left out too."""
    root = Path(root)
    fenced = [d.resolve() for b in NOT_TRIES for d in (LEDGER / b, root / b)]
    fenced += [a / b for a in (root.resolve(), *root.resolve().parents) if a.name == "ledger" for b in NOT_TRIES]
    def benchmark(f):
        sits = f.parent.resolve() / f.name                     # the link itself, its directories resolved
        return any(p.is_relative_to(d) for p in (sits, f.resolve()) for d in fenced)
    return [f for f in root.glob(f"**/{name}" if recursive else name) if not benchmark(f)]
