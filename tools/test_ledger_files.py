"""tools/ledger_files.py: every reader of the ledger's try rows skips the benchmark rows under ledger/speed/ (task #191),
so a speed re-solve never retires a ladder cell, owes a prover sample, or counts in the retro."""
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
import ledger_files


class LedgerFiles(unittest.TestCase):
    def test_try_rows_skip_the_speed_benchmark_and_keep_everything_else(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            for p in ("minif2f/test/1.jsonl", "mil/2.jsonl", "speed/run-3.jsonl", "speed/x/4.jsonl", "speedy/5.jsonl",
                      "prover-beats/tpu-20261023T0100.jsonl"):
                (root / p).parent.mkdir(parents=True, exist_ok=True)
                (root / p).write_text("{}\n")
            got = sorted(str(f.relative_to(root)) for f in ledger_files.try_files(root))
            self.assertEqual(got, ["mil/2.jsonl", "minif2f/test/1.jsonl", "speedy/5.jsonl"])

    def test_a_root_inside_a_benchmark_or_a_link_into_one_is_still_left_out(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d) / "ledger"
            (root / "speed").mkdir(parents=True)
            (root / "speed" / "run-1.jsonl").write_text("{}\n")
            (root / "minif2f").mkdir()
            (root / "minif2f" / "link.jsonl").symlink_to(root / "speed" / "run-1.jsonl")
            self.assertEqual(ledger_files.try_files(root / "speed"), [])          # retro --ledger ledger/speed
            self.assertEqual(ledger_files.try_files(root), [])                    # the link resolves into speed/
            (Path(d) / "elsewhere.jsonl").write_text("{}\n")
            (root / "speed" / "out.jsonl").symlink_to(Path(d) / "elsewhere.jsonl")
            self.assertEqual(ledger_files.try_files(root), [])                    # a link out of speed/ is speed's
            self.assertEqual(ledger_files.try_files(root / "minif2f", recursive=False), [])   # one directory, too

    def test_one_directory_only_when_not_recursive(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            (root / "sub").mkdir()
            (root / "a.jsonl").write_text("{}\n")
            (root / "sub" / "b.jsonl").write_text("{}\n")
            self.assertEqual([f.name for f in ledger_files.try_files(root, recursive=False)], ["a.jsonl"])

    def test_speed_is_reserved_as_a_target_set_name(self):
        targets = Path(__file__).resolve().parent.parent / "targets"
        self.assertFalse(any(p.name in ledger_files.NOT_TRIES for p in targets.iterdir()),
                         "a target set named like a benchmark directory would have its tries hidden")

    def test_every_recursive_ledger_reader_goes_through_it(self):
        import re
        tools = Path(__file__).parent
        bad = re.compile(r"""\.rglob\(\s*f?["'][^"']*jsonl|\.glob\(\s*f?["']\*\*/[^"']*jsonl""")   # any quoting
        for f in sorted(tools.glob("*.py")):
            if f.name.startswith("test_") or f.name == "ledger_files.py":
                continue
            for n, line in enumerate(f.read_text().splitlines(), 1):
                self.assertIsNone(bad.search(line), f"{f.name}:{n} walks the ledger itself: use ledger_files.try_files")


if __name__ == "__main__":
    unittest.main()
