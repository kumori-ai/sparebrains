"""The TPU kernel's weight prefetch (2026-10-24): a pinned snapshot over HTTP in its own process, restarted when it
stalls, resumed from partial files, verified against the hub's manifest, before vLLM loads it offline. Real child
processes with tiny files and short clocks; no network."""
import json
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
import hf_prefetch

PY = sys.executable


def child(script):
    return lambda attempt: [PY, "-c", script.replace("ATTEMPT", str(attempt))]


class Prefetch(unittest.TestCase):
    def setUp(self):
        self.d = tempfile.TemporaryDirectory()
        self.dir = Path(self.d.name)
        self.beats = []

    def tearDown(self):
        self.d.cleanup()

    def run_it(self, script, **kw):
        return hf_prefetch.prefetch(child(script), self.dir, beat=lambda e, **k: self.beats.append((e, k)),
                                    poll_s=0.05, **{"stall_s": 0.6, "max_restarts": 2, **kw})

    def test_a_stalled_child_is_killed_and_restarted_and_a_partial_file_resumes(self):
        # attempt 0 writes half and hangs; attempt 1 finds the half and finishes
        script = ("import os, time\np = r'%s/w.bin'\nif ATTEMPT == 0:\n    open(p, 'wb').write(b'x' * 50)\n"
                  "    time.sleep(60)\nelse:\n    have = os.path.getsize(p)\n    open(p, 'ab').write(b'x' * (100 - have))\n"
                  % self.dir)
        ok, restarts, reason = self.run_it(script)
        self.assertEqual((ok, restarts), (True, 1), reason)
        self.assertEqual((self.dir / "w.bin").stat().st_size, 100)
        self.assertIn("restart", [e for e, _ in self.beats])

    def test_restarts_run_out_and_the_failure_says_why(self):
        ok, restarts, reason = self.run_it("import time\ntime.sleep(60)")
        self.assertEqual((ok, restarts), (False, 2))
        self.assertIn("no new bytes", reason)

    def test_a_child_that_exits_non_zero_is_restarted_too(self):
        # stall_s far above a Python start: under full-suite load a child took longer than 0.6 s to exit, was
        # killed as stalled, and the reason read "no new bytes" (flaked 2026-11-04); this test is about the exit
        ok, restarts, reason = self.run_it("import sys\nsys.exit(3)", max_restarts=1, stall_s=30)
        self.assertEqual((ok, restarts), (False, 1))
        self.assertIn("exit 3", reason)


class Manifest(unittest.TestCase):
    API = {"sha": "abc", "siblings": [{"rfilename": "model-00001-of-00002.safetensors", "size": 10},
                                      {"rfilename": "model-00002-of-00002.safetensors", "size": 20},
                                      {"rfilename": "config.json", "size": 3}, {"rfilename": "README.md", "size": 9},
                                      {"rfilename": "tokenizer.json", "size": 4}]}

    def test_the_manifest_is_the_pinned_revision_and_only_what_vllm_loads(self):
        asked = []
        m = hf_prefetch.manifest("o/m", "abc", fetch=lambda url: asked.append(url) or json.dumps(self.API))
        self.assertIn("/revision/abc", asked[0])
        self.assertEqual(sorted(m), ["config.json", "model-00001-of-00002.safetensors",
                                     "model-00002-of-00002.safetensors", "tokenizer.json"])

    def test_verify_names_missing_and_short_files(self):
        with tempfile.TemporaryDirectory() as d:
            (Path(d) / "config.json").write_bytes(b"abc")
            (Path(d) / "model-00001-of-00002.safetensors").write_bytes(b"x" * 9)
            m = {"config.json": 3, "model-00001-of-00002.safetensors": 10, "tokenizer.json": 4}
            self.assertEqual(hf_prefetch.verify(Path(d), m),
                             ["model-00001-of-00002.safetensors: 9 of 10 bytes", "tokenizer.json: missing"])

    def test_manifest_beats_stay_under_ntfys_size_and_lose_nothing(self):
        m = {f"model-{i:05d}-of-00099.safetensors": 4_900_000_000 + i for i in range(99)}
        parts = hf_prefetch.parts(m)
        self.assertTrue(all(len(json.dumps(p)) < 3000 for p in parts))
        self.assertEqual({k: v for p in parts for k, v in p["files"].items()}, m)
        self.assertEqual([p["part"] for p in parts], list(range(1, len(parts) + 1)))


class Mounted(unittest.TestCase):
    """The 32B loads a mounted Kaggle mirror, hash-checked against the pinned hub revision (2026-11-25, #534): four of
    four 32B batches died reading the venv in /tmp after the 65 GB download landed beside it."""
    API = {"siblings": [
        {"rfilename": "model-00001-of-00001.safetensors", "size": 5,
         "lfs": {"sha256": "2cf24dba5fb0a30e26e83b2ac5b9e29e1b161e5c1fa7425e73043362938b9824"}},   # sha256(b"hello")
        {"rfilename": "config.json", "size": 2, "blobId": "9e26dfeeb6e641a33dae4961196235bdb965b21b"},   # git blob of b"{}"
        {"rfilename": "README.md", "size": 1, "blobId": "x"}]}

    def setUp(self):
        self.d = tempfile.TemporaryDirectory()
        self.root = Path(self.d.name)

    def tearDown(self):
        self.d.cleanup()

    def mirror(self, at, weights=b"hello"):
        p = self.root / at
        p.mkdir(parents=True)
        (p / "model-00001-of-00001.safetensors").write_bytes(weights)
        (p / "config.json").write_bytes(b"{}")
        return p

    def test_hashes_are_the_pinned_revisions_lfs_sha256_or_git_blob_sha1_for_what_vllm_loads(self):
        asked = []
        h = hf_prefetch.hashes("o/m", "abc", fetch=lambda url: asked.append(url) or json.dumps(self.API))
        self.assertIn("/revision/abc?blobs=true", asked[0])
        self.assertEqual(h, {"model-00001-of-00001.safetensors": ("sha256", self.API["siblings"][0]["lfs"]["sha256"]),
                             "config.json": ("gitsha1", "9e26dfeeb6e641a33dae4961196235bdb965b21b")})

    def test_a_matching_mirror_passes_and_one_changed_byte_fails(self):
        h = hf_prefetch.hashes("o/m", "abc", fetch=lambda url: json.dumps(self.API))
        good = self.mirror("good")
        self.assertEqual(hf_prefetch.verify_hashes(good, h, expect=h), [])
        bad = self.mirror("bad", weights=b"hellp")              # same size, one byte off: a size check would pass it
        self.assertEqual(hf_prefetch.verify_hashes(bad, h, expect=h), ["model-00001-of-00001.safetensors: sha256 differs"])
        (good / "config.json").unlink()
        self.assertEqual(hf_prefetch.verify_hashes(good, h, expect=h), ["config.json: missing"])

    def test_the_mounted_copy_is_found_by_its_manifest_wherever_kaggle_mounts_it(self):
        man = {"model-00001-of-00001.safetensors": 5, "config.json": 2}
        self.mirror("other-model/transformers/8b/1", weights=b"hi")              # a config.json, wrong sizes
        want = self.mirror("goedel-prover-v2/transformers/32b/1")
        self.assertEqual(hf_prefetch.find_mounted(man, roots=(self.root,)), str(want))
        self.assertIsNone(hf_prefetch.find_mounted(man, roots=(self.root / "nowhere",)))

    def test_empty_or_partial_metadata_never_passes(self):
        # Codex 20261125T182811031376Z f1: {} from the hub gave manifest {}, hashes {}, found, bad [] (fail open)
        self.mirror("m")
        self.assertIsNone(hf_prefetch.find_mounted({}, roots=(self.root,)))
        self.assertTrue(hf_prefetch.verify_hashes(self.root / "m", {}, expect={"config.json": 2}))
        h = hf_prefetch.hashes("o/m", "abc", fetch=lambda url: json.dumps(self.API))
        h.pop("config.json")
        self.assertTrue(hf_prefetch.verify_hashes(self.root / "m", h,
                                                  expect={"config.json": 2, "model-00001-of-00001.safetensors": 5}))

    def test_only_the_32b_has_a_mirror_and_it_names_a_kaggle_model_source(self):
        self.assertEqual(set(hf_prefetch.MIRRORS), {"Goedel-LM/Goedel-Prover-V2-32B"})
        self.assertEqual(len(hf_prefetch.MIRRORS["Goedel-LM/Goedel-Prover-V2-32B"].split("/")), 5)   # owner/model/framework/instance/version


class Robustness(unittest.TestCase):
    """Codex 20261024T195435827483Z f3: a partial file renamed mid-scan must not crash the watchdog, and a watchdog
    that fails for any reason leaves no download child running."""

    def test_a_file_gone_between_listing_and_stat_is_skipped(self):
        with tempfile.TemporaryDirectory() as d:
            (Path(d) / "a").write_bytes(b"xx")
            ghost = Path(d) / "renamed.incomplete"
            from unittest import mock
            with mock.patch.object(Path, "rglob", lambda self, pat: iter([Path(d) / "a", ghost])), \
                    mock.patch.object(Path, "is_file", lambda self: True):      # listed as a file, gone by its stat
                self.assertEqual(hf_prefetch.dir_bytes(d), 2)

    def test_the_child_is_reaped_when_the_watchdog_raises(self):
        with tempfile.TemporaryDirectory() as d:
            procs = []
            def popen(cmd, env=None):
                import subprocess
                p = subprocess.Popen([PY, "-c", "import time; time.sleep(60)"])
                procs.append(p)
                return p
            calls = [0]
            def now():
                calls[0] += 1
                if calls[0] > 2:
                    raise OSError("clock broke")
                return 0.0
            with self.assertRaises(OSError):
                hf_prefetch.prefetch(lambda a: ["x"], Path(d), poll_s=0.01, popen=popen, now=now)
            self.assertIsNotNone(procs[0].poll(), "the download child was killed")
