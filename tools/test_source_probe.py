"""tools/source_probe.py: once a day, one ranged GET of a file a rung cannot run without, its answer kept in the ledger, so
the daily report says when an outside data source went away and when it came back. 2026-11-05: openproblems' bucket
answered 403 AllAccessDisabled and the only sign was a failed run's mail. No network: the opener is faked."""
import io
import json
import sys
import tempfile
import unittest
import urllib.error
from datetime import datetime, timezone
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
import source_probe

NOW = datetime(2026, 11, 6, 6, 40, tzinfo=timezone.utc)
DISABLED = (b'<?xml version="1.0" encoding="UTF-8"?>\n<Error><Code>AllAccessDisabled</Code>'
            b'<Message>All access to this object has been disabled.</Message></Error>')


def opener(status=200, body=b""):
    def go(req, timeout):
        if status not in (200, 206):
            raise urllib.error.HTTPError(req.full_url, status, "Forbidden", {}, io.BytesIO(body))
        class R:
            pass
        r = R()
        r.status = status
        return r
    return go


class Probe(unittest.TestCase):
    def test_a_disabled_bucket_is_down_with_its_code(self):
        row = source_probe.probe("openproblems", "https://x/y.h5ad", NOW, open_=opener(403, DISABLED))
        self.assertEqual((row["ok"], row["status"], row["code"]), (False, 403, "AllAccessDisabled"))
        self.assertEqual(row["at"], NOW.isoformat())

    def test_it_asks_for_one_byte_so_an_error_body_comes_back(self):
        seen = {}
        def go(req, timeout):
            seen.update(method=req.get_method(), range=req.get_header("Range"))
            return opener(200)(req, timeout)
        source_probe.probe("openproblems", "https://x/y.h5ad", NOW, open_=go)
        self.assertEqual(seen, {"method": "GET", "range": "bytes=0-0"})

    def test_a_200_is_up(self):
        row = source_probe.probe("openproblems", "https://x/y.h5ad", NOW, open_=opener(200))
        self.assertEqual((row["ok"], row["status"], row["code"]), (True, 200, None))

    def test_a_network_failure_is_down_not_a_crash(self):
        def fail(req, timeout):
            raise urllib.error.URLError("dns")
        row = source_probe.probe("openproblems", "https://x/y.h5ad", NOW, open_=fail)
        self.assertEqual((row["ok"], row["status"]), (False, None))
        self.assertIn("dns", row["code"])


class State(unittest.TestCase):
    def rows(self, *oks):
        return [{"at": f"2026-11-0{i + 1}T06:40:00+00:00", "ok": ok, "status": 200 if ok else 403,
                 "code": None if ok else "AllAccessDisabled"} for i, ok in enumerate(oks)]

    def test_down_since_the_first_failure_of_the_current_streak(self):
        s = source_probe.state(self.rows(True, False, False))
        self.assertEqual((s["ok"], s["down_since"], s["code"]), (False, "2026-11-02T06:40:00+00:00", "AllAccessDisabled"))

    def test_back_after_an_outage_says_so(self):
        s = source_probe.state(self.rows(False, False, True))
        self.assertEqual((s["ok"], s["back_since"], s["was_down_since"]),
                         (True, "2026-11-03T06:40:00+00:00", "2026-11-01T06:40:00+00:00"))

    def test_never_probed_is_none(self):
        self.assertIsNone(source_probe.state([]))


class Url(unittest.TestCase):
    def test_the_probed_file_is_the_one_openproblems_downloads_first(self):
        import openproblems as op
        self.assertEqual(source_probe.SOURCES["openproblems"], f"{op.S3}/datasets/{op.DATASET}/{op.NORM}/{op.FILES[0]}.h5ad")


class Cli(unittest.TestCase):
    def test_rows_append_to_the_sources_ledger(self):
        with tempfile.TemporaryDirectory() as d:
            out = Path(d) / "sources" / "openproblems.jsonl"
            for _ in range(2):
                source_probe.record("openproblems", out, NOW, open_=opener(403, DISABLED))
            rows = [json.loads(l) for l in out.read_text().splitlines()]
            self.assertEqual(len(rows), 2)
            self.assertEqual(rows[0]["code"], "AllAccessDisabled")


if __name__ == "__main__":
    unittest.main()
