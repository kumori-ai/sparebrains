"""Once a day, one ranged GET (the first byte) of a file a rung cannot run without; the answer goes to ledger/sources/<name>.jsonl so the daily
report says when an outside data source went away and when it came back (DECISIONS 2026-11-05: openproblems' bucket
answered 403 AllAccessDisabled from 11-05 and the only sign was a failed run's mail).

    python3 tools/source_probe.py            # every source in SOURCES, one row each
"""
import json, re, sys, urllib.error, urllib.request
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
# openproblems.py's S3 / DATASET / NORM / FILES[0], spelled out: that module imports numpy, which the retro job lacks.
# test_source_probe checks they still agree.
SOURCES = {"openproblems": "https://openproblems-data.s3.amazonaws.com/resources/task_predict_modality/datasets/"
                           "openproblems_neurips2021/bmmc_cite/normal/log_cp10k/train_mod1.h5ad"}
OUT = ROOT / "ledger" / "sources"


def probe(name, url, now, open_=urllib.request.urlopen, timeout=20):
    """{at, source, url, ok, status, code}: code is S3's <Code> on an error answer, or the failure's text."""
    row = {"at": now.isoformat(), "source": name, "url": url, "ok": False, "status": None, "code": None}
    try:
        # a ranged GET, not HEAD: a HEAD error has no body, so S3's <Code> (AllAccessDisabled, NoSuchKey) is lost
        req = urllib.request.Request(url, headers={"User-Agent": "sparebrains-source-probe", "Range": "bytes=0-0"})
        r = open_(req, timeout=timeout)
        row.update(ok=200 <= r.status < 300, status=r.status)
    except urllib.error.HTTPError as e:
        body = e.read()[:2000].decode(errors="replace") if hasattr(e, "read") else ""
        e.close()
        m = re.search(r"<Code>([^<]+)</Code>", body)
        row.update(status=e.code, code=m.group(1) if m else f"HTTP {e.code}")
    except (urllib.error.URLError, OSError) as e:
        row["code"] = f"{type(e).__name__}: {e}"[:200]
    return row


def state(rows):
    """The source's state from its rows in time order: {ok, at, code, down_since} while down, {ok, at, back_since,
    was_down_since} when the newest row is up after a failure, {ok, at} when it never failed; None with no rows."""
    if not rows:
        return None
    rows = sorted(rows, key=lambda r: r["at"])
    last = rows[-1]
    streak = []
    for r in reversed(rows):
        if r["ok"] != last["ok"]:
            break
        streak.append(r)
    first = streak[-1]
    if not last["ok"]:
        return {"ok": False, "at": last["at"], "code": last.get("code"), "down_since": first["at"]}
    before = rows[:len(rows) - len(streak)]
    if not before:
        return {"ok": True, "at": last["at"]}
    down = []
    for r in reversed(before):
        if r["ok"]:
            break
        down.append(r)
    return {"ok": True, "at": last["at"], "back_since": first["at"], "was_down_since": down[-1]["at"]}


def read(name, root=OUT):
    f = Path(root) / f"{name}.jsonl"
    return [json.loads(l) for l in f.read_text().splitlines() if l.strip()] if f.exists() else []


def record(name, out, now, open_=urllib.request.urlopen):
    row = probe(name, SOURCES[name], now, open_)
    out = Path(out)
    out.parent.mkdir(parents=True, exist_ok=True)
    with open(out, "a") as f:
        f.write(json.dumps(row) + "\n")
    return row


def main():
    now = datetime.now(timezone.utc).replace(microsecond=0)
    for name in SOURCES:
        row = record(name, OUT / f"{name}.jsonl", now)
        print(f"{name}: {'up' if row['ok'] else 'DOWN'} ({row['status']} {row['code'] or ''})".rstrip())
    return 0


if __name__ == "__main__":
    sys.exit(main())
