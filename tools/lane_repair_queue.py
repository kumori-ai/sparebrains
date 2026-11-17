"""Append-only repair requests. Workflow workers serialize; enqueue jobs never wait on that lock."""
import argparse
import base64
import json
import math
import os
import re
import subprocess
import sys
import time
from pathlib import Path

MAX_AGE = 7 * 86400
MAX_CHECKS, MAX_ATTEMPTS = 96, 12
RECHECK = 900
STALE = 340 * 60 + 3600     # the worker job's timeout plus an hour: past this an admitted or started request is stranded
CLASSES = {"unknown_name", "lean3_syntax", "unsolved_goals"}
ROOT = Path(__file__).resolve().parent.parent
QUEUE = ROOT / "ledger" / "lane-repair-requests"


def read(path):
    return [json.loads(line) for line in Path(path).read_text().splitlines() if line.strip()]


def state(events):
    first = events[0]
    if first["event"] != "requested":
        raise ValueError("request has no immutable configuration")
    s = {**first, "status": "queued", "remaining": first["rounds"], "due": first["at"],
         "checks": 0, "attempts": 0, "since": first["at"]}
    for e in events[1:]:
        s["since"] = e["at"]
        if e["event"] in ("deferred", "blocked", "admitted"):
            if s["status"] not in ("queued", "deferred", "admitted"):
                raise ValueError("cannot defer a running or terminal request")
            s.update(status=e["event"], due=e.get("due"), checks=s["checks"] + 1)
        elif e["event"] == "started":
            if s["status"] not in ("queued", "deferred", "admitted") or e["reserved"] != s["remaining"]:
                raise ValueError("invalid or overlapping reservation")
            s.update(status="started", remaining=0, reserved=e["reserved"], attempt=e["attempt"],
                     attempts=s["attempts"] + 1)
        elif e["event"] == "finished":
            if s["status"] != "started" or s["attempt"] != e["attempt"]:
                raise ValueError("completion has no matching reservation")
            used = e["used"]
            if type(used) is not int or not 0 <= used <= s["reserved"]:
                raise ValueError("completion exceeds original budget")
            s.update(status=e["status"], remaining=s["reserved"] - used, due=e.get("due"))
        else:
            raise ValueError("unknown request event")
    return s


def append(path, event):
    # Validate the whole transition before persisting even one byte.
    state(read(path) + [event])
    with Path(path).open("a") as fh:
        fh.write(json.dumps(event, sort_keys=True) + "\n")


def enqueue(root, request, cls, lanes, rounds, now):
    lanes = [lane.strip() for lane in lanes.split(",")]
    if (not re.fullmatch(r"[0-9]+", request) or cls not in CLASSES
            or type(rounds) is not int or not 1 <= rounds <= 12
            or not lanes or len(lanes) > 16
            or any(not re.fullmatch(r"[a-zA-Z0-9_.-]+", lane) for lane in lanes)
            or len(set(lanes)) != len(lanes)):
        raise ValueError("invalid repair request")
    config = {"request": request, "class": cls, "lanes": lanes, "rounds": rounds}
    path = Path(root) / f"{request}.jsonl"
    if path.exists():
        old = read(path)[0]
        if any(old[k] != v for k, v in config.items()):
            raise ValueError("existing request configuration is immutable")
        return path
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("x") as fh:
        fh.write(json.dumps({**config, "event": "requested", "at": now}, sort_keys=True) + "\n")
    return path


def public(decision):
    """The three fields of an admission answer that go in the ledger, which is a public repo: never the answer whole
    (other tenants' usage, account details)."""
    if type(decision.get("eligible_now")) is not bool:
        raise ValueError("admission missing boolean eligible_now")
    out = {"eligible_now": decision["eligible_now"]}
    if decision.get("reason") is not None:
        out["reason"] = str(decision["reason"])[:200]
    when = decision.get("next_check_at")
    if type(when) in (int, float) and math.isfinite(when):
        out["next_check_at"] = when
    return out


UNMETERED = ("unknown_backend", "unsupported_budget")


def router_admission(client=None):
    """admission(lane, need) from Kumori's GET /api/v1/llm/admission (contract: kumori ma965666b533, 2026-11-17): a
    snapshot of the recorded daily call budget, no reservation and no model call, so the router's own gate still
    decides each ask. An answer about another lane, app or call count is refused, never read as room."""
    if client is None:
        from utilities import kumori_api_client as client
    if not hasattr(client, "llm_admission"):
        raise RuntimeError("canonical admission adapter is not yet installed")
    client.init()

    def admission(lane, need):
        r = client.llm_admission(lane, need, app_name="sparebrains")
        if (r.get("ok") is not True or r.get("backend") != lane or r.get("max_calls") != need
                or r.get("app_name") != "sparebrains"):
            raise ValueError("admission answer is not for this request")
        return r
    return admission


def select(root, admission, now):
    """Admission adapter returns eligible_now, reason, and a Unix next_check_at. No model calls here."""
    requests = []
    for path in Path(root).glob("*.jsonl"):
        try:        # one unreadable file (a hand edit, a recovered artifact) must not stop every other request
            requests.append((path, state(read(path))))
        except Exception as exc:
            print(f"::warning::{path.name} is unreadable and needs review: {type(exc).__name__}", flush=True)
    for path, s in sorted(requests, key=lambda pair: (pair[1]["at"], pair[1]["request"])):
        # Workers run one at a time, so a request still admitted or started after a whole job's time has no worker.
        if s["status"] == "admitted" and now - s["since"] >= STALE:
            append(path, {"event": "blocked", "at": now, "reason": "admitted but never started; needs review"})
        elif s["status"] == "started" and now - s["since"] >= STALE:
            finish(path, s["attempt"], [], now, success=False)
        if s["status"] not in ("queued", "deferred"):
            continue
        if now - s["at"] >= MAX_AGE or s["checks"] >= MAX_CHECKS or s["attempts"] >= MAX_ATTEMPTS:
            append(path, {"event": "blocked", "at": now, "reason": "retry bound reached; needs review"})
            continue
        if now < s["due"]:
            continue
        eligible, decisions = [], {}
        for lane in s["lanes"]:
            try:
                decision = public(admission(lane, s["remaining"]))
            except Exception as exc:
                decision = {"eligible_now": False, "reason": f"admission unavailable: {type(exc).__name__}",
                            "next_check_at": now + RECHECK}
            decisions[lane] = decision
            if decision["eligible_now"]:
                eligible.append(lane)
        if eligible:
            # Persist ownership before setup too: a setup crash must not cause repeated expensive rebuilds.
            append(path, {"event": "admitted", "at": now, "admission": decisions})
            return {**s, "path": str(path), "lanes": eligible, "admission": decisions}
        if all(d.get("reason") in UNMETERED for d in decisions.values()):
            # The router cannot answer for any of these lanes: rechecking would only spin (kumori ma965666b533).
            append(path, {"event": "blocked", "at": now, "reason": "no requested lane has an admission meter; needs review",
                          "admission": decisions})
            continue
        due = []
        for decision in decisions.values():
            when = decision.get("next_check_at")
            if isinstance(when, (int, float)) and math.isfinite(when) and when > now:
                due.append(when)
        append(path, {"event": "deferred", "at": now, "due": max(now + RECHECK, min(due)) if due else now + RECHECK,
                      "admission": decisions})
    return None


def start(path, attempt, lanes, now):
    s = state(read(path))
    if (not re.fullmatch(r"[0-9]+-[0-9]+", attempt) or not lanes
            or any(lane not in s["lanes"] for lane in lanes)):
        raise ValueError("attempt or authorized writer list is invalid")
    append(path, {"event": "started", "at": now, "attempt": attempt, "lanes": lanes,
                  "reserved": s["remaining"]})


def finish(path, attempt, rows, now, success=True):
    s = state(read(path))
    if s["status"] != "started" or attempt != s["attempt"]:
        raise ValueError("attempt has no outstanding reservation")
    # An interrupted process may have made a call without writing its row. Do not refund unknown use.
    if not success or not rows:
        used, status = s["reserved"], "interrupted"
    else:
        used = 0
        for row in rows:
            if row.get("writer") is not None:
                repairs = row.get("repair_asks", 0)
                if type(repairs) is not int or repairs < 0:
                    raise ValueError("invalid consumed ask count")
                used += 1 + repairs
        quota = any(row.get("refused") or row.get("repair_refused") for row in rows)
        status = "deferred" if quota and used < s["reserved"] else "complete"
    append(path, {"event": "finished", "at": now, "attempt": attempt, "used": used, "status": status,
                  "due": now + RECHECK if status == "deferred" else None})


def release(path, attempt, now):
    """A reservation whose model step never started (the reserve step itself failed): nothing was asked, so nothing
    is recorded as spent, and the request stops for review instead of retrying."""
    s = state(read(path))
    if s["status"] != "started" or attempt != s["attempt"]:
        raise ValueError("attempt has no outstanding reservation")
    append(path, {"event": "finished", "at": now, "attempt": attempt, "used": 0, "status": "blocked",
                  "reason": "reserved but the model step never ran; needs review"})


def publish_events(message):
    """Use the existing race-safe publisher. Push credentials exist only in this trusted step's environment."""
    import publish
    token = os.environ["GH_TOKEN"]
    header = "AUTHORIZATION: basic " + base64.b64encode(f"x-access-token:{token}".encode()).decode()
    values = {"GIT_CONFIG_COUNT": "1", "GIT_CONFIG_KEY_0": "http.https://github.com/.extraheader",
              "GIT_CONFIG_VALUE_0": header, "GIT_AUTHOR_NAME": "sparebrains-bot",
              "GIT_COMMITTER_NAME": "sparebrains-bot", "GIT_AUTHOR_EMAIL": "sparebrains-bot@users.noreply.github.com",
              "GIT_COMMITTER_EMAIL": "sparebrains-bot@users.noreply.github.com"}
    old = {k: os.environ.get(k) for k in values}
    try:
        os.environ.update(values)
        return publish.publish(ROOT, message)
    finally:
        for key, value in old.items():
            if value is None:
                os.environ.pop(key, None)
            else:
                os.environ[key] = value


def selection(path):
    s = json.loads(Path(path).read_text())
    request = s["request"]
    if not re.fullmatch(r"[0-9]+", request):
        raise ValueError("invalid request ID")
    # Never trust a serialized arbitrary path, even one written by our own earlier step.
    s["path"] = str(QUEUE / f"{request}.jsonl")
    current = state(read(s["path"]))
    if (s["class"] != current["class"] or any(lane not in current["lanes"] for lane in s["lanes"])
            or type(s["remaining"]) is not int or not 1 <= s["remaining"] <= current["rounds"]):
        raise ValueError("selection disagrees with immutable request")
    return s


def output_file(s, attempt):
    if not re.fullmatch(r"[0-9]+-[0-9]+", attempt):
        raise ValueError("invalid attempt ID")
    return ROOT / "ledger" / "lane-repair" / f"{s['class']}-request-{s['request']}-{attempt}.jsonl"


def main(argv=None, admission=None):
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("command", choices=("enqueue", "select", "start", "run", "finish", "abort", "publish"))
    ap.add_argument("--selection", default=os.environ.get("RUNNER_TEMP", ".") + "/repair-selection.json")
    ap.add_argument("--attempt", default=f"{os.environ.get('GITHUB_RUN_ID', '')}-{os.environ.get('GITHUB_RUN_ATTEMPT', '')}")
    ap.add_argument("--success", action="store_true")
    a = ap.parse_args(argv)
    now = int(time.time())
    if a.command == "enqueue":
        path = enqueue(QUEUE, os.environ["GITHUB_RUN_ID"], os.environ["INPUT_CLASS"],
                       os.environ["INPUT_LANES"], int(os.environ["INPUT_ROUNDS"]), now)
        publish_events(f"Queue repair request {path.stem}")
        return 0
    if a.command == "publish":
        publish_events(f"Repair request events from {os.environ['GITHUB_RUN_ID']}")
        return 0
    if a.command == "select":
        if admission is None:
            sys.path.insert(0, str(ROOT))
            admission = router_admission()
        selected = select(QUEUE, admission, now)
        publish_events(f"Repair admission checks {os.environ['GITHUB_RUN_ID']}")
        if selected:
            Path(a.selection).write_text(json.dumps(selected) + "\n")
        with open(os.environ["GITHUB_OUTPUT"], "a") as fh:
            fh.write(f"ready={'true' if selected else 'false'}\n")
        return 0
    s = selection(a.selection)
    path, out = Path(s["path"]), output_file(s, a.attempt)
    if a.command == "start":
        if state(read(path))["remaining"] != s["remaining"]:
            raise ValueError("selection has a stale ask budget")
        start(path, a.attempt, s["lanes"], now)
        publish_events(f"Reserve {s['remaining']} asks for repair request {s['request']}, attempt {a.attempt}")
    elif a.command == "run":
        current = state(read(path))
        if current["status"] != "started" or current["attempt"] != a.attempt:
            raise ValueError("no matching durable reservation")
        if out.exists():
            raise ValueError("attempt already has output; refusing to replay it")
        return subprocess.run([sys.executable, str(ROOT / "tools" / "lane_repair.py"),
                               "--class", s["class"], "--lanes", ",".join(s["lanes"]),
                               "--rounds", str(s["remaining"]), "--out", str(out)], check=False).returncode
    elif a.command == "finish":
        rows = read(out) if out.exists() else []
        finish(path, a.attempt, rows, now, success=a.success)
        current = state(read(path))
        print(f"request {s['request']}: {current['status']}; {current['remaining']} asks unspent")
    elif a.command == "abort":
        current = state(read(path))
        if current["status"] == "admitted":
            append(path, {"event": "blocked", "at": now, "reason": "setup failed or was canceled; needs review"})
        elif current["status"] == "started" and current["attempt"] == a.attempt:
            if out.exists():        # abort runs only when the reserve step failed, so the model step never ran
                raise ValueError("attempt has output; its use is not known to be zero")
            release(path, a.attempt, now)
    return 0


if __name__ == "__main__":
    sys.exit(main())
