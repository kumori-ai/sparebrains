"""The weekly retro (Kumori task #460): where the swarm got stuck last week, read from the ledger alone.

For the last closed ISO week (Monday to Sunday, UTC): tries and accepts by mode, the first-time solves (a target's
first accept ever), and the loop's stop reasons beside the week before, with the one that grew most. It writes
ledger/retro/<year>-W<week>.md once; a rerun writes the same bytes, so publishing it twice changes nothing. It is a
file in our own repository, not a GitHub issue (an issue is Andy's call, each time).

    python3 tools/retro.py                      # the last closed week, if its page is not there yet
    python3 tools/retro.py --today 2026-10-22   # as if run that day
"""
import argparse, json, sys
import ledger_files
from collections import Counter, defaultdict
from datetime import date, datetime, timedelta
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
TOP_STOPS = 10


def last_closed_week(today):
    """The ISO (year, week) of the week that ended before `today` (YYYY-MM-DD)."""
    d = date.fromisoformat(today)
    return tuple((d - timedelta(days=d.isoweekday())).isocalendar()[:2])


def week_of(ts):
    return tuple(datetime.fromisoformat(ts).isocalendar()[:2])


def load(ledger):
    """Every ledger row that is a try: it has a time, a target, a mode and a verdict. Other files are skipped."""
    rows = []
    for f in sorted(ledger_files.try_files(ledger)):
        for line in f.read_text().splitlines():
            try:
                r = json.loads(line)
            except ValueError:
                continue
            if isinstance(r, dict) and all(r.get(k) for k in ("ts", "target", "mode", "verdict")):
                rows.append(r)
    return rows


def summarize(rows, week):
    prev = week_of((date.fromisocalendar(*week, 1) - timedelta(days=7)).isoformat())
    modes, first, stops, before = defaultdict(lambda: [0, 0]), {}, Counter(), Counter()
    for r in sorted(rows, key=lambda r: r["ts"]):
        w, key = week_of(r["ts"]), (r.get("target_set") or "", r["target"])
        if r["verdict"] == "accept" and key not in first:
            first[key] = (w, r["mode"])
        if w == week and r["verdict"] != "skipped":
            modes[r["mode"]][0] += 1
            modes[r["mode"]][1] += r["verdict"] == "accept"
        stopped = ((r.get("tools") or {}).get("subgoals") or {}).get("stopped")   # the loop's own reason
        if stopped:
            (stops if w == week else before if w == prev else Counter())[stopped] += 1
    top = sorted(stops, key=lambda s: (-stops[s], s))[:TOP_STOPS]
    growth = {s: stops[s] - before[s] for s in top if stops[s] > before[s]}
    return {"week": week, "modes": dict(modes),
            "first_time": sorted((k[0], k[1], m) for k, (w, m) in first.items() if w == week),
            "stops": [(s, stops[s], before[s]) for s in top],
            "grew": max(growth, key=lambda s: (growth[s], s)) if growth else None}


def render(s):
    y, w = s["week"]
    mon = date.fromisocalendar(y, w, 1)
    out = [f"# Retro {y}-W{w:02d} ({mon} to {mon + timedelta(days=6)})", "",
           "Read from the ledger by tools/retro.py. A try is any judged answer; skipped ones are not counted.", "",
           "## Tries and accepts by mode", "", "| mode | tries | accepts |", "|---|---:|---:|"]
    out += [f"| {m} | {t:,} | {a:,} |" for m, (t, a) in sorted(s["modes"].items(), key=lambda x: (-x[1][0], x[0]))]
    out += ["", f"## First-time solves: {len(s['first_time'])}", ""]
    out += [f"- {ts} {t} ({m})" for ts, t, m in s["first_time"]] or ["None this week."]
    out += ["", "## Where the loop stopped", "", "| stop reason | this week | week before |", "|---|---:|---:|"]
    out += [f"| {r} | {n:,} | {b:,} |" for r, n, b in s["stops"]]
    out += ["", f"Grew most: {s['grew']}." if s["grew"] else "No stop reason grew.", ""]
    return "\n".join(out)


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--ledger", default=str(ROOT / "ledger"))
    ap.add_argument("--out", default=str(ROOT / "ledger" / "retro"))
    ap.add_argument("--today", default=date.today().isoformat())
    a = ap.parse_args(argv)
    rows = load(a.ledger)
    if not rows:
        sys.exit(f"no ledger rows under {a.ledger}: a retro of nothing would read as a quiet week")
    s = summarize(rows, last_closed_week(a.today))
    page = Path(a.out) / f"{s['week'][0]}-W{s['week'][1]:02d}.md"
    if page.exists():
        print(f"{page.name} already written")
        return 0
    page.parent.mkdir(parents=True, exist_ok=True)
    page.write_text(render(s))
    shown = page.resolve().relative_to(ROOT) if page.resolve().is_relative_to(ROOT) else page   # the commit message's
    print(f"wrote {shown}: {sum(t for t, _ in s['modes'].values()):,} tries, {len(s['first_time'])} first-time solves")
    return 0


if __name__ == "__main__":
    sys.exit(main())
