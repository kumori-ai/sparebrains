"""The top of the daily report: what changed since the prior week of reports, as wins, losses, what to fix and ideas,
each carrying its own numbers, plus a headline and preheader for kumori's morning mail (subject and preview text).
Fixed rules over the report JSON, no model: a line is in here only because a number crossed a threshold below.

Thresholds are Claude's call of 2026-11-05, set against the 2026-10-28..11-05 reports (accept rate 15-29%, loss
before the kernel 23-34% every day from 10-29); re-tune them with receipts when the spread moves.
"""
from collections import defaultdict
from datetime import date, timedelta
from statistics import median

RATE_BAND = 5            # points off the week's median accept rate before it is a win or a loss
MIN_ANSWERED = 100       # a day with fewer answered tries reads too noisy to compare
LOST_FIX = 0.20          # share of judged tries lost before the kernel that earns a fix line
RESCUE_FLOOR = 0.10      # edge-cut rescues saving under this share, over at least RESCUE_MIN tries, is a fix
RESCUE_MIN = 20
IDLE_FIX_DAYS = 7        # a side rung idle this long is a fix; the ladder itself gets LADDER_IDLE_DAYS
LADDER_IDLE_DAYS = 1
CRASH_FIX = 0.40         # openproblems rounds crashing at this share of all rounds
LIFT_PTS = 10            # tool-lift move in points, both weeks with at least LIFT_MIN targets
LIFT_MIN = 10
COMPARABLE = 0.6         # the smaller week must have tried at least this share of the larger week's problems
BEST_MIN = 10            # answered tries before a lane can be named the day's most-accepts lane
HISTORY_DAYS = 7
# Rungs stopped on purpose: never a fix to restart, never a daily line. Take one off this list when it runs again.
RETIRED = {"goal batches (GPU)": "retired 2026-11-02: its bar (3 first-time solves in 7 days) was missed with 1, and the Kaggle "
                          "GPU went back to whole problems (DECISIONS.md, kumori #461)"}
HEADLINE_MAX = 70        # kumori prefixes "sparebrAIns: "; past this the optional parts drop, least important first


def _pct(a, b):
    return round(100 * a / b) if b else 0


def _lost(t):
    return sum((t.get("errors") or {}).values())


def _comparable(s):
    """2026-11-05: ministral-8b's '34% to 6%' was 18 problems against 44, kumori's pacing having dropped the lane."""
    lo, hi = sorted((s.get("targets", 0), s.get("prev_targets", 0)))
    return hi == 0 or lo / hi >= COMPARABLE


def _lift(s):
    """(this week %, week before %) for a speed row both of whose weeks are big enough to compare, else None."""
    if not s.get("prev_week") or s.get("targets", 0) < LIFT_MIN or s.get("prev_targets", 0) < LIFT_MIN:
        return None
    if not _comparable(s):
        return None
    return _pct(s["accepted"], s["targets"]), _pct(s["prev_accepted"], s["prev_targets"])


def _footing(r):
    """(accepted, answered, footing) for a report's accept rate. Off the no-model baseline when the report carries that
    read, and then the footing is that baseline's run id; else None, the totals. Since 2026-11-09 the ladder sets aside
    the targets Lean's automation proves (83% of the accepts until then): the 11-11 and 11-12 reports read 5% (12/240)
    and 4% (27/660) as losses against a 28% median of days that still tried them, while the rate off them, by UTC day,
    had been 1.9-8.6% from 10-29 to 11-06. A report is only compared with reports on its own footing, and a new
    baseline is a new footing (Codex 20261112T192728170594Z f2)."""
    ob = r.get("off_baseline") or {}
    if "answered_off" in ob:
        return ob["accepted_off"], ob["answered_off"], ob.get("baseline") or "?"
    return r["totals"]["accepted"], r["totals"].get("answered", 0), None


def brief(d, history):
    """d is today's report JSON; history the earlier reports' JSON, any order. Returns the brief dict."""
    t = d["totals"]
    prior = sorted((h for h in history if h.get("day", "") < d["day"]), key=lambda h: h["day"])[-HISTORY_DAYS:]
    wins, losses, fixes, ideas, head = [], [], [], [], []

    firsts = d.get("first_solves") or []
    head.append(f"{len(firsts)} first-time solve{'s' if len(firsts) != 1 else ''}" if firsts else "0 new solves")
    for f in firsts:
        wins.append(f"First-time solve: `{f['key']}` by {f['lane']}.")

    accepted, answered, off = _footing(d)
    rate = _pct(accepted, answered)
    rates = [_pct(a, n) for a, n, o in map(_footing, prior) if o == off and n >= MIN_ANSWERED]
    rate_head = f"accept rate {rate}%" + (" off baseline" if off else "")
    if rates and answered >= MIN_ANSWERED:
        med = round(median(rates))
        line = (f"accept rate {'off the no-model baseline ' if off else ''}{rate}% ({accepted}/{answered}) against a "
                f"{med}% median over the last {len(rates)} reports.")
        if rate - med >= RATE_BAND:
            wins.append("Higher " + line)
            rate_head += f" (week {med}%)"
        elif med - rate >= RATE_BAND:
            losses.append("Lower " + line)
            rate_head += f" (week {med}%)"
    head.append(rate_head)

    by_lane = defaultdict(lambda: [0, 0])
    for g in d.get("grades") or []:
        for l in g.get("lanes") or []:
            by_lane[l["lane"]][0] += l["accepts"]
            by_lane[l["lane"]][1] += l["answered"]
    # most accepts, not best rate: a 13/14 lane outranked a 49/67 one on rate (2026-11-05), and 14 tries is noise
    ranked = sorted(((a, a / n, n, k) for k, (a, n) in by_lane.items() if n >= BEST_MIN), reverse=True)
    if ranked:
        a, _, n, k = ranked[0]
        wins.append(f"Most accepts: {k}, {a}/{n} ({_pct(a, n)}%).")

    problems = []                                     # (rank, headline part): the worst one joins the headline
    for b in (d.get("kaggle") or {}).get("failed") or []:
        fixes.append(f"Kaggle prover batch {b['batch']} failed.")
    if (d.get("kaggle") or {}).get("failed"):
        problems.append((0, f"{len(d['kaggle']['failed'])} Kaggle failed"))

    lost = _lost(t)
    if t.get("judged") and lost / t["judged"] >= LOST_FIX:
        streak, want, exhausted = 1, date.fromisoformat(d["day"]) - timedelta(days=1), True
        for h in reversed(prior):                       # calendar days, not reports: a missing day ends the streak
            ht = h["totals"]
            if h["day"] != want.isoformat() or not ht.get("judged") or _lost(ht) / ht["judged"] < LOST_FIX:
                exhausted = False
                break
            streak, want = streak + 1, want - timedelta(days=1)
        causes = ", ".join(f"{n} {k}" for k, n in sorted((t.get("errors") or {}).items(), key=lambda x: -x[1]))
        fixes.append(f"Lost before the kernel: {lost} of {t['judged']} ({_pct(lost, t['judged'])}%), {causes}"
                     + (f"; {'at least ' if exhausted else ''}{streak} days running at "
                        f"{_pct(LOST_FIX, 1)}% or more." if streak > 1 else "."))
        problems.append((2, f"{_pct(lost, t['judged'])}% lost pre-kernel"))
    rc = t.get("recovered") or {}
    if fixes and fixes[-1].startswith("Lost before") and rc.get("attempted", 0) >= RESCUE_MIN \
            and rc.get("answers", 0) / rc["attempted"] < RESCUE_FLOOR:
        # #597's 2026-11-03 read: a failed rescue's saved result is the upstream timeout itself, so this is the free
        # upstreams' latency behind kumori's router, not a fault in this repo's client
        fixes[-1] = fixes[-1][:-1] + (f"; the edge-cut rescue saved {rc.get('answers', 0)} of {rc['attempted']}, because "
                                      "the saved results were the upstream timeouts themselves (kumori's routing).")

    for r in d.get("rungs") or []:
        idle = r.get("idle_days")
        if r["rung"].startswith("competition math"):
            if idle is not None and idle > LADDER_IDLE_DAYS:
                fixes.append(f"The ladder has been idle {idle} days.")
                problems.append((1, f"ladder idle {idle}d"))
            continue
        if r["rung"] in RETIRED:                         # the details table still lists it; the brief stays quiet
            continue
        if idle is not None and idle > IDLE_FIX_DAYS:
            fixes.append(f"{r['rung']} idle {idle} days: restart it or retire it from the report.")
        if r["rung"] == "openproblems.bio":
            src = r.get("source") or {}
            if src and not src["ok"]:
                fixes.append(f"openproblems.bio's data source is down since {src['down_since'][:10]} ({src['code']}); "
                             "its two scheduled workflows stay disabled (DECISIONS 2026-11-05).")
            elif src.get("back_since"):
                fixes.append(f"openproblems.bio's data source answers again since {src['back_since'][:10]}: archive the "
                             "data with checksums, then re-enable openproblems.yml and openproblems_qualify.yml.")
            rounds = r.get("scored", 0) + r.get("crashed", 0)
            if rounds and r.get("crashed", 0) / rounds >= CRASH_FIX:
                fixes.append(f"openproblems.bio: {r['crashed']} crashed beside {r['scored']} scored ({_pct(r['crashed'], rounds)}% of rounds).")

    regressed, refusing = [], []
    for s in d.get("speed") or []:
        if s.get("prev_week") and not _comparable(s):
            fixes.append(f"Tool lift for {s['lane']} is not comparable: {s['targets']} problems tried this week against "
                         f"{s['prev_targets']} the week before.")
            if s.get("refused", 0) >= s.get("targets", 0):
                refusing.append(f"{s['lane']} ({s['refused']} refusals, {s['targets']} targets)")
            continue
        move = _lift(s)
        if move is None:
            continue
        now, before = move
        line = (f"tool lift {s['lane']}: {now}% ({s['accepted']}/{s['targets']}) this week against {before}% "
                f"({s['prev_accepted']}/{s['prev_targets']}) the week before.")
        if before - now >= LIFT_PTS:
            regressed.append(s["lane"])
            losses.append("Down: " + line)
            if s.get("refused", 0) >= s["targets"]:
                refusing.append(f"{s['lane']} ({s['refused']} refusals, {s['targets']} targets)")
        elif now - before >= LIFT_PTS:
            wins.append("Up: " + line)
    if refusing:
        ideas.append("Refusals outnumber targets on " + ", ".join(refusing) +
                     ": refusals, not the tools, cut the problems tried.")
    # headline only for a lane newly regressed since the last report; the body lists every one, every day
    was = {s["lane"] for s in (prior[-1].get("speed") or [] if prior else []) if (m := _lift(s)) and m[1] - m[0] >= LIFT_PTS}
    if set(regressed) - was:
        problems.append((3, f"lift down {len(regressed)}/{len(d['speed'])}"))

    if problems:
        head.append(min(problems)[1])
    if len(" · ".join(head)) > HEADLINE_MAX:            # the rate's comparison goes first, then the rate itself
        head[1] = rate_head.split(" (")[0]
    if len(" · ".join(head)) > HEADLINE_MAX:
        del head[1]
    # with the headline's rate read off the baseline, these totals say they are every target's (Codex f3)
    pre = f"{t['accepted']}/{t['answered']} accepted{' on all targets' if off else ''} · {t['solved_ever']} solved ever, {t['open']} open"
    pre += f" · most accepts {ranked[0][3]} {ranked[0][0]}/{ranked[0][2]}" if ranked else ""
    if not prior:
        pre += " · no earlier reports to compare against"
    elif off and not rates:
        pre += " · no earlier report read off the no-model baseline yet"
    return {"headline": " · ".join(head), "preheader": pre, "wins": wins, "losses": losses, "fixes": fixes, "ideas": ideas}


def render(b):
    out = []
    for title, items in (("Wins", b["wins"]), ("Losses", b["losses"]), ("Fix", b["fixes"]), ("Ideas", b["ideas"])):
        out += [f"**{title}**", ""] + ([f"- {i}" for i in items] or ["- none today"]) + [""]
    return "\n".join(out)
