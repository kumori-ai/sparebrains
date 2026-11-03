"""Lane budget: will a batch fit in a router lane's free daily cap, before it makes one call (kumori #574, 2026-11-03).

Every kumori router lane has a daily cap the router enforces, shared by every app on the router (llm_usage(), the
cluster-wide summary), and a backoff when the provider rate-limits it (llm_backoff_state()). Run 41725608251 was
dispatched with no look at either: a head-to-head needing up to 240 calls on meganova-mistral-small-3-2-24b, a lane
capped at 50 a day with 49 used by 22:09 UTC, and every meganova lane in backoff to midnight. Here a batch plans
at most SHARE of what a lane has left today, so one sparebrains run never empties a lane other apps also use.

    python3 tools/lane_budget.py --need 240                     # the lanes with room for 240 calls today
    python3 tools/lane_budget.py --need 240 --lane groq-qwen3-8-27b   # exit 1, with the reason, if it has none
"""
import argparse, sys

SHARE = 0.5     # of a lane's remaining daily cap one batch may plan on (a courtesy to the other apps; not measured)


def headroom(usage, backoff):
    """{lane: cap, used, remaining, enabled, backed_off, back_in_s} from llm_usage() and llm_backoff_state()."""
    out = {}
    for name, u in (usage.get("backends") or {}).items():
        b = backoff.get(name) or {}
        out[name] = {"cap": u.get("cap"), "used": u.get("used"), "remaining": u.get("remaining"),
                     "enabled": bool(u.get("enabled")), "backed_off": bool(b.get("backed_off")),
                     "back_in_s": b.get("remaining_sec") if b.get("backed_off") else None}
    return out


def why_not(lane, need, room, share=SHARE):
    """None when `need` calls fit in `share` of the lane's remaining cap and it is up; else the reason."""
    r = room.get(lane)
    if r is None:
        return f"{lane} is not in the router's usage table"
    if not r["enabled"]:
        return f"{lane} is disabled on the router"
    if r["backed_off"]:
        return f"{lane} is in backoff for {r['back_in_s']} s more"
    if r["remaining"] is None:
        return f"{lane} reports no daily cap, so the need cannot be checked"
    if need > share * r["remaining"]:
        return (f"{lane} has {r['remaining']} of {r['cap']} calls left today; {need} needed, "
                f"at most {int(share * r['remaining'])} ({share:.0%}) for one batch")
    return None


def roomy(need, room, share=SHARE, n=8, among=None):
    """The lanes `need` calls fit in, most room first; `among`: only these (the chat catalog, not whisper or rerankers)."""
    ok = [(k, r) for k, r in room.items() if (among is None or k in among) and why_not(k, need, room, share) is None]
    return [k for k, _ in sorted(ok, key=lambda x: -x[1]["remaining"])][:n]


def preflight(lane, need, usage_fn, backoff_fn, share=SHARE, catalog_fn=None):
    """Raise SystemExit before any call when the batch does not fit, naming chat lanes that would."""
    room = headroom(usage_fn(), backoff_fn())
    why = why_not(lane, need, room, share)
    if why:
        alt = roomy(need, room, share, among=chat_lanes(catalog_fn) if catalog_fn else None)
        sys.exit(f"lane budget: {why}. Lanes with room for {need} today: {', '.join(alt) or 'none'}")
    r = room[lane]
    print(f"lane budget: {lane} {r['remaining']} of {r['cap']} left today, this batch plans on up to {need}", flush=True)


def chat_lanes(catalog_fn):
    return {b.get("name") or b.get("backend") for b in catalog_fn()}


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--need", type=int, required=True)
    ap.add_argument("--lane", default="")
    ap.add_argument("--share", type=float, default=SHARE)
    a = ap.parse_args(argv)
    sys.path.insert(0, str(__import__("pathlib").Path(__file__).resolve().parent.parent))
    from utilities.kumori_api_client import init, llm_backends, llm_backoff_state, llm_usage
    init()
    if a.lane:
        preflight(a.lane, a.need, llm_usage, llm_backoff_state, a.share, llm_backends)
        return 0
    room = headroom(llm_usage(), llm_backoff_state())
    for k in roomy(a.need, room, a.share, n=50, among=chat_lanes(llm_backends)):
        print(f"{k}\t{room[k]['remaining']} of {room[k]['cap']} left")
    return 0


if __name__ == "__main__":
    sys.exit(main())
