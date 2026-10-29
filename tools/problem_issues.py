"""Stage 2's public threads: one GitHub issue per open problem, written and kept current by
kumori-ai[bot] (DECISIONS.md 2026-10-06). The issue is the surface for people; the machines keep
reading the dossier and the ledger. Everything here is rendered from the public dossier.

    python3 tools/problem_issues.py --dry-run _oneoff/issues --only mil/mil_c05_s01_ex03,...
    python3 tools/problem_issues.py --post --only ...         (GH_TOKEN: the app's installation token)
    python3 tools/problem_issues.py --digest RUN_ID            one comment per problem a relay run touched
    python3 tools/problem_issues.py --sync                     every comment back into the dossier
    python3 tools/problem_issues.py --refill 1000 --max-new 25 a thread for every open problem, 25 more a run at most
    python3 tools/problem_issues.py --catchup                  every judged try no bot comment has reported yet, any mode
    python3 tools/problem_issues.py --daily                    the daily log: one comment a UTC day on the log issue
    python3 tools/problem_issues.py --open                     a new issue from OPEN_TITLE / OPEN_BODY / OPEN_LABELS (env)

The issue body is the bot's and is regenerated in place (it opens with MARKER); people write in
the comments, and those comments reach the next model through the dossier.
"""
import argparse, json, os, re, sys, time, urllib.request
from datetime import datetime, timedelta, timezone
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT), str(ROOT / "tools")]
import daily_report, ledger_files
import relay

REPO = "kumori-ai/sparebrains"
API = f"https://api.github.com/repos/{REPO}"
LABEL = "problem"
MARKER = "<!-- sparebrains:problem {key} -->"
DIGEST_MARK = "<!-- sparebrains:digest run={run} -->"
LOG_LABEL, LOG_MARKER = "log", "<!-- sparebrains:log -->"
GATE_MARKER = "<!-- sparebrains:gate {stage} -->"   # the open gate issue a stage's workflow reports on
DAY_MARK = "<!-- sparebrains:day {day} -->"         # one bot comment per thread per UTC day, edited as runs finish
DAY_CAP = 60_000                                     # GitHub caps a comment at 65,536 characters
# Where each problem comes from, said on every thread and every solve (2026-10-18, after the r/aiwars review: credit
# the sources and say plainly that people solved these long ago; "open" means open to our free pool).
ORIGIN = {"amc12": "an AMC 12 competition problem", "aime": "an AIME competition problem",
          "imo": "an International Mathematical Olympiad problem", "mathd": "a problem from the MATH dataset (Hendrycks et al., 2021)"}
SOURCES = {
    "minif2f": "formal statement from miniF2F (OpenAI, 2021; Lean 4 port by Google DeepMind, Apache-2.0)",
    "mil": "an exercise from Mathematics in Lean by Jeremy Avigad and Patrick Massot (Apache-2.0)",
    "primer": "a level of the Natural Number Game (leanprover-community/NNG4, Apache-2.0)",
}
PACE_S = 1.0          # between writes: GitHub allows 80 content writes a minute and 500 an hour (its REST rate-limit docs, 2026-10-17)
AGENTS_URL = f"https://github.com/{REPO}/blob/main/kumori_agents.md"
PITCH = ("**Help solve it:** tell any coding agent (Claude Code, Codex, Cline, ...) *\"read "
         f"[kumori_agents.md]({AGENTS_URL}) and start\"*. Your quota, your machine, and the Lean kernel is the only judge.")
MAX_POSTS = 150       # digest comments a run at most; the next hourly run takes the rest


def credit(target_set, target):
    """One sentence: where the problem comes from and who solved it first."""
    origin = next((v for k, v in ORIGIN.items() if target.startswith(k)), None)
    family = target_set.split("/")[0]                # target sets carry a split: minif2f/test
    source = SOURCES.get(family, f"from the {target_set} set")
    if family == "minif2f":
        what = f"{origin or 'a competition-style problem'}, {source}"
    else:
        what = source
    return (f"**Where it comes from:** {what}. People solved it long ago; it is open only to our free pool, "
            "and every proof here is credited to the model that wrote it.")


def key_of(target_set, target):
    return f"{target_set}/{target}"


def render(d, order=None):
    """(title, body) for one open problem, from its dossier."""
    key = key_of(d["target_set"], d["target"])
    page = f"{relay.SITE}/problems/{key}"
    fails = "\n".join(f"| `{f['kind']}` | {f['n']} | {f['lanes']} |" for f in d.get("failures", []))
    near = (d.get("near_misses") or [None])[0]
    names = relay.library_names(d)
    target_text = (ROOT / "targets" / d["target_set"] / f"{d['target']}.lean").read_text()
    prompt, _ = relay.relay_prompt(target_text, d)
    parts = [MARKER.format(key=key), "",
             f"**Open to our free pool.** `{d['target']}` · {d.get('rung_label') or d.get('rung')}"
             + (f" · number {order} in the [stage-2 order]({relay.SITE}/targets#open)" if order else ""), "",
             f"{d['answered']} answered tries by {d['lanes_tried']} models so far, every one rejected by the Lean kernel. "
             "This first post is written by kumori-ai[bot] and regenerated from the ledger after every run; "
             "**the comments below are yours**, and the next model that tries this problem reads them.", "",
             credit(d["target_set"], d["target"]), "",
             "### The statement", f"A proof replaces the `sorry`. [On GitHub]({d['source']}).",
             "```lean", (d.get("statement") or target_text).rstrip(), "```", "",
             "### How the tries failed", "| kind | rejects | models |", "|---|---|---|", fails, ""]
    if near:
        parts += ["### The closest attempt so far",
                  f"`{near['failure_kind']}`, by `{near['backend']}` ({near['try_mode'] or 'cold'}), "
                  f"[transcript]({relay.SITE}/attempts/{near['id']}). What Lean said is the part worth reading: "
                  "it is exactly what is left to prove.",
                  "```lean", relay._clip(near["proof"], relay.PROOF_CAP), "```",
                  "```", relay._clip(relay.RUNNER_PATH.sub("", near["lean_output"] or ""), relay.LEAN_CAP), "```", ""]
    if names:
        parts += ["### Library names models invented", "These do not exist in the pinned mathlib: "
                  + ", ".join(f"`{n}`" for n in names) + ".", ""]
    parts += ["### How to help",
              "- **An idea, a lemma name that does exist, a partial proof:** comment below, in your own words.",
              "- **Your own model or agent:** paste the prompt pack below into it, check the result with "
              "`tools/check.py` ([kumori_agents.md](https://github.com/kumori-ai/sparebrains/blob/main/kumori_agents.md)), and post "
              "the hand-off. Say which model you used; AI help is welcome here and is always disclosed.",
              "- **The statement looks wrong:** use the misformalization form instead of a proof.",
              f"- Everything known about this problem: [the dossier]({page}), or [as JSON]({page}.json) for a program.", "",
              "The Lean kernel is the only judge: nothing here counts until it accepts a proof. A known proof of "
              "this problem from elsewhere is welcome as a link, but it is a literature find, not a new solve.", "",
              "<details><summary>Prompt pack: what the free models are shown (paste into your own)</summary>", "",
              "````", prompt, "````", "", "</details>"]
    title = f"Open to our free pool: {d['target']} ({d.get('rung_label') or d.get('rung')})"
    return title, "\n".join(parts)


def quote(author, body, cap=400):
    """A GitHub quote-reply of a person's comment: their words, attributed, clipped."""
    text = relay._clip(body, cap)
    return f"> **@{author}** wrote:\n" + "\n".join("> " + l for l in text.splitlines())


def digest(run_id, rows, comments=None):
    """(key, comment) per problem a relay run touched, from that run's ledger rows. When some tries
    read people's comments (relay+thread), the reply opens by quoting them; `comments` maps a
    comment id to (author, body)."""
    by = defaultdict(list)
    for r in rows:
        if str(r.get("run_id")) == str(run_id) and r.get("verdict") in ("accept", "reject", "error"):
            by[key_of(r["target_set"], r["target"])].append(r)
    out = []
    for key, rs in by.items():
        answered = [r for r in rs if r["verdict"] in ("accept", "reject")]
        accepted = [r for r in rs if r["verdict"] == "accept"]
        read = sorted({i for r in rs for i in r.get("comment_ids") or [] if (comments or {}).get(i)})
        head = []
        for i in read:
            head += [quote(*comments[i]), ""]
        if read:
            n_read = sum(1 for r in rs if r.get("try_mode") == "relay+thread" and r["verdict"] in ("accept", "reject"))
            head += [f"{n_read} of this run's answers came from models that read the comment above (`relay+thread`); "
                     "every try, answered or not, is below:", ""]
        kinds = ", ".join(sorted({r.get("try_mode") or "cold" for r in rs}))
        lines = [DIGEST_MARK.format(run=run_id)] + head + [f"**Run [{run_id}]({relay.SITE}/runs/{run_id})** ({kinds}): {len(rs)} tries, {len(answered)} answers, "
                 f"{len(accepted)} accepted by the kernel.", "", "| model | lane | try | verdict | what Lean said first |", "|---|---|---|---|---|"]
        for r in rs:
            reason = (r.get("reason") or "").replace("|", "\\|").replace("\n", " ")[:140]
            lines.append(f"| `{r.get('model') or 'unknown'}` | `{r['backend']}` | {r.get('attempt_no')} "
                         f"({r.get('try_mode') or 'cold'}) | {r['verdict']} | {reason} |")
        if accepted:
            a = accepted[0]
            lines += ["", f"**Solved.** The kernel accepted `{a['backend']}`'s proof: "
                      f"[verified/{key}/{a['backend']}.lean](https://github.com/{REPO}/blob/main/verified/{key}/{a['backend']}.lean).",
                      "", credit(a["target_set"], a["target"])]
        else:
            lines += ["", "_Spot what they missed? A lemma that exists, a different route, a partial proof: comment "
                      "below and the next run's models read it, as one did for `mathd_algebra_756` (#11)._"]
        lines += ["", PITCH]
        out.append((key, "\n".join(lines)))
    return out


def digested_runs(comments):
    """Run ids the bot's comments on a thread already reported: the marker, or the older '**Run [id](' heading."""
    out = set()
    for c in comments:
        if (c.get("user") or {}).get("type") == "Bot":
            body = c.get("body") or ""
            out.update(re.findall(r"sparebrains:digest run=(\d+)", body) + re.findall(r"\*\*Run \[(\d+)\]\(", body))
    return out


def pending_runs(rows, since, done):
    """Run ids with a judged try on this problem after `since` (the thread's opening) that no bot comment has
    reported, oldest first. Every mode counts: relay, cold, the loop, the prover, volunteers."""
    first = {}
    for r in rows:
        run = str(r.get("run_id") or "")
        if run and run not in done and (r.get("ts") or "") > since and r.get("verdict") in ("accept", "reject", "error"):
            first[run] = min(first.get(run, r["ts"]), r["ts"])
    return sorted(first, key=first.get)


def row_day(line):
    """A ledger line's YYYY-MM-DD, read without parsing it. Most rows open with ts; volunteer rows open with run_id."""
    i = line.find('"ts": "')
    return line[i + 7:i + 17] if i >= 0 else ""


def load_rows(since_day):
    """Every ledger row from `since_day` (YYYY-MM-DD) on; older lines are skipped unparsed."""
    out = []
    for f in ledger_files.try_files(ROOT / "ledger"):
        for l in f.read_text().splitlines():
            if l.strip() and row_day(l) >= since_day:
                out.append(json.loads(l))
    return out


def daily_log(report, runs):
    """The daily log comment: the school report (tools/daily_report.py) plus the Actions runs behind it."""
    lines = [LOG_MARKER, daily_report.render(report).rstrip()]
    if runs:
        by = defaultdict(lambda: defaultdict(int))
        for r in runs:
            state = r.get("conclusion") or r.get("status")
            if state != "skipped":                   # a comment wakes bench and volunteer; a skipped run did nothing
                by[Path(r.get("path") or r["name"]).stem][state] += 1
        lines += ["", "**GitHub Actions runs:** " + "; ".join(
            f"{n} " + ", ".join(f"{c} {k}" for k, c in sorted(v.items())) for n, v in sorted(by.items()))]
    lines += ["", f"Every try, transcript and verdict: {relay.SITE}. Every accepted proof: "
              f"[verified/](https://github.com/{REPO}/tree/main/verified).", "", PITCH]
    return "\n".join(lines)


class GitHub:
    def __init__(self, token):
        self.token = token

    def write(self, method, path, data=None):
        """A content write, paced to stay under GitHub's per-minute limit."""
        out = self.call(method, path, data)
        time.sleep(PACE_S)
        return out

    def comments(self, number):
        out, page = [], 1
        while True:
            batch = self.call("GET", f"/issues/{number}/comments?per_page=100&page={page}")
            out += batch
            if len(batch) < 100:
                return out
            page += 1

    def call(self, method, path, data=None):
        req = urllib.request.Request(API + path, method=method, data=json.dumps(data).encode() if data is not None else None,
                                     headers={"Authorization": f"token {self.token}", "Accept": "application/vnd.github+json",
                                              "User-Agent": relay.USER_AGENT})
        with urllib.request.urlopen(req, timeout=30) as r:
            body = r.read()
        return json.loads(body) if body else None

    def problem_issues(self):
        """key → issue, for every issue (open or closed) carrying the bot's marker."""
        found, page = {}, 1
        while True:
            batch = self.call("GET", f"/issues?labels={LABEL}&state=all&per_page=100&page={page}")
            for i in batch:
                body = i.get("body") or ""
                if body.startswith("<!-- sparebrains:problem "):
                    found[body.split(" ", 2)[2].split(" -->")[0]] = i
            if len(batch) < 100:
                return found
            page += 1


def post_daily(gh, number, text, comments, day=None):
    """Add a run's digest to the thread's one bot comment for this UTC day, editing it in place, so a watcher
    gets one notification a day, not one per run (52 bot comments against 2 from people on 2026-10-18). A new
    comment starts only for a new day, or when today's would pass GitHub's size cap. Returns 'edited' or 'posted'."""
    day = day or f"{datetime.now(timezone.utc):%Y-%m-%d}"
    mark = DAY_MARK.format(day=day)
    text = text.replace("\n\n" + PITCH, "")             # the pitch goes once, at the top of the day's comment
    mine = [c for c in comments if (c.get("user") or {}).get("type") == "Bot" and (c.get("body") or "").startswith(mark)]
    if mine and len(mine[-1]["body"]) + len(text) < DAY_CAP:
        body = mine[-1]["body"] + "\n\n---\n\n" + text
        gh.write("PATCH", f"/issues/comments/{mine[-1]['id']}", {"body": body})
        mine[-1]["body"] = body
        return "edited"
    head = (f"{mark}\n**Runs on {day} (UTC).** One comment a day, updated in place as runs finish; "
            f"the newest run is at the bottom.\n\n{PITCH}")
    c = gh.write("POST", f"/issues/{number}/comments", {"body": head + "\n\n" + text})
    comments.append(c or {"user": {"type": "Bot"}, "body": head + "\n\n" + text, "id": None})
    return "posted"


def refill(gh, issues, open_targets, fetch_dossier, n, order=None, render_fn=None, max_new=None):
    """Keep n problem threads open (Andy, 2026-10-08; every open problem from 2026-10-17). A solved problem's
    thread closes in the digest; its place goes to the next problem in the stage-2 order that has never had a
    thread. A closed thread is never reopened, no more than n are ever open, and a run opens at most max_new
    (default n). Returns opened keys."""
    render_fn = render_fn or render
    open_now, opened = sum(1 for i in issues.values() if i["state"] == "open"), []
    for t in open_targets:
        if open_now >= n or len(opened) >= (max_new or n):
            break
        k = key_of(t["target_set"], t["target"])
        if k in issues:
            continue
        d = fetch_dossier(t["target_set"], t["target"])
        if d.get("solved"):
            continue
        title, body = render_fn(d, (order or {}).get(k))
        i = (gh.write if hasattr(gh, "write") else gh.call)("POST", "/issues", {"title": title, "body": body, "labels": [LABEL]})
        issues[k] = i
        open_now += 1
        opened.append(k)
        print(f"{k}: opened #{i['number']} {i['html_url']} (refill to {n})")
    return opened


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--only", default="", help="comma-separated <set>/<target> keys; with --post, all = every open thread")
    ap.add_argument("--dry-run", default="", help="write each rendered issue to this directory; post nothing")
    ap.add_argument("--post", action="store_true", help="create or update each --only problem's issue")
    ap.add_argument("--digest", default="", help="post a relay run's results on each problem it touched")
    ap.add_argument("--sync", action="store_true", help="copy every problem issue's comments into the dossier")
    ap.add_argument("--note", type=int, default=0, help="post NOTE_BODY (env) on this issue number as the bot")
    ap.add_argument("--close", action="store_true", help="with --note: close the issue as completed")
    ap.add_argument("--refill", type=int, default=0, help="open threads for the next unsolved problems in the "
                    "stage-2 order until this many are open")
    ap.add_argument("--max-new", type=int, default=0, help="with --refill: open at most this many this run")
    ap.add_argument("--catchup", action="store_true", help="post every judged try no bot comment has reported, on its thread")
    ap.add_argument("--daily", action="store_true", help="post today's log comment, once a UTC day")
    ap.add_argument("--redo", action="store_true", help="with --daily: rewrite today's log comment in place, marked corrected")
    ap.add_argument("--open", action="store_true", help="open an issue from OPEN_TITLE / OPEN_BODY / OPEN_LABELS (env)")
    ap.add_argument("--gate-note", default="", help="post NOTE_BODY (env) on the open gate issue of this stage, e.g. stage3")
    args = ap.parse_args()
    try:
        order = {key_of(t["target_set"], t["target"]): t["order"] for t in relay.fetch_json("/targets.json")["open"]}
    except Exception as e:                           # the position line is a nicety; never block a thread on it
        print(f"stage-2 order unavailable ({type(e).__name__}: {e}); rendering without it")
        order = {}
    keys = [k.strip() for k in args.only.split(",") if k.strip()]

    if args.dry_run:
        out = Path(args.dry_run)
        out.mkdir(parents=True, exist_ok=True)
        for k in keys:
            title, body = render(relay.fetch_dossier(*k.rsplit("/", 1)), order.get(k))
            path = out / (k.replace("/", "__") + ".md")
            path.write_text(f"# {title}\n\n{body}\n")
            print(f"rendered {k} -> {path} ({len(body)} chars)")
        return 0

    gh = GitHub(os.environ["GH_TOKEN"])
    if args.open:                                    # a gate or plan issue, opened as the bot
        title, body = os.environ.get("OPEN_TITLE", "").strip(), os.environ.get("OPEN_BODY", "").strip()
        if not title or not body:
            sys.exit("--open needs OPEN_TITLE and OPEN_BODY")
        labels = [l.strip() for l in os.environ.get("OPEN_LABELS", "").split(",") if l.strip()]
        i = gh.write("POST", "/issues", {"title": title, "body": body, "labels": labels})
        print(f"opened #{i['number']} {i['html_url']}")
        return 0
    if args.gate_note:                               # a stage's workflow reporting on its own gate issue
        body, mark = os.environ.get("NOTE_BODY", "").strip(), GATE_MARKER.format(stage=args.gate_note)
        gates = [i for i in gh.call("GET", "/issues?labels=gate&state=open&per_page=20") if (i.get("body") or "").startswith(mark)]
        if not body or not gates:
            print(f"gate note: {'no body' if not body else 'no open gate issue for ' + args.gate_note}; nothing posted")
            return 0
        n = gates[0]["number"]
        how = post_daily(gh, n, body, gh.comments(n))   # one comment a day, edited as checks run (2026-10-18)
        print(f"gate note on #{n}: {how}")
        return 0
    if args.note:                                    # a status note on a plan issue, written by a person
        body = os.environ.get("NOTE_BODY", "").strip()
        if not body:
            sys.exit("--note needs NOTE_BODY")
        c = gh.call("POST", f"/issues/{args.note}/comments", {"body": body})
        print(f"note on #{args.note}: {c['html_url']}")
        if args.close:
            gh.call("PATCH", f"/issues/{args.note}", {"state": "closed", "state_reason": "completed"})
            print(f"#{args.note} closed")
        return 0
    issues = gh.problem_issues()
    if args.post:
        if keys == ["all"]:                          # re-render every open thread (a wording change, 2026-10-18)
            keys = [k for k, i in issues.items() if i["state"] == "open"]
        for k in keys:
            d = relay.fetch_dossier(*k.rsplit("/", 1))
            if d.get("solved"):
                print(f"{k}: solved; no thread")
                continue
            title, body = render(d, order.get(k))
            if k in issues:
                gh.write("PATCH", f"/issues/{issues[k]['number']}", {"title": title, "body": body})
                print(f"{k}: updated #{issues[k]['number']}")
            else:
                i = gh.call("POST", "/issues", {"title": title, "body": body, "labels": [LABEL]})
                print(f"{k}: opened #{i['number']} {i['html_url']}")
    if args.digest:
        rows = [json.loads(l) for f in ledger_files.try_files(ROOT / "ledger", f"{args.digest}.jsonl")
                for l in f.read_text().splitlines() if l.strip()]
        comments = {}
        for i in {i for r in rows for i in r.get("comment_ids") or []}:
            try:
                c = gh.call("GET", f"/issues/comments/{i}")
                comments[i] = (c["user"]["login"], c["body"])
            except Exception as e:                       # a deleted comment is just not quoted
                print(f"comment {i} unavailable ({type(e).__name__}); not quoted")
        for k, text in digest(args.digest, rows, comments):
            if k not in issues:
                print(f"{k}: no thread yet; digest not posted")
                continue
            n = issues[k]["number"]
            post_daily(gh, n, text, gh.comments(n))
            d = relay.fetch_dossier(*k.rsplit("/", 1))
            if not d.get("solved"):                      # keep the first post current with the newest near misses
                title, body = render(d, order.get(k))
                gh.call("PATCH", f"/issues/{n}", {"title": title, "body": body})
            if "**Solved.**" in text and issues[k]["state"] == "open":
                gh.call("PATCH", f"/issues/{n}", {"state": "closed", "state_reason": "completed"})
            print(f"{k}: digest on #{n}")
    if args.refill:
        refill(gh, issues, relay.fetch_json("/targets.json")["open"], relay.fetch_dossier, args.refill, order,
               max_new=args.max_new or None)
    if args.catchup:                                 # robust to the workflow_run events GitHub drops (2026-10-17: 22 of 60)
        live = {k: i for k, i in issues.items() if i["state"] == "open"}
        since_day = min((i["created_at"][:10] for i in live.values()), default="9999")
        by_key = defaultdict(list)
        for r in load_rows(since_day):
            by_key[key_of(r["target_set"], r["target"])].append(r)
        posted = 0
        for k, i in sorted(live.items(), key=lambda x: x[1]["number"]):
            n, since = i["number"], i["created_at"].replace("Z", "+00:00")
            thread = gh.comments(n)
            for run in pending_runs(by_key.get(k, []), since, digested_runs(thread)):
                if posted >= MAX_POSTS:
                    print(f"catch-up: {MAX_POSTS} posted; the rest wait for the next run")
                    break
                (_, text), = digest(run, by_key[k])
                post_daily(gh, n, text, thread)
                posted += 1
                print(f"{k}: run {run} on #{n}")
                if "**Solved.**" in text:
                    gh.write("PATCH", f"/issues/{n}", {"state": "closed", "state_reason": "completed"})
                    break
            else:
                continue
            if posted >= MAX_POSTS:
                break
        print(f"catch-up: {posted} digest comments")
    if args.daily:
        now = datetime.now(timezone.utc)
        day = f"{now:%Y-%m-%d}"
        logs = [i for i in gh.call("GET", f"/issues?labels={LOG_LABEL}&state=open&per_page=10")
                if (i.get("body") or "").startswith(LOG_MARKER)]
        log = logs[0] if logs else gh.write("POST", "/issues", {"title": "sparebrAIns daily log: what the bots did today",
              "labels": [LOG_LABEL], "body": f"{LOG_MARKER}\n**What we are trying to do:** prove every open problem on the "
              "ladder (competition mathematics in Lean 4) with spare free-tier AI compute, every answer judged by the Lean "
              f"kernel and published. {PITCH}\n\nOnce a day kumori-ai[bot] posts the last 24 hours below: tries "
              "judged by the Lean kernel, accepts, first-time solves and the GitHub Actions runs behind them. Counts "
              f"only, every one from the public ledger. The live view: {relay.SITE}."})
        today = [c for c in gh.comments(log["number"]) if c["created_at"][:10] == day and (c.get("user") or {}).get("type") == "Bot"]
        if today and not args.redo:
            print(f"daily log: {day} already posted on #{log['number']}")
        else:
            since = (now - timedelta(hours=24)).isoformat()
            report = daily_report.build(ROOT / "ledger", now)
            try:
                runs = gh.call("GET", f"/actions/runs?created=>={since[:19]}&per_page=100")["workflow_runs"]
            except Exception as e:                   # the Actions line is a nicety; the log posts without it
                print(f"actions runs unavailable ({type(e).__name__}); log without them")
                runs = []
            text = daily_log(report, runs)
            if today:                                # a correction is said out loud, never silent
                text += f"\n\n_Corrected {now:%H:%M} UTC: the first version missed rows that do not open with their timestamp (volunteer hand-offs)._"
                gh.write("PATCH", f"/issues/comments/{today[-1]['id']}", {"body": text})
            else:
                gh.write("POST", f"/issues/{log['number']}/comments", {"body": text})
            print(f"daily log: {day} on #{log['number']}")
    if args.sync:
        from utilities.kumori_api_client import init as kumori_init, sparebrains_thread
        kumori_init()
        for k, i in issues.items():
            comments = gh.call("GET", f"/issues/{i['number']}/comments?per_page=100")
            ts, t = k.rsplit("/", 1)
            sparebrains_thread({"target_set": ts, "target": t, "issue_number": i["number"], "comments": [
                {"id": c["id"], "author": c["user"]["login"], "author_type": c["user"]["type"],
                 "created_at": c["created_at"], "updated_at": c["updated_at"], "body": c["body"], "url": c["html_url"]}
                for c in comments]})
            print(f"{k}: synced {len(comments)} comments from #{i['number']}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
