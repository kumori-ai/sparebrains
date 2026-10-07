"""Stage 2's public threads: one GitHub issue per open problem, written and kept current by
kumori-ai[bot] (DECISIONS.md 2026-10-06). The issue is the surface for people; the machines keep
reading the dossier and the ledger. Everything here is rendered from the public dossier.

    python3 tools/problem_issues.py --dry-run _oneoff/issues --only mil/mil_c05_s01_ex03,...
    python3 tools/problem_issues.py --post --only ...         (GH_TOKEN: the app's installation token)
    python3 tools/problem_issues.py --digest RUN_ID            one comment per problem a relay run touched
    python3 tools/problem_issues.py --sync                     every comment back into the dossier

The issue body is the bot's and is regenerated in place (it opens with MARKER); people write in
the comments, and those comments reach the next model through the dossier.
"""
import argparse, json, os, sys, urllib.request
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT), str(ROOT / "tools")]
import relay

REPO = "kumori-ai/sparebrains"
API = f"https://api.github.com/repos/{REPO}"
LABEL = "problem"
MARKER = "<!-- sparebrains:problem {key} -->"


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
             f"**Open problem.** `{d['target']}` · {d.get('rung_label') or d.get('rung')}"
             + (f" · number {order} in the [stage-2 order]({relay.SITE}/targets#open)" if order else ""), "",
             f"{d['answered']} answered tries by {d['lanes_tried']} models so far, every one rejected by the Lean kernel. "
             "This first post is written by kumori-ai[bot] and regenerated from the ledger after every run; "
             "**the comments below are yours**, and the next model that tries this problem reads them.", "",
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
              "`tools/check.py` ([AGENTS.md](https://github.com/kumori-ai/sparebrains/blob/main/AGENTS.md)), and post "
              "the hand-off. Say which model you used; AI help is welcome here and is always disclosed.",
              "- **The statement looks wrong:** use the misformalization form instead of a proof.",
              f"- Everything known about this problem: [the dossier]({page}), or [as JSON]({page}.json) for a program.", "",
              "The Lean kernel is the only judge: nothing here counts until it accepts a proof. A known proof of "
              "this problem from elsewhere is welcome as a link, but it is a literature find, not a new solve.", "",
              "<details><summary>Prompt pack: what the free models are shown (paste into your own)</summary>", "",
              "````", prompt, "````", "", "</details>"]
    title = f"Open problem: {d['target']} ({d.get('rung_label') or d.get('rung')})"
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
        lines = head + [f"**Run [{run_id}]({relay.SITE}/runs/{run_id})** ({kinds}): {len(rs)} tries, {len(answered)} answers, "
                 f"{len(accepted)} accepted by the kernel.", "", "| model | lane | try | verdict | what Lean said first |", "|---|---|---|---|---|"]
        for r in rs:
            reason = (r.get("reason") or "").replace("|", "\\|").replace("\n", " ")[:140]
            lines.append(f"| `{r.get('model') or 'unknown'}` | `{r['backend']}` | {r.get('attempt_no')} "
                         f"({r.get('try_mode') or 'cold'}) | {r['verdict']} | {reason} |")
        if accepted:
            a = accepted[0]
            lines += ["", f"**Solved.** The kernel accepted `{a['backend']}`'s proof: "
                      f"[verified/{key}/{a['backend']}.lean](https://github.com/{REPO}/blob/main/verified/{key}/{a['backend']}.lean)."]
        out.append((key, "\n".join(lines)))
    return out


class GitHub:
    def __init__(self, token):
        self.token = token

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


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--only", default="", help="comma-separated <set>/<target> keys")
    ap.add_argument("--dry-run", default="", help="write each rendered issue to this directory; post nothing")
    ap.add_argument("--post", action="store_true", help="create or update each --only problem's issue")
    ap.add_argument("--digest", default="", help="post a relay run's results on each problem it touched")
    ap.add_argument("--sync", action="store_true", help="copy every problem issue's comments into the dossier")
    ap.add_argument("--note", type=int, default=0, help="post NOTE_BODY (env) on this issue number as the bot")
    ap.add_argument("--close", action="store_true", help="with --note: close the issue as completed")
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
        for k in keys:
            d = relay.fetch_dossier(*k.rsplit("/", 1))
            if d.get("solved"):
                print(f"{k}: solved; no thread")
                continue
            title, body = render(d, order.get(k))
            if k in issues:
                gh.call("PATCH", f"/issues/{issues[k]['number']}", {"title": title, "body": body})
                print(f"{k}: updated #{issues[k]['number']}")
            else:
                i = gh.call("POST", "/issues", {"title": title, "body": body, "labels": [LABEL]})
                print(f"{k}: opened #{i['number']} {i['html_url']}")
    if args.digest:
        rows = [json.loads(l) for f in (ROOT / "ledger").glob(f"**/{args.digest}.jsonl")
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
            gh.call("POST", f"/issues/{n}/comments", {"body": text})
            d = relay.fetch_dossier(*k.rsplit("/", 1))
            if not d.get("solved"):                      # keep the first post current with the newest near misses
                title, body = render(d, order.get(k))
                gh.call("PATCH", f"/issues/{n}", {"title": title, "body": body})
            if "**Solved.**" in text and issues[k]["state"] == "open":
                gh.call("PATCH", f"/issues/{n}", {"state": "closed", "state_reason": "completed"})
            print(f"{k}: digest on #{n}")
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
