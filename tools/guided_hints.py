"""A paired, leaf-only hint experiment. No assembly or exchange of new proofs between treatments."""
import hashlib
import json
import re

import check
import goal_closer

ARMS = ("unhinted", "hinted")


def validate_manifest(man, n):
    sha = lambda value: isinstance(value, str) and re.fullmatch(r"[0-9a-f]{64}", value)
    bp = man.get("blueprint") or {}
    generation = man.get("generation") or {}
    if not bp.get("path") or not sha(bp.get("sha256")):
        raise ValueError("hint experiment requires a frozen blueprint path and sha256")
    if not man.get("problems") or any(not sha((man.get("target_sha256") or {}).get(k)) for k in man["problems"]):
        raise ValueError("hint experiment requires every target sha256")
    if type(n) is not int or n < 1 or type(man.get("samples_per_hole")) is not int or man["samples_per_hole"] != n:
        raise ValueError("hint experiment requires an explicit matching samples_per_hole")
    if (not generation.get("model") or not isinstance(generation.get("revision"), str)
            or not re.fullmatch(r"[0-9a-f]{40}", generation["revision"])):
        raise ValueError("hint experiment requires a frozen model and revision")


def digest(value):
    return hashlib.sha256(value.encode()).hexdigest()


def leaf(item):
    g = item["guided"]
    return f"{item['target_set']}/{item['target']}:" + ".".join(map(str, [*g.get("path", []), g["hole"]]))


def paired_work(work, names):
    keys = [leaf(p) for p in work]
    if not keys or len(set(keys)) != len(keys) or set(keys) != set(names):
        raise ValueError("hints must name exactly the exported leaves, once each")
    out = []
    for index, p in enumerate(work):
        hints = names[leaf(p)]
        if (not isinstance(hints, list) or not 1 <= len(hints) <= 8
                or any(not isinstance(n, str) or not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9'.]*", n) for n in hints)):
            raise ValueError("a hint contains only checked declaration names, not code or prose")
        if type(p["n"]) is not int or p["n"] < 1:
            raise ValueError("each arm needs a positive sample budget")
        hint_sha = digest(json.dumps(hints, separators=(",", ":")))
        for arm in ARMS if index % 2 == 0 else reversed(ARMS):
            prompt = ("-- Suggested Mathlib declarations: " + ", ".join(hints) + "\n" if arm == "hinted" else "") + p["statement"]
            out.append({**p, "statement": prompt,
                        "guided": {**p["guided"], "hint_arm": arm, "hint_sha": hint_sha,
                                   "statement_sha": digest(p["statement"]), "prompt_sha": digest(prompt)}})
    return out


def judge(work, answers, judge_text, proof_of):
    expected = {(leaf(p), p["guided"]["hint_arm"]): p for p in work}
    if not expected or len(expected) != len(work):
        raise ValueError("empty or duplicated experiment plan")
    keys = list(dict.fromkeys(key for key, arm in expected))
    if any((key, arm) not in expected for key in keys for arm in ARMS):
        raise ValueError("experiment plan must contain both treatments")
    samples, config = {}, None
    # Reject provenance drift and duplicate sample IDs BEFORE invoking Lean on anything.
    for answer in answers:
        key = leaf(answer), answer["guided"].get("hint_arm")
        p = expected.get(key)
        sample = answer.get("sample")
        if (p is None or answer["guided"] != p["guided"] or type(sample) is not int
                or not 0 <= sample < p["n"] or (*key, sample) in samples):
            raise ValueError("unplanned, duplicated or mismatched hint sample")
        actual = answer.get("config")
        if not isinstance(actual, dict) or not actual:
            raise ValueError("generation configuration is missing")
        frozen = p["guided"].get("generation")
        if frozen and any(actual.get(k) != v for k, v in frozen.items()):
            raise ValueError("generation does not match the frozen model revision")
        if config is not None and actual != config:
            raise ValueError("generation settings changed between samples")
        config = actual
        samples[*key, sample] = answer
    rows, held = [], {}
    for key in keys:
        row = {"leaf": key, "kind": "paired_lemma_names", "try_mode": "guided",
               "config": config, "arms": {}, "complete": True,
               "claim": "selected leaves only; raw acceptance without binder normalization or repairs; "
                        "not comparable to earlier repair-assisted batches; no whole-proof or general lift claim"}
        for arm in ARMS:
            p = expected[key, arm]
            g = p["guided"]
            prompt = p["statement"]
            # The comment is prompt-only. Always judge the original statement, never the generated declaration.
            original = prompt.split("\n", 1)[1] if arm == "hinted" else prompt
            if digest(original) != g["statement_sha"] or digest(prompt) != g["prompt_sha"]:
                raise ValueError("planned goal or prompt changed")
            prefix = goal_closer.prefix_of(original)
            verdicts = []
            for i in range(p["n"]):
                answer = samples.get((key, arm, i))
                if answer is None:
                    continue
                body = proof_of(answer.get("text") or "")
                result = judge_text(prefix + "\n" + body) if body else {"verdict": "reject", "reason": "no proof"}
                unfinished = check.unfinished(result.get("reason", "")) or check.unfinished(result.get("output", ""))
                verdicts.append({"sample": i, "verdict": result["verdict"], "unfinished": unfinished,
                                 "seconds": result.get("seconds"), "no_proof": not bool(body)})
                if result["verdict"] == "accept":
                    held_key = f"{key}:{arm}:{i}"
                    held[held_key] = prefix + "\n" + body
                    verdicts[-1]["proof_sha"] = digest(held[held_key])
            complete = len(verdicts) == p["n"] and not any(v["unfinished"] for v in verdicts)
            row["arms"][arm] = {"planned": p["n"], "generated": len(verdicts), "complete": complete,
                                "pass_at_n": any(v["verdict"] == "accept" for v in verdicts) if complete else None,
                                "accepts": sum(v["verdict"] == "accept" for v in verdicts),
                                "hint_sha": g["hint_sha"], "statement_sha": g["statement_sha"],
                                "prompt_sha": g["prompt_sha"], "samples": verdicts}
            row["complete"] &= complete
        rows.append(row)
    return rows, held
