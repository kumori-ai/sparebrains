#!/usr/bin/env bash
# Start prover or leanstral when GitHub's schedule dropped it: a lane with no run (queued counts) in 130 minutes gets
# one, so the cadence is the one the crons meant, never more (2026-10-18: GitHub fired 6 of prover's 12 scheduled
# runs). Called by attempt.yml after a relay job and every 20 minutes by tools/lanes_heartbeat.sh beside a ladder job.
# Fails closed on its own (set -e), however it is invoked: an unreadable queue never reaches a dispatch.
# Needs GH_TOKEN (actions: write) and GITHUB_REPOSITORY.
set -euo pipefail
. "$(dirname "$0")/gh_retry.sh"
since=$(date -u -d '130 minutes ago' +%Y-%m-%dT%H:%M:%SZ)
# leanstral shares the 'leanstral' group with headtohead (and decompose watches the same Mistral limit): never start a
# round while any of the three is waiting. A plain sum, never a pipeline, whose status would be its last read's
# (Codex 20261104T230348153659Z).
waiting=0
for g in leanstral decompose headtohead; do
  n=$(gh_retry gh run list --workflow "$g.yml" --repo "$GITHUB_REPOSITORY" \
        --limit 5 --json status --jq '[.[] | select(.status == "pending" or .status == "queued" or .status == "waiting")] | length')
  waiting=$((waiting + n))
done
echo "waiting in the leanstral group: $waiting"
for w in prover leanstral; do
  if [ "$w" = leanstral ] && [ "$waiting" != "0" ]; then continue; fi
  last=$(gh_retry gh run list --workflow "$w.yml" --repo "$GITHUB_REPOSITORY" --limit 1 --json createdAt --jq '.[0].createdAt // ""')
  echo "$w: last run ${last:-none}"
  # a dispatch is sent once, never retried: one answered 500 can still have landed (Codex 20261104T225804993745Z)
  if [ -z "$last" ] || [[ "$last" < "$since" ]]; then gh workflow run "$w.yml" --ref main; echo "started $w"; fi
done
