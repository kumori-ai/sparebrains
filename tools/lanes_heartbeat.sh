#!/usr/bin/env bash
# Beside a ladder job (attempt.yml job 'lanes'): run tools/start_dropped_lanes.sh every TICK_S while this run's
# 'attempt' job is alive. GitHub's cron fired almost nothing from 09:42 to 15:29 on 2026-11-04 while a ladder job ran
# the whole time, so the backup rides the job that is alive. The tick runs in the background in its own process
# group, so a slow tick (gh_retry can sleep minutes) never delays noticing that the ladder job finished: the run then
# ends within POLL_S and the next chained run, queued in the same concurrency group, starts (Codex 20261104T235532650614Z).
# Degraded mode: if the job status is unreadable MAX_UNREADABLE polls in a row, the heartbeat stops (that run loses
# its backup) rather than hold the chain up to the job timeout.
set -uo pipefail
set -m   # job control: each background tick gets its own process group, so stop_tick ends gh and its retries too
TICK_S=${TICK_S:-1200}; POLL_S=${POLL_S:-60}; MAX_UNREADABLE=${MAX_UNREADABLE:-10}
TICK_CMD=${TICK_CMD:-"$(dirname "$0")/start_dropped_lanes.sh"}
tick=""; last_tick=0; unreadable=0
stop_tick() { [ -n "$tick" ] && kill -0 "$tick" 2>/dev/null && kill -TERM -- "-$tick" 2>/dev/null; wait "$tick" 2>/dev/null; tick=""; }
trap stop_tick EXIT
while :; do
  # the ladder job is named 'attempt' (its matrix is [""]); every job but this one counts
  open=$(gh api "repos/$GITHUB_REPOSITORY/actions/runs/$GITHUB_RUN_ID/jobs" \
           --jq '[.jobs[] | select(.name != "lanes" and .status != "completed")] | length' 2>/dev/null) || open=""
  if [ -z "$open" ]; then
    unreadable=$((unreadable + 1))
    echo "::warning::job status unreadable ($unreadable/$MAX_UNREADABLE)"
    if [ "$unreadable" -ge "$MAX_UNREADABLE" ]; then echo "::warning::heartbeat stops: status unreadable"; exit 0; fi
  else
    unreadable=0
    if [ "$open" = 0 ]; then echo "ladder job finished; heartbeat ends"; exit 0; fi
  fi
  if [ -n "$tick" ] && ! kill -0 "$tick" 2>/dev/null; then
    wait "$tick"; rc=$?; tick=""
    [ "$rc" = 0 ] || echo "::warning::lane tick failed (exit $rc); the next tick tries again"
  fi
  now=$(date +%s)
  if [ -z "$tick" ] && [ $((now - last_tick)) -ge "$TICK_S" ]; then
    bash "$TICK_CMD" & tick=$!; last_tick=$now
  fi
  sleep "$POLL_S"
done
