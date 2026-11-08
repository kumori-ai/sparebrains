#!/usr/bin/env bash
# retry.sh <seconds per attempt> <command...>: run a step that talks to a machine we do not control, up to 4 times,
# waiting 15, 30, 60 s between tries (RETRY_WAITS overrides, for tests); exits with the last attempt's code.
# Each attempt is cut at the given seconds where coreutils `timeout` exists (the Ubuntu runners).
set -uo pipefail
limit=$1; shift
read -r -a waits <<< "${RETRY_WAITS:-15 30 60}"
attempts=$(( ${#waits[@]} + 1 ))
run() { if command -v timeout >/dev/null; then timeout "$limit" "$@"; else "$@"; fi; }
for (( n = 1; n <= attempts; n++ )); do
  run "$@" && exit 0
  rc=$?
  if (( n == attempts )); then
    echo "::error::failed after $n attempts (exit $rc): $*"
    exit "$rc"
  fi
  echo "::warning::attempt $n of $attempts failed (exit $rc): $*; retrying in ${waits[n-1]} s"
  sleep "${waits[n-1]}"
done
