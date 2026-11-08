#!/usr/bin/env bash
# elan, then the toolchain lean-toolchain names, as lean-action v1.6.0's scripts/install_elan.sh does; both download
# from GitHub, so retry.sh wraps this whole file. lean and lake by their absolute paths: GITHUB_PATH only reaches later
# steps (Codex 20261108T160100530734Z f2). LEAN_BUILD_FAIL_FIRST=true is the canary: the first attempt fetches a
# file that does not exist, so the retry must run.
set -euo pipefail
marker="${RUNNER_TEMP:-/tmp}/lean-build-canary"
if [ "${LEAN_BUILD_FAIL_FIRST:-false}" = true ] && [ ! -e "$marker" ]; then
  touch "$marker"
  curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/no-such-file-lean-build-canary >/dev/null
fi
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y --default-toolchain none
"$HOME/.elan/bin/lean" --version
"$HOME/.elan/bin/lake" --version
