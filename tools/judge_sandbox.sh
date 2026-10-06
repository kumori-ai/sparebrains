#!/usr/bin/env bash
# Run once per job, after lean-action: creates the user that runs untrusted Lean for
# tools/check.py and points the judge at it. That user can read the toolchain and the
# workspace but not this job's processes, so no /proc/<pid>/environ holds a secret it can see.
set -euo pipefail
u=sbjudge
id "$u" >/dev/null 2>&1 || sudo useradd --system --no-create-home --shell /usr/sbin/nologin "$u"
sudo install -d -o "$u" -m 700 "/tmp/$u"
d="$GITHUB_WORKSPACE"
while [ "$d" != / ]; do sudo chmod o+x "$d"; d=$(dirname "$d"); done
chmod o+x "$HOME"
chmod -R o+rX "${ELAN_HOME:-$HOME/.elan}" "$GITHUB_WORKSPACE"
echo "SB_JUDGE_USER=$u" >> "$GITHUB_ENV"
