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

# The kernel's memory limits on untrusted Lean (kumori #683): 8000 MB over every run together, on the slice
# tools/check.py puts them in, and 4000 MB on each run's own scope, which check.py sets from SB_JUDGE_MEM_MB.
# Measured by tools/judge_memory_canary.py, check runs 43336349606 and 43338876083 (2026-11-12). A scope is started
# here and the limits read back from inside it: a job whose limits are not in force stops now, not at a runaway.
slice=sbjudge.slice slice_mb=8000 scope_mb=4000
sudo systemctl start "$slice"
sudo systemctl set-property --runtime "$slice" "MemoryMax=${slice_mb}M" MemorySwapMax=0
got=$(sudo systemd-run --scope --quiet --slice="$slice" --uid="$u" -p OOMPolicy=kill -p "MemoryMax=${scope_mb}M" \
  -p MemorySwapMax=0 sh -c 'cd "/sys/fs/cgroup$(cut -d: -f3 /proc/self/cgroup)" && echo $(cat memory.max memory.oom.group ../memory.max ../memory.swap.max)')
want="$((scope_mb * 1048576)) 1 $((slice_mb * 1048576)) 0"
[ "$got" = "$want" ] || { echo "judge memory limits not in force: read '$got', want '$want'"; exit 1; }
echo "SB_JUDGE_MEM_MB=$scope_mb" >> "$GITHUB_ENV"
