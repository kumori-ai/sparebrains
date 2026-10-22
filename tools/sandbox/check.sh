#!/usr/bin/env bash
# Install gVisor, build the candidate image, and prove the sandbox before any candidate runs (DECISIONS 2026-10-22):
# gVisor's runsc is the runtime, the network is off, and a trivial candidate's prediction streams back whole.
# gVisor's apt repository per gvisor.dev/docs/user_guide/install (read 2026-10-22); it configures Docker itself.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
sudo apt-get update -qq && sudo apt-get install -y -qq apt-transport-https ca-certificates curl gnupg
curl -fsSL https://gvisor.dev/archive.key | sudo gpg --dearmor --yes -o /usr/share/keyrings/gvisor-archive-keyring.gpg
echo "deb [arch=$(dpkg --print-architecture) signed-by=/usr/share/keyrings/gvisor-archive-keyring.gpg] https://storage.googleapis.com/gvisor/releases release main" \
  | sudo tee /etc/apt/sources.list.d/gvisor.list > /dev/null
sudo apt-get update -qq && sudo apt-get install -y -qq runsc
sudo systemctl reload docker || sudo systemctl restart docker
docker info --format '{{json .Runtimes}}' | grep -q runsc || { echo "runsc is not a docker runtime" >&2; exit 1; }
docker build -q -t sb-candidate "$here"
export SB_RUNTIME=runsc
"${PY:-python3}" -I "$here/../openproblems.py" sandbox-check --work "$(mktemp -d)"
echo "SB_RUNTIME=runsc" >> "${GITHUB_ENV:-/dev/null}"
