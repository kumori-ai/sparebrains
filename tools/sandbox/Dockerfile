# One openproblems candidate's container (tools/openproblems.py docker_cmd). Built once per job; candidates run it
# with no network, a read-only root and only their own inputs mounted. python:3.12-slim pinned by digest
# (Docker Hub, 2026-10-21); the runner's own venv is Python 3.12 too.
FROM python:3.12-slim@sha256:cb33f7f771ecec2ef1225cf39b159591a040391bd73e4c01f00fdfc4c47611d2
COPY requirements.txt /tmp/requirements.txt
RUN pip install --no-cache-dir -r /tmp/requirements.txt && rm /tmp/requirements.txt
USER 65534:65534
