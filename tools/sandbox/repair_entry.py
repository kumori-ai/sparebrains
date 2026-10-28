"""Inside the candidate container only (tools/lane_repair.py): a lane-written repair pass on stored rejects.
Reads JSON lines {"id", "proof", "lean_output"} on stdin, imports repair() from /app/cand.py, writes
{"id", "proof"} per line on stdout (the repaired proof, or the input unchanged), and a candidate's crash goes to
stderr with a nonzero exit. Nothing else is on stdout, so there is no output file to trust."""
import json, os, sys
from pathlib import Path

ns = {"__name__": "candidate"}
exec(compile(Path(sys.argv[1]).read_text(), "candidate.py", "exec"), ns)
repair = ns["repair"]
out = os.fdopen(os.dup(1), "w")
os.dup2(2, 1)
sys.stdout = sys.stderr
for line in sys.stdin:
    if not line.strip():
        continue
    item = json.loads(line)
    got = repair(item["proof"], item.get("lean_output") or "")
    out.write(json.dumps({"id": item["id"], "proof": got if isinstance(got, str) else item["proof"]}) + "\n")
out.flush()
