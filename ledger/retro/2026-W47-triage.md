# Failure triage 2026-W47 (answered rejects to 2026-11-23)

Read from the ledger by tools/triage.py: 50,982 answered rejects over 108 lanes (937 unclassified, 0 unattributed). Ranked by cross-lane demand; a candidate is >=40% of some lane's rejects (lane n>=100) or in the top 5. Recoverability is unknown until a replay measures it.

| class | all lanes | last week | lanes | past a lane's bar | existing tool | frozen replies, by signature |
|---|---:|---:|---:|---|---|---|
| tactic_failed | 12,740 | 263 | 100 | openrouter-minimax-m3, vercel-minimax-m3-free | - | groq-allam: 26 of 26 (fenced_lean4 9, unfenced_lean4 17; 0 truncated; 1 database-only) |
| unknown_name | 11,203 | 214 | 92 | - | fixer names pass | groq-allam: 80 of 80 (fenced_lean4 20, lean3_body 12, prose 4, unfenced_lean4 44; 11 truncated; 1 database-only) |
| unsolved_goals | 6,151 | 133 | 95 | - | the loop's holes and automation | groq-allam: 109 of 109 (fenced_lean4 15, lean3_body 10, prose 1, unfenced_lean4 83; 9 truncated; 5 database-only) |
| no_fence | 4,701 | 25 | 66 | groq-allam, opencode_zen-mimo-v2.5-free, openrouter-laguna-xs-2-1 | proof_text.recover_lean3 (lean3_body) | groq-allam: 780 of 780 (fenced_lean4 50, lean3_body 476, prose 252, unfenced_lean4 2; 260 truncated; 45 database-only) |
| other | 4,262 | 96 | 73 | mistral-leanstral-1-5 | - | groq-allam: 11 of 11 (fenced_lean4 6, lean3_body 1, unfenced_lean4 4; 0 truncated; 3 database-only) |
