# Failure triage 2026-W43 (answered rejects to 2026-10-26)

Read from the ledger by tools/triage.py: 39,377 answered rejects over 97 lanes (852 unclassified, 0 unattributed). Ranked by cross-lane demand; a candidate is >=40% of some lane's rejects (lane n>=100) or in the top 5. Recoverability is unknown until a replay measures it.

| class | all lanes | last week | lanes | past a lane's bar | existing tool | frozen replies, by signature |
|---|---:|---:|---:|---|---|---|
| tactic_failed | 9,805 | 2,283 | 87 | meganova-l3-70b-euryale-v2-1, meganova-mistral-small-3-2-24b-instruct-2506, meganova-mn-violet-lotus-12b, openrouter-minimax-m3, vercel-minimax-m3-free | - | groq-allam: 26 of 26 (fenced_lean4 9, unfenced_lean4 17; 0 truncated; 1 database-only) |
| unknown_name | 8,578 | 1,435 | 80 | routeway-gemma-4-26b-a4b-it-chimerax | fixer names pass | groq-allam: 80 of 80 (fenced_lean4 20, lean3_body 12, prose 4, unfenced_lean4 44; 11 truncated; 1 database-only) |
| unsolved_goals | 4,781 | 974 | 84 | - | the loop's holes and automation | groq-allam: 109 of 109 (fenced_lean4 15, lean3_body 10, prose 1, unfenced_lean4 83; 9 truncated; 5 database-only) |
| no_fence | 4,424 | 104 | 45 | groq-allam, opencode_zen-mimo-v2.5-free, openrouter-laguna-xs-2-1 | proof_text.recover_lean3 (lean3_body) | groq-allam: 780 of 780 (fenced_lean4 50, lean3_body 476, prose 252, unfenced_lean4 2; 260 truncated; 45 database-only) |
| lean3_syntax | 3,987 | 228 | 50 | - | fixer lean3 pass | groq-allam: 98 of 98 (fenced_lean4 14, lean3_body 21, unfenced_lean4 63; 17 truncated; 6 database-only) |
| other | 3,159 | 776 | 65 | mistral-leanstral-1-5 | - | groq-allam: 11 of 11 (fenced_lean4 6, lean3_body 1, unfenced_lean4 4; 0 truncated; 3 database-only) |
