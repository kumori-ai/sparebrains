/-! The judge-isolation canary (tools/judge_isolation_canary.py). Candidate files can run IO
while Lean elaborates them, so this one goes looking for the planted secret SB_CANARY: in its
own environment, and in every /proc/<pid>/environ it is allowed to read. -/

def probeProc : IO (Nat × Nat) := do
  let mut scanned := 0
  let mut hits := 0
  for entry in (← System.FilePath.readDir "/proc") do
    try
      let bytes ← IO.FS.readBinFile (entry.path / "environ")
      scanned := scanned + 1
      if let some s := String.fromUTF8? bytes then
        let parts := s.splitOn "SB_CANARY="
        if parts.length > 1 then
          hits := hits + 1
          IO.println s!"PROBE leak {(parts.getD 1 "").takeWhile (· != '\x00')}"
    catch _ => pure ()
  return (scanned, hits)

#eval show IO Unit from do
  IO.println s!"PROBE direct {(← IO.getEnv "SB_CANARY").getD "none"}"
  let (scanned, hits) ← probeProc
  IO.println s!"PROBE scanned {scanned} hits {hits}"

theorem env_leak_probe : True := trivial
