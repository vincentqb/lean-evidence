module

public import LeanEvidenceTests.Fixtures.Core
public meta import LeanEvidence

public section

namespace LeanEvidenceTests.Fixtures

initialize counter : IO.Ref Nat ← IO.mkRef 0

partial def drain (stream : IO.FS.Stream) : IO Unit := do
  let line ← stream.getLine
  unless line.isEmpty do drain stream

@[exercises ClockAdvances] def clockSuite : IO Unit := do
  let first ← IO.monoMsNow
  let second ← IO.monoMsNow
  unless first ≤ second do throw (IO.userError "the monotonic clock ran backwards")

end LeanEvidenceTests.Fixtures
