module

public import SoftwareChallengeTests.Fixtures.Core
public meta import SoftwareChallenge

public section

namespace SoftwareChallengeTests.Fixtures

initialize counter : IO.Ref Nat ← IO.mkRef 0

partial def drain (stream : IO.FS.Stream) : IO Unit := do
  let line ← stream.getLine
  unless line.isEmpty do drain stream

partial def loopIdentity (n : Nat) : IO Unit := do
  unless identity n == n do loopIdentity (n + 1)

@[exercises ClockAdvances] def clockSuite : IO Unit := do
  let first ← IO.monoMsNow
  let second ← IO.monoMsNow
  unless first ≤ second do throw (IO.userError "the monotonic clock ran backwards")

end SoftwareChallengeTests.Fixtures
