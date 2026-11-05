module

public import Tests.Fixtures.Core

public section

namespace Tests.Fixtures

initialize counter : IO.Ref Nat ← IO.mkRef 0

partial def drain (stream : IO.FS.Stream) : IO Unit := do
  let line ← stream.getLine
  unless line.isEmpty do drain stream

def report (n : Nat) : IO Unit := IO.println (successor n)

end Tests.Fixtures
