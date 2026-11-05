module

public meta import LeanEvidence.Commands

public section
meta section

open Lean Elab Command LeanEvidence

namespace Tests

elab "rejects " reason:str " in " cmd:command : command => do
  let saved ← get
  let oldCount := saved.messages.toList.length
  let mut diagnostics : Array String := #[]
  try
    withScope (fun scope => { scope with opts := Elab.async.set scope.opts false }) do
      elabCommand cmd
    for message in (← get).messages.toList.drop oldCount do
      if message.severity == .error then
        diagnostics := diagnostics.push (← message.data.toString)
  catch error =>
    diagnostics := diagnostics.push (← error.toMessageData.toString)
  set saved
  unless diagnostics.any (fun text => (text.splitOn reason.getString).length > 1) do
    throwError "Expected rejection containing {reason.getString}, got {diagnostics}"

elab "assert_absent " n:ident : command => do
  unless (← resolveGlobalName n.getId).isEmpty do
    throwError "{n} survived a rejected command"

elab "assert_claim " n:ident " is " kind:ident : command => do
  let name ← resolveGlobalConstNoOverload n
  let expected := if kind.getId == `world then ClaimKind.world else .conjecture
  unless claimKind? (← getEnv) name == some expected do
    throwError "{name}: expected a {kind.getId} claim"

elab "assert_evidence " n:ident " = " tests:num " tests " checks:num " checks" : command => do
  let name ← resolveGlobalConstNoOverload n
  let found := evidenceFor (← getEnv) name
  let kernel := (found.filter (!·.native)).size
  let native := (found.filter (·.native)).size
  unless kernel == tests.getNat && native == checks.getNat do
    throwError "{name}: {kernel} tests and {native} checks"

end Tests
