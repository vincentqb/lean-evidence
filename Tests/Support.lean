module

public meta import LeanManifests.Basic

public section
meta section

open Lean Elab Command LeanManifests

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

elab "assert_evidence " n:ident " is " kind:str : command => do
  let name ← resolveGlobalConstNoOverload n
  let some evidence := getEvidence? (← getEnv) name
    | throwError "No evidence for {name}"
  unless toString evidence.kind == kind.getString do
    throwError "{name}: expected {kind.getString}, got {evidence.kind}"

elab "assert_assumptions " n:ident " = " "[" deps:ident,* "]" : command => do
  let name ← resolveGlobalConstNoOverload n
  let some evidence := getEvidence? (← getEnv) name
    | throwError "No evidence for {name}"
  let expected ← deps.getElems.mapM resolveGlobalConstNoOverload
  unless evidence.assumptions == expected do
    throwError "{name}: expected assumptions {expected}, got {evidence.assumptions}"

elab "assert_receipts " n:ident " = " p:num "/" t:num : command => do
  let name ← Internal.fullName n
  let some r := getTestResults (← getEnv) name | throwError "No receipts for {name}"
  unless r.passed == p.getNat && r.total == t.getNat do
    throwError "{name}: unexpected receipts {repr r}"

elab "assert_absent " n:ident : command => do
  unless (← resolveGlobalName n.getId).isEmpty do
    throwError "{n} survived a rejected command"

end Tests
