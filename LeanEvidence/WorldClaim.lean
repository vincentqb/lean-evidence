module

public meta import LeanEvidence.Basic

public section
meta section

namespace LeanEvidence
open Lean Elab Command Internal

syntax (name := worldClaimSyn)
  (docComment)? "WorldClaim " ident " := " term : command

@[command_elab worldClaimSyn]
def elabWorldClaim : CommandElab := fun stx => do
  match stx with
  | `($[$doc?:docComment]? WorldClaim $n:ident := $t:term) =>
    unless doc?.isSome do
      throwError "WorldClaim {n} requires a doc comment describing the assumption and a falsifying observation"
    checkedCommand (← `(@[expose] public def $n : Prop := $t))
    let name ← fullName n
    mark name .world
    attachDoc doc? name
  | _ => throwUnsupportedSyntax

end LeanEvidence
