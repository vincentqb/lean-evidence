module

public meta import LeanEvidence.Policy
public meta import Lean

public section
meta section

open Lean Elab Command

namespace LeanEvidence

inductive EvidenceKind where
  | test | check | suite
  deriving BEq

structure Evidence where
  claim : Name
  kind : EvidenceKind
  source : Name := .anonymous

initialize claimsExt : SimplePersistentEnvExtension (Name × ClaimKind) (Array (Name × ClaimKind)) ←
  registerSimplePersistentEnvExtension { addEntryFn := Array.push, addImportedFn := Array.flatten }

initialize evidenceExt : SimplePersistentEnvExtension Evidence (Array Evidence) ←
  registerSimplePersistentEnvExtension { addEntryFn := Array.push, addImportedFn := Array.flatten }

def registeredClaims (env : Environment) : Array (Name × ClaimKind) := claimsExt.getState env

def claimKind? (env : Environment) (name : Name) : Option ClaimKind :=
  (registeredClaims env).findSome? fun (claim, kind) => if claim == name then some kind else none

def allEvidence (env : Environment) : Array Evidence := evidenceExt.getState env

def nonstandardAxioms (name : Name) : CoreM (Array Name) :=
  return (← collectAxioms name).filter (!standardAxioms.contains ·)

private def checked (cmd : Syntax) : CommandElabM Unit := do
  let errors := fun (messages : MessageLog) =>
    (messages.toList.filter (·.severity == .error)).length
  let before := errors (← get).messages
  withScope (fun scope => { scope with opts := Elab.async.set scope.opts false }) do
    elabCommand cmd
  if errors (← get).messages > before then throwError "declaration failed to elaborate"

private def declareClaim (doc? : Option (TSyntax `Lean.Parser.Command.docComment)) (n : Ident)
    (binders : TSyntaxArray `Lean.Parser.Term.bracketedBinder) (body : Term) (kind : ClaimKind) :
    CommandElabM Unit := do
  checked (← `($[$doc?]? @[expose, reducible] public def $n $binders* : Prop := $body))
  let name ← resolveGlobalConstNoOverload n
  modifyEnv (claimsExt.addEntry · (name, kind))

elab doc?:(docComment)? "WorldClaim " n:ident bs:(ppSpace bracketedBinder)* " := " t:term : command => do
  unless doc?.isSome do
    throwError "WorldClaim {n} needs a doc comment naming the observation that would falsify it"
  declareClaim doc? n bs t .world

elab doc?:(docComment)? "Conjecture " n:ident bs:(ppSpace bracketedBinder)* " := " t:term : command =>
  declareClaim doc? n bs t .conjecture

private def claimHead (claim : Term) : CommandElabM Name := liftTermElabM do
  let head := (← instantiateMVars (← Term.elabTermEnsuringType claim (mkSort .zero))).getAppFn.constName
  unless (claimKind? (← getEnv) head).isSome do throwError "{claim} is not a WorldClaim or Conjecture"
  return head

private def requireInstance (claim inst : Term) : CommandElabM Unit := do
  try checked (← `(example : $claim → $inst := fun h => by first | exact h | apply h))
  catch _ => throwError "{inst} is not an instance of {claim}"

elab "Test " claim:term " : " inst:term " := " proof:term : command => do
  let head ← claimHead claim
  requireInstance claim inst
  let env ← getEnv
  let mut index := 1
  while env.contains (mkPrivateName env (head ++ Name.mkSimple s!"test_{index}")) do
    index := index + 1
  let name := head ++ Name.mkSimple s!"test_{index}"
  checked (← `(private theorem $(mkIdent (rootNamespace ++ name)) : $inst := $proof))
  let axioms ← liftCoreM <| nonstandardAxioms (mkPrivateName env name)
  unless axioms.isEmpty do
    throwError "A Test must be kernel-checked; it depends on {axioms}. Use Check to run code."
  modifyEnv (evidenceExt.addEntry · { claim := head, kind := .test })

elab "Check " claim:term " : " inst:term : command => do
  let head ← claimHead claim
  requireInstance claim inst
  unless ← liftTermElabM (unsafe Term.evalTerm Bool (mkConst ``Bool) (← `(decide ($inst)))) do
    throwError "Check failed: {inst} is false when compiled and run"
  modifyEnv (evidenceExt.addEntry · { claim := head, kind := .check })

syntax (name := exercises) "exercises " ident : attr

initialize registerBuiltinAttribute {
  name := `exercises
  descr := "Marks a live suite as evidence for a claim it exercises at run time."
  add := fun suite stx kind => do
    unless kind == .global do throwError "exercises must be a global attribute"
    let `(attr| exercises $claim:ident) := stx | throwUnsupportedSyntax
    let name ← realizeGlobalConstNoOverloadWithInfo claim
    unless (claimKind? (← getEnv) name).isSome do
      throwError "{name} is not a WorldClaim or Conjecture"
    modifyEnv (evidenceExt.addEntry · { claim := name, kind := .suite, source := suite })
}

end LeanEvidence
