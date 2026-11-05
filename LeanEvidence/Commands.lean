module

public meta import LeanEvidence.Spec
public meta import Lean

public section
meta section

open Lean Elab Command

namespace LeanEvidence

structure Evidence where
  claim : Name
  statement : String
  native : Bool
  deriving Inhabited, Repr

initialize claimsExt : SimplePersistentEnvExtension (Name × ClaimKind)
    (Std.HashMap Name ClaimKind) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun claims (name, kind) => claims.insert name kind
    addImportedFn := fun entries => entries.foldl (init := {}) fun claims module =>
      module.foldl (init := claims) fun claims (name, kind) => claims.insert name kind
  }

initialize evidenceExt : SimplePersistentEnvExtension Evidence
    (Std.HashMap Name (Array Evidence)) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun found entry =>
      found.insert entry.claim ((found[entry.claim]?).getD #[] |>.push entry)
    addImportedFn := fun entries => entries.foldl (init := {}) fun found module =>
      module.foldl (init := found) fun found entry =>
        found.insert entry.claim ((found[entry.claim]?).getD #[] |>.push entry)
  }

def claimKind? (env : Environment) (name : Name) : Option ClaimKind :=
  (claimsExt.getState env)[name]?

def registeredClaims (env : Environment) : Array (Name × ClaimKind) :=
  (claimsExt.getState env).toArray

def evidenceFor (env : Environment) (claim : Name) : Array Evidence :=
  (evidenceExt.getState env)[claim]?.getD #[]

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

elab doc?:(docComment)? "WorldClaim " n:ident bs:bracketedBinder* " := " t:term : command => do
  unless doc?.isSome do
    throwError "WorldClaim {n} needs a doc comment naming the observation that would falsify it"
  declareClaim doc? n bs t .world

elab doc?:(docComment)? "Conjecture " n:ident bs:bracketedBinder* " := " t:term : command =>
  declareClaim doc? n bs t .conjecture

private def claimHead (claim : Term) : CommandElabM Name := liftTermElabM do
  let statement ← instantiateMVars (← Term.elabTermEnsuringType claim (mkSort .zero))
  let some head := statement.getAppFn.constName?
    | throwError "{claim} must apply a WorldClaim or Conjecture"
  unless (claimKind? (← getEnv) head).isSome do
    throwError "{head} is not a WorldClaim or Conjecture"
  return head

private def record (claim : Name) (inst : Term) (native : Bool) : CommandElabM Unit := do
  let statement := (inst.raw.reprint.getD (toString inst)).trimAscii.toString
  modifyEnv (evidenceExt.addEntry · { claim, statement, native })

private def requireInstance (claim inst : Term) : CommandElabM Unit := do
  try checked (← `(example : $claim → $inst := fun h => by first | exact h | apply h))
  catch _ => throwError "{inst} is not an instance of {claim}"

elab "Test " claim:term " : " inst:term " := " proof:term : command => do
  let head ← claimHead claim
  requireInstance claim inst
  let env ← getEnv
  let mut index := 1
  while env.contains (head ++ Name.mkSimple s!"test_{index}") do index := index + 1
  let name := head ++ Name.mkSimple s!"test_{index}"
  checked (← `(public theorem $(mkIdent (rootNamespace ++ name)) : $inst := $proof))
  let axioms ← liftCoreM <| nonstandardAxioms name
  unless axioms.isEmpty do
    throwError "A Test must be kernel-checked; it depends on {axioms}. Use Check to run code."
  record head inst false

private unsafe def evaluateUnsafe (term : Term) : TermElabM Bool :=
  Term.evalTerm Bool (mkConst ``Bool) term

@[implemented_by evaluateUnsafe] private opaque evaluate (term : Term) : TermElabM Bool

elab "Check " claim:term " : " inst:term : command => do
  let head ← claimHead claim
  requireInstance claim inst
  unless ← liftTermElabM (evaluate (← `(decide ($inst)))) do
    throwError "Check failed: {inst} is false when compiled and run"
  record head inst true

end LeanEvidence
