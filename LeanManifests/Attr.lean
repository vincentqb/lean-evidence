module

public meta import Lean

public section
meta section

open Lean

namespace LeanManifests

inductive EvidenceKind where
  | proven | derived | unproven | tested | failing | sketch | world | unitTest | fixture
  deriving BEq, ReflBEq, LawfulBEq, Inhabited, Repr

instance : ToString EvidenceKind where
  toString
    | .proven => "ProvenTheorem"
    | .derived => "DerivedConjecture"
    | .unproven => "UnprovenConjecture"
    | .tested => "TestedConjecture"
    | .failing => "FailingConjecture"
    | .sketch => "Sketch"
    | .world => "WorldClaim"
    | .unitTest => "UnitTest"
    | .fixture => "ConformanceFixture"

def EvidenceKind.requiresProof : EvidenceKind → Bool
  | .proven | .unitTest => true
  | _ => false

structure Evidence where
  kind : EvidenceKind
  assumptions : Array Name := #[]
  ownHole : Bool := false
  deriving Inhabited, Repr

def Evidence.assumptionNames (e : Evidence) (n : Name) : Array Name :=
  if e.ownHole then #[n] else e.assumptions

def Evidence.isComplete (e : Evidence) : Bool :=
  e.kind.requiresProof || (e.kind == .derived && e.assumptions.isEmpty)

def Evidence.needsWork (e : Evidence) : Bool :=
  match e.kind with
  | .sketch | .unproven | .tested | .failing => true
  | .derived => !e.assumptions.isEmpty
  | _ => false

initialize evidenceExt : SimplePersistentEnvExtension (Name × Evidence)
    (Std.HashMap Name Evidence) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m (n, e) => m.insert n e
    addImportedFn := fun entries => Id.run do
      let mut m := {}
      for a in entries do
        for (n, e) in a do m := m.insert n e
      return m
  }

def getEvidence? (env : Environment) (n : Name) : Option Evidence :=
  (evidenceExt.getState env)[n]?

def standardAxioms : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

def nonstandardAxioms (axioms : Array Name) : Array Name :=
  axioms.filter (!standardAxioms.contains ·)

def unexpectedAxioms (n : Name) : CoreM (Array Name) := do
  return nonstandardAxioms (← collectAxioms n)

def requireProof (n : Name) : CoreM Unit := do
  let axioms ← unexpectedAxioms n
  unless axioms.isEmpty do
    throwError "{n} depends on nonstandard axioms: {axioms}. A proved entry may use only propext, Classical.choice, and Quot.sound."

def namedAssumptions (root : Name) : CoreM (Array Name) := do
  let env := (← getEnv).setExporting false
  let axioms ← unexpectedAxioms root
  for ax in axioms do
    unless ax == ``sorryAx do
      throwError "{root} depends on an unregistered axiom: {ax}"
  let mut todo := #[root]
  let mut visited : NameSet := {}
  let mut frontier : Array Name := #[]
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if visited.contains n then continue
    visited := visited.insert n
    if (← unexpectedAxioms n).isEmpty then continue
    if let some e := getEvidence? env n then
      let assumptions := e.assumptionNames n
      if !assumptions.isEmpty then
        for dep in assumptions do
          if !frontier.contains dep then frontier := frontier.push dep
        continue
    let some info := env.find? n
      | throwError "Cannot inspect the assumed dependency {n}"
    let deps := info.getUsedConstantsAsSet
    if deps.contains ``sorryAx then
      throwError "{root} uses raw sorry in {n}; declare the assumption in a manifest."
    unless (info.value? (allowOpaque := true)).isSome do
      throwError "Cannot name assumptions behind the hidden body of {n}. Use import all for this package's proof module."
    for dep in deps.toArray do todo := todo.push dep
  if !axioms.isEmpty && frontier.isEmpty then
    throwError "Cannot recover the named assumptions of {root}"
  return frontier.qsort (fun a b => a.toString < b.toString)

syntax (name := theoremsAttr) "theorems" ident+ : attr

initialize theoremsExtension : SimplePersistentEnvExtension (Name × Array Name)
    (Std.HashMap Name (Array Name)) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m (n, claims) => m.insert n claims
    addImportedFn := fun entries => Id.run do
      let mut m := {}
      for a in entries do
        for (n, claims) in a do
          let previous := (m[n]?).getD #[]
          m := m.insert n (claims.foldl
            (fun acc claim => if acc.contains claim then acc else acc.push claim) previous)
      return m
  }

initialize registerBuiltinAttribute {
    name := `theoremsAttr
    descr := "author-supplied links from an API declaration to manifest claims"
    add := fun n stx kind => do
      unless kind == .global do throwError "theorems requires a global attribute"
      let claims ← match stx with
        | `(attr| theorems $ns:ident*) => ns.mapM resolveGlobalConstNoOverload
        | _ => throwError "invalid theorems attribute"
      for claim in claims do
        unless (getEvidence? (← getEnv) claim).isSome do
          throwError "{claim} has no manifest evidence"
      let previous := ((theoremsExtension.getState (← getEnv))[n]?).getD #[]
      let merged := claims.foldl
        (fun acc claim => if acc.contains claim then acc else acc.push claim) previous
      modifyEnv fun env => theoremsExtension.addEntry env (n, merged)
  }

def getTheorems? (env : Environment) (n : Name) : Option (Array Name) :=
  (theoremsExtension.getState env)[n]?

syntax (name := dependsOnAttr) "depends_on" ident+ : attr
initialize dependsOnExtension : ParametricAttribute (Array Name) ←
  registerParametricAttribute {
    name := `dependsOnAttr
    descr := "author-supplied work dependencies; not proof dependencies"
    getParam := fun _ stx => match stx with
      | `(attr| depends_on $ns:ident*) => ns.mapM resolveGlobalConstNoOverload
      | _ => throwError "invalid depends_on attribute"
  }

def getDependsOn? (env : Environment) (n : Name) : Option (Array Name) :=
  dependsOnExtension.getParam? env n

syntax (name := estimatedMinutesAttr) "estimated_minutes" num : attr
initialize estimatedMinutesExtension : ParametricAttribute Nat ←
  registerParametricAttribute {
    name := `estimatedMinutesAttr
    descr := "author-supplied effort estimate in minutes"
    getParam := fun _ stx => match stx with
      | `(attr| estimated_minutes $n) => return n.getNat
      | _ => throwError "invalid estimated_minutes attribute"
  }

def getEstimatedMinutes? (env : Environment) (n : Name) : Option Nat :=
  estimatedMinutesExtension.getParam? env n

initialize entryPointAttr : TagAttribute ←
  registerTagAttribute `entry_point "author-supplied work entry point"

def isEntryPoint (env : Environment) (n : Name) : Bool :=
  entryPointAttr.hasTag env n

end LeanManifests
