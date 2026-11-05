module

public meta import LeanEvidence.Report
public meta import Lean.Meta.Constructions.CtorIdx
import Lean.Elab.PreDefinition.Structural.Eqns
import Lean.Elab.PreDefinition.WF.Eqns

public section
meta section

open Lean

namespace LeanEvidence.Audit

private def owner? (env : Environment) (name : Name) : Option Name :=
  env.getModuleIdxFor? name |>.bind fun idx => env.allImportedModuleNames[idx.toNat]?

private def certifiedRecursion (env : Environment) (info : ConstantInfo) : CoreM Bool := do
  let some parent := Compiler.isUnsafeRecName? info.name | return false
  let some parentInfo := env.find? parent | return false
  return !parentInfo.isUnsafe && !parentInfo.isPartial &&
    owner? env parent == owner? env info.name &&
    (← findDeclarationRangesCore? info.name).isNone &&
    ((Elab.Structural.eqnInfoExt.find? env parent).isSome ||
      (Elab.WF.eqnInfoExt.find? env parent).isSome)

private def inductiveParent? (env : Environment) (name : Name) : Option Name :=
  match env.find? name with
  | some (.inductInfo _) => some name
  | some (.ctorInfo info) => some info.induct
  | _ => none

private def generatedParent? (env : Environment) (info : ConstantInfo) : CoreM (Option Name) := do
  if let some projection := env.getProjectionFnInfo? info.name then
    return inductiveParent? env projection.ctorName
  unless (← findDeclarationRangesCore? info.name).isNone do return none
  if Meta.isMatcherCore env info.name || isSparseCasesOn env info.name then
    return some info.name.getPrefix
  if let some parent := Compiler.isUnsafeRecName? info.name then return some parent
  let parent := info.name.getPrefix
  if let some projection := env.getProjectionFnInfo? parent then
    if owner? env parent == owner? env info.name &&
        (info.name == mkDefaultFnOfProjFn parent ||
          info.name == mkInheritedDefaultFnOfProjFn parent) then
      return inductiveParent? env projection.ctorName
  if isAuxRecursor env info.name || isNoConfusion env info.name then
    return inductiveParent? env parent
  if info.name == parent.str "go" && isAuxRecursor env parent &&
      (env.find? parent).any (fun parentInfo =>
        (parentInfo.value?).any (·.getUsedConstants.contains info.name)) then
    return inductiveParent? env parent.getPrefix
  if let some ind := isCtorIdxCore? env info.name then return some ind.name
  if info.name == mkFlatCtorOfStructCtorName parent then
    return inductiveParent? env parent |>.filter (isStructure env)
  if owner? env parent == owner? env info.name then
    if (Elab.Structural.eqnInfoExt.find? env parent).isSome then
      if info.name == Meta.mkSmartUnfoldingNameFor parent then return some parent
      if info.name == parent ++ `_f &&
          (env.find? parent).any (fun parentInfo =>
            (parentInfo.value?).any (·.getUsedConstants.contains info.name)) then
        return some parent
    if let some recursion := Elab.WF.eqnInfoExt.find? env parent then
      if info.name == recursion.declNameNonRec then return some parent
  if let some ind := inductiveParent? env parent then
    if info.name == ind.str "ofNat" && (← isEnumType ind) &&
        (env.find? (ind.str "ofNat_ctorIdx")).any (fun proof =>
          proof.isTheorem && proof.type.getUsedConstants.contains info.name) then
      return some ind
    let instanceName := ind ++ `_sizeOf_inst
    if Meta.isInstanceCore env instanceName then
      if let some instanceInfo := env.find? instanceName then
        if instanceInfo.type.getForallBody.getAppFn.constName? == some ``SizeOf &&
            (instanceInfo.value?).any (·.getUsedConstants.contains info.name) then
          return some ind
    if info.name == instanceName && Meta.isInstanceCore env info.name &&
        info.type.getForallBody.getAppFn.constName? == some ``SizeOf then
      return some ind
  return none

private def isSplitter (env : Environment) (info : ConstantInfo) : CoreM Bool := do
  let hasName := match info.name with
    | .str _ "splitter" => true
    | _ => false
  unless isPrivateName info.name && hasName &&
      !info.isUnsafe && !info.isPartial &&
      (← findDeclarationRangesCore? info.name).isNone do return false
  return Meta.isMatcherCore env info.name.getPrefix ||
    Meta.isMatcherCore env (privateToUserName info.name.getPrefix)

private partial def comptime (env : Environment) (name : Name) : CoreM Bool := do
  if isMarkedMeta env name then return true
  let some info := env.find? name | return false
  if info.isTheorem || (← isSplitter env info) then return true
  let some parent ← generatedParent? env info | return false
  return (← comptime env parent) || (← comptime env (privateToUserName parent))

private def generatedInstanceHelper (env : Environment) (info : ConstantInfo) : CoreM Bool := do
  let parent := info.name.getPrefix
  unless Meta.isInstanceCore env parent && owner? env parent == owner? env info.name do
    return false
  let some parentInfo := env.find? parent | return false
  let some body := parentInfo.value? | return false
  unless body.getUsedConstants.contains info.name do return false
  let some ranges ← findDeclarationRangesCore? info.name | return false
  let some parentRanges ← findDeclarationRangesCore? parent | return false
  return decide (ranges.range = ranges.selectionRange) &&
    decide (ranges.range = parentRanges.range) &&
    decide (ranges.selectionRange = parentRanges.selectionRange)

private def computational (info : ConstantInfo) : MetaM Bool := do
  unless info matches .defnInfo _ | .opaqueInfo _ | .axiomInfo _ do return false
  if ← Meta.isProp info.type then return false
  Meta.forallTelescopeReducing info.type fun _ result => return !(← Meta.whnf result).isSort

private def effects (env : Environment) (type : Expr) : Bool := Id.run do
  let mut pending := type.getUsedConstants
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if seen.contains name then continue
    seen := seen.insert name
    if name == ``IO.RealWorld then return true
    if let some info := env.find? name then
      match info with
      | .inductInfo inductiveInfo => pending := pending ++ inductiveInfo.ctors.toArray
      | .ctorInfo constructor => pending := pending ++ constructor.type.getUsedConstants
      | _ => pure ()
      if let some body := info.value? (allowOpaque := true) then
        pending := pending ++ body.getUsedConstants
  return false

private def foreign? (env : Environment) (name : Name) : Option ForeignEvidence :=
  getForeignEvidence? env name <|>
    (foreignExt.getState env).toArray.findSome? fun (_, entry) =>
      if Compiler.getImplementedBy? env entry.binding == some name then some entry else none

private def validForeign (project : Project) (entry : ForeignEvidence) : MetaM Bool := do
  let env ← getEnv
  let some model := env.find? entry.model | return false
  let some moduleName := owner? env entry.model | return false
  return project.role? moduleName == some .core &&
    !model.isUnsafe && !model.isPartial && !effects env model.type &&
    !isExtern env entry.model && (Compiler.getImplementedBy? env entry.model).isNone &&
    (getEvidence? env entry.assumption).map (·.kind) == some .world &&
    (getEvidence? env entry.fixture).map (·.kind) == some .fixture

private def runtimeAxioms (env : Environment) : CoreM (Array Name) := do
  let mut result := #[]
  for (axiomName, fixture) in (runtimeAxiomExt.getState env).toArray do
    unless (getEvidence? env fixture).map (·.kind) == some .fixture do continue
    unless (env.find? axiomName).any (·.isAxiom) do continue
    if (← collectAxioms fixture).contains axiomName then result := result.push axiomName
  return result

private def dependencies (env : Environment) (info : ConstantInfo) : CoreM (Array Name) := do
  let mut pending := info.getUsedConstantsAsSet.toArray.push info.name
  let mut seen : NameSet := {}
  let mut modules : NameSet := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if seen.contains name then continue
    seen := seen.insert name
    let some dependency := env.find? name
      | throwError "Cannot inspect the compiled dependency {name} of {info.name}"
    if !dependency.isTheorem then
      let some moduleName := owner? env name
        | throwError "Cannot locate the compiled dependency {name} of {info.name}"
      modules := modules.insert moduleName
    if let some replacement := Compiler.getImplementedBy? env name then
      pending := pending.push replacement
    if let some replacement := (Compiler.CSimp.ext.getState env).map.find? name then
      requireProof replacement.thmName
      pending := pending.push replacement.toDeclName
    for initializer in #[getInitFnNameFor? env name, getBuiltinInitFnNameFor? env name] do
      if let some initializer := initializer then pending := pending.push initializer
  return modules.toArray

private def declaration (project : Project) (nativeAxioms : Array Name)
    (info : ConstantInfo) (moduleName : Name) : CoreM DeclarationFact := do
  let env ← getEnv
  let isComputational ← Meta.MetaM.run' <| computational info
  let isRecursion ← certifiedRecursion env info
  let foreign := foreign? env info.name
  let foreignEvidence ← Meta.MetaM.run' <| match foreign with
    | some entry => validForeign project entry
    | none => pure false
  let needsContract := project.role? moduleName == some .core && isComputational &&
    info.type.isForall && !isPrivateName info.name &&
    !Meta.isInstanceCore env info.name && (← generatedParent? env info).isNone &&
    !(← isSplitter env info) &&
    !(← generatedInstanceHelper env info)
  let proofs := getContracts env info.name
  for proof in proofs do requireProof proof
  return {
    name := info.name
    moduleName
    computational := isComputational
    comptime := ← comptime env info.name
    isUnsafe := info.isUnsafe && !isRecursion
    isPartial := info.isPartial && !isRecursion
    effects := isComputational && effects env info.type
    initializes := (getInitFnNameFor? env info.name).isSome ||
      (getBuiltinInitFnNameFor? env info.name).isSome
    external := isExtern env info.name ||
      (Compiler.getImplementedBy? env info.name).isSome || foreign.isSome
    foreignEvidence
    missingBody := (info.value? (allowOpaque := true)).isNone
    axioms := ← collectAxioms info.name
    conformance := (getEvidence? env info.name).map (·.kind) == some .fixture ||
      (getRuntimeAxiomOrigin? env info.name).isSome
    runtimeAxioms := nativeAxioms
    needsContract
    hasContract := !proofs.isEmpty
    dependencies := ← if isComputational then dependencies env info else pure #[]
  }

def collect (project : Project) (catalog : Array Name) : CoreM Inventory := do
  modifyEnv (·.setExporting false)
  let env ← getEnv
  let nativeAxioms ← runtimeAxioms env
  let modules ← catalog.mapM fun name => do
    let some idx := env.getModuleIdx? name | throwError "Compiled module {name} is unavailable"
    let data := env.header.moduleData[idx.toNat]!
    return {
      name
      usesModuleSystem := data.isModule
      imports := data.imports.map fun dependency =>
        { name := dependency.module, comptime := dependency.isMeta }
    }
  let mut declarations := #[]
  for (name, info) in env.constants.toList do
    if let some moduleName := owner? env name then
      if catalog.contains moduleName then
        declarations := declarations.push
          (← withCurrHeartbeats <| declaration project nativeAxioms info moduleName)
  let mut claims := #[]
  for name in project.requirements do
    if !(env.contains name) then continue
    let some moduleName := owner? env name
      | throwError "{name}: cannot locate required inventory"
    unless catalog.contains moduleName do
      throwError "{name}: requirements must belong to a classified project module"
    let checked ← withCurrHeartbeats <| Meta.MetaM.run' <| validateRequirements name
    for claim in checked do
      for declarationName in #[claim.name] ++ claim.evidence.toArray do
        unless (owner? env declarationName).any catalog.contains do
          throwError "{declarationName}: required evidence must belong to a classified project module"
    claims := claims ++ checked
  return {
    modules
    declarations := declarations.qsort (fun a b => a.name.toString < b.name.toString)
    claims
  }

def violations (project : Project) (catalog : Array Name) (inventory : Inventory) : Array String :=
  Id.run do
    let mut errors := #[]
    if project.requirements.isEmpty then
      errors := errors.push "Select at least one compiled Requirements inventory"
    unless decide project.requirements.toList.Nodup do
      errors := errors.push "Duplicate required inventories"
    unless decide (inventory.claims.toList.map (·.name)).Nodup do
      errors := errors.push "Duplicate required claims"
    for name in project.requirements do
      unless inventory.claims.any (·.inventory == name) do
        errors := errors.push s!"Missing required inventory: {name}"
    for claim in inventory.claims do
      unless project.requirements.contains claim.inventory do
        errors := errors.push s!"Unexpected required inventory: {claim.inventory}"
      unless claim.isComplete do
        errors := errors.push s!"Outstanding {repr claim.kind} requirement: {claim.name}"
    unless decide (project.modules.toList.map (·.name)).Nodup do
      errors := errors.push "Duplicate module classifications"
    for name in catalog do
      if (project.role? name).isNone then errors := errors.push s!"Unclassified module: {name}"
      unless inventory.modules.any (·.name == name) do
        errors := errors.push s!"Missing compiled module: {name}"
    for rule in project.modules do
      unless catalog.contains rule.name do errors := errors.push s!"Stale module classification: {rule.name}"
    for fact in inventory.modules do
      unless fact.check project do
        errors := errors.push s!"{fact.name}: use module and import only permitted module roles"
    for fact in inventory.declarations do
      if let some role := project.role? fact.moduleName then
        unless fact.check project role do
          let mut reasons := #[]
          if fact.needsContract && !fact.hasContract then reasons := reasons.push "missing Contract"
          if fact.axioms.any (fun ax => !standardAxioms.contains ax &&
              !(fact.conformance && fact.runtimeAxioms.contains ax)) then
            reasons := reasons.push s!"nonstandard axioms {nonstandardAxioms fact.axioms}"
          if fact.external && !(role == .foreign && fact.foreignEvidence) &&
              !(role == .tooling && fact.comptime) then
            reasons := reasons.push "unregistered foreign implementation"
          if fact.computational then
            if fact.missingBody && !fact.external then reasons := reasons.push "unavailable body"
            if role != .tooling && (fact.isUnsafe || fact.isPartial) &&
                !(fact.external && fact.foreignEvidence) then reasons := reasons.push "unsafe or partial"
            if role == .core && (fact.effects || fact.initializes || fact.external) then
              reasons := reasons.push "effects in core"
            if role == .tooling && !fact.comptime then reasons := reasons.push "runtime code in tooling"
            let forbidden := fact.dependencies.filter (fun target => !project.permits role target false)
            if !forbidden.isEmpty then reasons := reasons.push s!"forbidden dependencies {forbidden}"
          if fact.conformance && role == .core then reasons := reasons.push "runtime evidence in core"
          let reason := String.intercalate "; " reasons.toList
          errors := errors.push s!"{fact.name}: {reason}"
      else errors := errors.push s!"{fact.name}: unclassified owner {fact.moduleName}"
    return errors

def check (project : Project) (catalog : Array Name) : CoreM Inventory := do
  let inventory ← collect project catalog
  unless project.isComplete catalog inventory do
    let errors := String.intercalate "\n" (violations project catalog inventory).toList
    throwError "Project audit failed:\n{errors}"
  return inventory

private def union (left right : Array Name) : Array Name :=
  right.foldl (fun names name => if names.contains name then names else names.push name) left

private def merge (left right : DeclarationFact) : DeclarationFact := {
  left with
  computational := left.computational || right.computational
  comptime := left.comptime && right.comptime
  isUnsafe := left.isUnsafe || right.isUnsafe
  isPartial := left.isPartial || right.isPartial
  effects := left.effects || right.effects
  initializes := left.initializes || right.initializes
  external := left.external || right.external
  foreignEvidence := left.foreignEvidence || right.foreignEvidence
  missingBody := left.missingBody && right.missingBody
  axioms := union left.axioms right.axioms
  conformance := left.conformance || right.conformance
  runtimeAxioms := union left.runtimeAxioms right.runtimeAxioms
  needsContract := left.needsContract || right.needsContract
  hasContract := left.hasContract || right.hasContract
  dependencies := union left.dependencies right.dependencies
}

def inspect (project : Project) (catalog : Array Name) : IO Inventory := do
  let mut imported : NameSet := {}
  for root in catalog do
    let dependencies ← Report.withEnvironment #[{ module := root }] do
      let env ← getEnv
      return catalog.filter fun name => name != root && (env.getModuleIdx? name).isSome
    for dependency in dependencies do imported := imported.insert dependency
  let mut modules : Std.HashMap Name ModuleFact := {}
  let mut declarations : Std.HashMap (Name × Name) DeclarationFact := {}
  let mut claims : Std.HashMap Name ClaimFact := {}
  for root in catalog.filter (fun name => !imported.contains name) do
    let inventory ← Report.withEnvironment #[{ module := root }] do
      let env ← getEnv
      collect project (catalog.filter fun name => (env.getModuleIdx? name).isSome)
    for fact in inventory.modules do modules := modules.insert fact.name fact
    for fact in inventory.declarations do
      let key := (fact.moduleName, fact.name)
      let fact := (declarations[key]?).map (merge · fact) |>.getD fact
      declarations := declarations.insert key fact
    for claim in inventory.claims do
      if let some previous := claims[claim.name]? then
        unless previous.inventory == claim.inventory && previous.kind == claim.kind &&
            previous.evidence == claim.evidence && previous.verified == claim.verified do
          throw <| IO.userError s!"Conflicting compiled requirement: {claim.name}"
      claims := claims.insert claim.name claim
  let inventory := {
    modules := modules.toArray.map Prod.snd |>.qsort (fun a b => a.name.toString < b.name.toString)
    declarations := declarations.toArray.map Prod.snd |>.qsort (fun a b =>
      if a.moduleName == b.moduleName then a.name.toString < b.name.toString
      else a.moduleName.toString < b.moduleName.toString)
    claims := claims.toArray.map Prod.snd |>.qsort (fun a b => a.name.toString < b.name.toString)
    : Inventory
  }
  unless project.isComplete catalog inventory do
    throw <| IO.userError <|
      "Project audit failed:\n" ++ String.intercalate "\n" (violations project catalog inventory).toList
  return inventory

def run (project : Project) (catalog : Array Name) : IO Unit := do
  let inventory ← inspect project catalog
  IO.println s!"Checked {inventory.modules.size} modules, {inventory.declarations.size} declarations, \
    and {inventory.claims.size} required claims"

end LeanEvidence.Audit
