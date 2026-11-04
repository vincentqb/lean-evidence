module

public section
namespace LeanEvidence.Conformance

@[expose] def approxEq (a b : Float) (tolerance : Float := 1e-10) : Bool :=
  (a - b).abs < tolerance

@[expose] def approxEqArray (a b : Array Float) (tolerance : Float := 1e-10) : Bool :=
  a.size == b.size && (Array.zipWith (fun x y => approxEq x y tolerance) a b).all id

@[expose] def normalizedEq (a b : String) : Bool :=
  let normalize (s : String) := (s.replace "\r\n" "\n").trimAscii.toString
  normalize a == normalize b

@[expose] def rowMultisetEq (a b : Array String) : Bool :=
  a.qsort (· < ·) == b.qsort (· < ·)

end LeanEvidence.Conformance
