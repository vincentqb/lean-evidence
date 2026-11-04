module

public section

namespace Examples.ConstantFolding

inductive Expr where
  | lit (value : Nat)
  | var (index : Nat)
  | add (left right : Expr)
  deriving Repr, DecidableEq

def eval (env : Nat → Nat) : Expr → Nat
  | .lit n => n
  | .var x => env x
  | .add a b => eval env a + eval env b

inductive Evaluates (env : Nat → Nat) : Expr → Nat → Prop where
  | lit (n : Nat) : Evaluates env (.lit n) n
  | var (x : Nat) : Evaluates env (.var x) (env x)
  | add {a b : Expr} {x y : Nat} :
      Evaluates env a x → Evaluates env b y → Evaluates env (.add a b) (x + y)

private def combine : Expr → Expr → Expr
  | .lit a, .lit b => .lit (a + b)
  | a, b => .add a b

def fold : Expr → Expr
  | .lit n => .lit n
  | .var x => .var x
  | .add a b => combine (fold a) (fold b)

def nodeCount : Expr → Nat
  | .lit _ => 1
  | .var _ => 1
  | .add a b => 1 + nodeCount a + nodeCount b

end Examples.ConstantFolding
