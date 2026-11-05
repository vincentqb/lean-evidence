module

public import Examples.ConstantFolding.Core

public section

namespace Examples.ConstantFolding.Shell

@[expose] def output (e : Expr) : String := toString (evalNative (fun _ => 0) (fold e))

def run (e : Expr) : IO Unit := IO.println (output e)

end Examples.ConstantFolding.Shell
