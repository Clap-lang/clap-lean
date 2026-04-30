import Lean
import Clap.Compiler.Traverse
import Mathlib.Lean.CoreM

set_option maxRecDepth 10000 in
#eval Clap.Compiler.ExampruSym.profileThis
