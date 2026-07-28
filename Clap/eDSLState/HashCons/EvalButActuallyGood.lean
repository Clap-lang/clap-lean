import Clap.eDSLState.HashCons.HashConsM

namespace Clap.HashConsM

abbrev ValueCache (p : ℕ) := Array (Option (ZMod p))

def Barney {p} (Γ : VarStore p) (expr : CacheExpr p) (cache : ValueCache p) : Option (ZMod p) :=
  match expr with
  | .c k => .some k
  | .v idx => Γ[idx]?
  | .binary_op lhs rhs op =>
    let op := match op with
              | .add => (· + ·)
              | .sub => (· - ·)
              | .mul => (· * ·)
    let lhs := cache[lhs]!
    let rhs := cache[rhs]!
    op <$> lhs <*> rhs

def evalWithCache {p}
  (varStore : VarStore p) (e : ExprRef) (cache : ValueCache p) (σ : HashConsSt p) : ValueCache p :=
  if e < cache.size
  then cache
  else match σ[e]? with
       | .none => cache
       | .some expr => let val := Barney varStore expr cache
                       evalWithCache varStore e (cache.push val) σ
  termination_by (e + 1) - cache.size
  decreasing_by grind
 
def eval {p} (varStore : VarStore p) (e : ExprRef) (σ : HashConsSt p) : Option (ZMod p) :=
  (evalWithCache varStore e #[] σ)[e]!

end Clap.HashConsM
