import Clap.Lang.Core.F.mkF
import Clap.Lang.Core.FB.eq
import Clap.Lang.Core.Combinators.mapM
import Clap.Lang.Data.JWT.Scaffold.bracketsMap
namespace Clap.Lang

variable {p : ℕ}

def bracketsMap [p.AtLeastTwo] {w} (input : FVec p w) : ClapM p (FVec p w) := do
  input.mapM (fun c ↦ do
    let eqOpen ← eq c (← mkF '{'.toNat)
    let eqClose ← eq c (← mkF '}'.toNat)
    eqOpen - eqClose
    )

namespace bracketsMap

lemma convertsM
  [p.AtLeastTwo]
  {k}
  {state : ClapMState p}
  {a : FVec p k}
  {a_val : Vector (ZMod p) k}
  (h_a : Converts FVec.conversion state a a_val)
  (h_p : 2 ^ (8 + 1) < p)
:
  ConvertsM FVec.conversion (bracketsMap a) state
    (a_val.map fun c : ZMod p ↦
      if c == '{'.toNat then 1 else if c == '}'.toNat then -1 else 0
    )
    True
:= convertsM_mapM (FVec.converts_iff_F_converts.mp h_a) (step_convertsM h_p)

end bracketsMap

end Clap.Lang
