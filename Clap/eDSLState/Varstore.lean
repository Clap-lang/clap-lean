import Mathlib.Data.ZMod.Basic
import Std.Data.ExtTreeMap

namespace Clap

def VarStore (p : ℕ) := Std.ExtTreeMap ℕ (ZMod p) (cmp := compare)
deriving Inhabited

instance {p : ℕ} : EmptyCollection (VarStore p) := inferInstanceAs (EmptyCollection (Std.ExtTreeMap ℕ (ZMod p)))

instance {p : ℕ} : GetElem? (VarStore p) ℕ (ZMod p) (λ Γ x ↦ Γ.contains x) where
  getElem  Γ x h := Γ.get x h
  getElem? Γ x   := Γ.get? x

end Clap
