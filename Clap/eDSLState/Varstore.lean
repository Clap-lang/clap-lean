import Mathlib.Data.ZMod.Basic
import Std.Data.ExtTreeMap
import Std.Data.ExtTreeMap.Lemmas

namespace Clap

def VarStore (p : ℕ) := Std.ExtTreeMap ℕ (ZMod p) (cmp := compare)
deriving Inhabited

instance {p : ℕ} : EmptyCollection (VarStore p) := inferInstanceAs (EmptyCollection (Std.ExtTreeMap ℕ (ZMod p)))

instance varStoreGetElem? {p : ℕ} : GetElem? (VarStore p) ℕ (ZMod p) (λ Γ x ↦ Γ.contains x) where
  getElem  Γ x h := Γ.get x h
  getElem? Γ x   := Γ.get? x

variable (p : ℕ)

theorem VarStore.getElem?_insert_self {p} (varStrore : VarStore p) k v:
  getElem? (self := varStoreGetElem?) (varStrore.insert k v) k = some v :=
  Std.ExtTreeMap.getElem?_insert_self

end Clap
