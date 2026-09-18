import Mathlib.Data.ZMod.Basic
import Clap.eDSLState.Monad
import Clap.eDSLState.Varstore

namespace Clap

class IsValid (p : ℕ) (α : Type) where
  isValid : VarStore p → HashConsSt p → α → Prop

class VarStoreSize (p : ℕ) (α : Type) where
  size : ℕ
  toLinear : (VarStore p) → α → Vector (ZMod p) size

attribute [reducible] VarStoreSize.size

instance instVarStoreSizeUnit {p : ℕ} : VarStoreSize p Unit where
  size := 0
  toLinear _ _ := #v[]

@[grind =]
lemma instVarStoreSizeUnit_size {p : ℕ}:
  (@instVarStoreSizeUnit p).size = 0
:= rfl

@[grind =]
lemma instVarStoreSizeUnit_size' {p : ℕ}:
  @VarStoreSize.size p Unit instVarStoreSizeUnit = 0
:= rfl

-- set_option pp.all true in
@[grind =]
lemma instVarStoreSizeUnit_toLinear
  {p : ℕ}
  {varStore : VarStore p}
  {x : Unit}
:
  (@instVarStoreSizeUnit p).toLinear varStore x =
  @Vector.mk _ 0 #[] (by simp)
:= rfl

end Clap
