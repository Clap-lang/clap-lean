import Clap.eDSLState.eDSL
import Clap.eDSLState.Spec

import Clap.Lang.Wheels

namespace Clap.Edsl.Lang

abbrev F p := FixedExp p

namespace F

variable {p : ℕ}

def isValid (x : F p) (varStore : VarStore p) : Prop :=
  (x.eval varStore).isSome

instance : IsValid p (F p) := ⟨fun Γ x ↦ F.isValid x Γ⟩

lemma isValid_iff {varStore : VarStore p} {x : F p} :
  IsValid.isValid (α := F p) varStore x ↔ (x.eval varStore).isSome
:= by rfl

lemma isValid_iff_mem {varStore : VarStore p} {x : F p} :
  IsValid.isValid (α := F p) varStore x ↔ x ∈ varStore
:= isValid_iff.trans CircuitStateM.mem_iff_isSome.symm

def isAlwaysValid (x : F p) : Prop := ∀ varStore, x.isValid varStore

instance : VarStoreSize p (F p) where
  size := 1
  toLinear Γ x := #v[x.eval Γ |>.getD 42]

def toZMod (x : F p) (varStore : VarStore p) : Option (ZMod p) := x.eval varStore
def ofZMod (p : ℕ) (v : ZMod p) : F p := .c v

@[simp, grind =]
lemma toZMod_def {varStore : VarStore p} {x : F p} :
  x.toZMod varStore = [varStore|x]
:= rfl

@[simp, grind =]
lemma eval_ofZMod {varStore : VarStore p} {v : ZMod p} :
  [varStore|ofZMod p v] = .some v
:= by simp [ofZMod]

namespace ofZMod

lemma isAlwaysValid (v : ZMod p) : F.isAlwaysValid (F.ofZMod p v) := by
  unfold F.isAlwaysValid F.isValid F.ofZMod
  simp

end ofZMod

instance : Convert p (F p) (ZMod p) where
  toIdeal Γ x := F.toZMod x Γ
  toRepresents := F.ofZMod p
  isValid_iff_isSome_toIdeal := fun _ _ ↦ Iff.rfl
  toIdeal_toRepresents := fun _ _ ↦ by simp
  toRepresents_toIdeal := fun Γ x _ ↦ by simp [Option.some_get]

@[simp, grind =]
lemma toIdeal_def {varStore : VarStore p} {x : F p} :
  Convert.toIdeal varStore x = [varStore|x]
:= rfl

lemma toRepresents_def {v : ZMod p} :
  Convert.toRepresents p (representsT := F p) (idealT := ZMod p) v = F.ofZMod p v
:= rfl

lemma eval_ofZMod_toZMod_of_isValid
  {varStore : VarStore p} {x : F p} (h : x.isValid varStore)
:
  [varStore|(F.ofZMod p ((x.toZMod varStore).get h)) =Γ x]
:= by simp [Option.some_get]

section
variable {p : ℕ} [NeZero p]

def toFin (x : F p) (varStore : VarStore p) : Option (Fin p) :=
  (x.eval varStore).map (ZMod.finEquiv p).symm

def ofFin (p : ℕ) [NeZero p] (n : Fin p) : F p := .c ((ZMod.finEquiv p) n)

@[simp, grind =]
lemma toFin_def {varStore : VarStore p} {x : F p} :
  x.toFin varStore = (x.eval varStore).map (ZMod.finEquiv p).symm
:= rfl

@[simp, grind =]
lemma eval_ofFin {varStore : VarStore p} {n : Fin p} :
  [varStore|ofFin p n] = .some ((ZMod.finEquiv p) n)
:= by simp [ofFin]

instance : Convert p (F p) (Fin p) where
  toIdeal Γ x := F.toFin x Γ
  toRepresents := F.ofFin p
  isValid_iff_isSome_toIdeal Γ x := by unfold_projs; simp [F.isValid, F.toFin]
  toIdeal_toRepresents Γ n := by simp [F.toFin, F.ofFin]
  toRepresents_toIdeal Γ x h := by simp [F.toFin, F.ofFin, Option.some_get]

lemma toIdeal_def_fin {varStore : VarStore p} {x : F p} :
  Convert.toIdeal (representsT := F p) (idealT := Fin p) varStore x = F.toFin x varStore
:= rfl

lemma toRepresents_def_fin {n : Fin p} :
  Convert.toRepresents p (representsT := F p) (idealT := Fin p) n = F.ofFin p n
:= rfl

end

end F

end Clap.Edsl.Lang
