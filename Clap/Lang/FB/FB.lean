import Clap.Lang.F.F
import Clap.eDSLState.Spec

namespace Clap.Edsl.Lang

abbrev FB p := F p

namespace FB

def true (p : ℕ) [Fact (p ≥ 2)] : FB p := .c 1
def false (p : ℕ) [Fact (p ≥ 2)] : FB p := .c 0

variable {p : ℕ} [Fact (p ≥ 2)]

def isValid (x : FB p) (varStore : ℕ → Option (ZMod p)) : Prop :=
  x.eval varStore = .some 0 ∨
  x.eval varStore = .some 1

def isAlwaysValid (x : FB p) : Prop :=
  ∀ varStore, x.isValid varStore

def toBool (x : FB p) (varStore : ℕ → Option (ZMod p)) : Bool :=
  x.eval varStore == .some 1

def ofBool (p : ℕ) [Fact (p ≥ 2)] (x : Bool) : FB p :=
  if x then FB.true p else FB.false p  

@[simp, grind .] -- TODO(provisional `simp`)
lemma eval_ofBool_toBool_of_isValid
  {p : ℕ}
  {varStore : ℕ → Option (ZMod p)}
  (f: FB p)
  (h : f.isValid varStore)
  [Fact (p ≥ 2)]
:
  (FB.ofBool p (f.toBool varStore)).eval varStore = f.eval varStore
:= by
  aesop (add simp [toBool,FB.ofBool,FB.isValid])

@[simp, grind =]
lemma toBool_ofBool
  {p : ℕ}
  {varStore : ℕ → Option (ZMod p)}
  (b: Bool)
  [Fact (p ≥ 2)]
:
  (FB.ofBool p b).toBool varStore = b
:= by
  aesop (add simp [toBool,FB.ofBool,FB.true,FB.false])

namespace ofBool

lemma isAlwaysValid (b:Bool) : isAlwaysValid (FB.ofBool p b) := by
  unfold FB.isAlwaysValid isValid FB.ofBool
  aesop

lemma equiv (varStore) (b) : FixedExp.eval varStore (ofBool p b) =
  if b then .some 1 else .some 0
:= by
  simp [ofBool]
  cases b
  all_goals simp [FB.false, FB.true]

end ofBool

instance : IsValid p (FB p) := ⟨fun Γ a ↦ FB.isValid a Γ⟩

omit [Fact (p ≥ 2)] in
lemma isValid_iff {varStore} {x} :
  IsValid.isValid (α := FB p) varStore x ↔
  x.eval varStore = .some 0 ∨
  x.eval varStore = .some 1 := by rfl

instance {p} : VarStoreSize p (FB p) where
  size := 1
  toLinear varStore x := #v[x.eval varStore |>.getD 42]

instance : Convert p (FB p) Bool where
  toIdeal Γ x := .some (FB.toBool x Γ)
  toRepresents := FB.ofBool p
  someOfIsValid := by simp
  toIdealtoRepresents := by simp
  toRepresentstoIdeal := by simp

/-
TODO Provisional simp
-/
attribute [simp, grind =] Convert.toIdealtoRepresents Convert.toRepresentstoIdeal 

lemma toIdeal_def {varStore} {x} :
  Convert.toIdeal (representsT := FB p) (idealT := Bool) varStore x =
  .some (FB.toBool x varStore) := rfl

lemma toRepresents_def {x} :
  Convert.toRepresents p (representsT := FB p) (idealT := Bool) x =
  FB.ofBool p x := rfl

end FB

end Clap.Edsl.Lang
