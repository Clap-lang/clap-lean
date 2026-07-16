import Clap.Lang.F.F
import Clap.eDSLState.Spec

namespace Clap.Edsl.Lang

abbrev FB p := F p

namespace FB

def true (p : ℕ) [p.AtLeastTwo] : FB p := .c 1
def false (p : ℕ) [p.AtLeastTwo] : FB p := .c 0

@[grind =]
lemma eval_true {p : ℕ} {varStore : VarStore p} [p.AtLeastTwo]:
  [varStore|true p] = .some 1
:= by
  simp [FB.true]

@[grind =]
lemma eval_false {p : ℕ} {varStore : VarStore p} [p.AtLeastTwo]:
  [varStore|false p] = .some 0
:= by
  simp [FB.false]

@[simp, grind =]
lemma eval_true_isSome {p : ℕ} {varStore : VarStore p} [p.AtLeastTwo]:
  [varStore|true p].isSome = Bool.true
:= by
  grind

@[simp, grind =]
lemma eval_false_isSome {p : ℕ} {varStore : VarStore p} [p.AtLeastTwo]:
  [varStore|false p].isSome = Bool.true
:= by
  grind

variable {p : ℕ} [p.AtLeastTwo]

def isValid (x : FB p) (varStore : VarStore p) : Prop :=
  x.eval varStore = .some 0 ∨
  x.eval varStore = .some 1

-- TODO there must be a better way of putting this
-- Well, this is just `isValid_iff` with an extra step.
-- I think this is good, and it `simp`s down to `true | false` via `eval_<t|f>`.
@[grind .]
lemma isValid_iff_eval_eq_eval_false_or_eval_true
  {x : FB p} {varStore : VarStore p}
:
  x.isValid varStore ↔ (
    [varStore|x] = [varStore|(false p)] ∨
    [varStore|x] = [varStore|(true p)]
  )
:= by
  simp [isValid, eval_true, eval_false]

def isAlwaysValid (x : FB p) : Prop :=
  ∀ varStore, x.isValid varStore

def toBool (x : FB p) (varStore : VarStore p) : Option Bool :=
  [varStore|x].bind (λ x => if x == 1 then Bool.true else if x == 0 then Bool.false else .none)

@[grind .]
lemma toBool_isSome_eq_true_of_isValid
  {x : FB p} {varStore : VarStore p}
  (h_isValid : x.isValid varStore)
:
  (x.toBool varStore).isSome = Bool.true
:= by
  grind [toBool]

omit [p.AtLeastTwo] in
@[grind .]
lemma toBool_isSome_eq_false_of_isValid
  {x : FB p} {varStore : VarStore p}
  (h_isValid : ¬x.isValid varStore)
:
  (x.toBool varStore).isSome = Bool.false
:= by
  simp [isValid] at h_isValid
  unfold toBool
  set y := [varStore|x]
  obtain _ | ⟨y⟩ := y <;> grind

def ofBool (p : ℕ) [p.AtLeastTwo] (x : Bool) : FB p :=
  if x then FB.true p else FB.false p

@[simp, grind =]
lemma eval_ofBool {p : ℕ} {varStore : VarStore p} [p.AtLeastTwo] {b : Bool} :
  [varStore|ofBool p b] = if b then [varStore|true p] else [varStore|false p]
:= by
  grind [FB.ofBool]

@[simp, grind =]
lemma toBool_ofBool
  {p : ℕ}
  {varStore : VarStore p}
  (b: Bool)
  [p.AtLeastTwo]
:
  (FB.ofBool p b).toBool varStore = b
:= by
  aesop (add simp [toBool,FB.ofBool,FB.true,FB.false])

@[simp, grind =]
lemma toBool_false
  {varStore : VarStore p}
:
  (false p).toBool varStore = Bool.false
:= by
  simp [FB.false, FB.toBool]

@[grind .]
lemma toBool_of_eval_eq_eval_false
  {varStore : VarStore p}
  {x : FB p}
  (h : [varStore|x] = [varStore|false p])
:
  x.toBool varStore = .some Bool.false
:= by
  grind [FB.toBool, false]

@[grind .]
lemma toBool_of_eval_eq_eval_true
  {varStore : VarStore p}
  {x : FB p}
  (h : [varStore|x] = [varStore|true p])
:
  x.toBool varStore = .some Bool.true
:= by
  grind [FB.toBool, true]

@[simp, grind =]
lemma toBool_true
  {varStore : VarStore p}
:
  (true p).toBool varStore = Bool.true
:= by
  simp [FB.true, FB.toBool]

@[simp, grind .] -- TODO(provisional `simp`)
lemma eval_ofBool_toBool_of_isValid
  {p : ℕ}
  {varStore : VarStore p}
  {x: FB p}
  (h : x.isValid varStore)
  [p.AtLeastTwo]
:
  [varStore|(FB.ofBool p ((x.toBool varStore).get (by grind)))] = [varStore|x]
:= by
  grind

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

omit [p.AtLeastTwo] in
lemma isValid_iff {varStore} {x} :
  IsValid.isValid (α := FB p) varStore x ↔
  x.eval varStore = .some 0 ∨
  x.eval varStore = .some 1 := by rfl

instance {p} : VarStoreSize p (FB p) where
  size := 1
  toLinear varStore x := #v[x.eval varStore |>.getD 42]

instance : Convert p (FB p) Bool where
  toIdeal Γ x := FB.toBool x Γ
  toRepresents := FB.ofBool p
  isValid_iff_isSome_toIdeal Γ x := by unfold_projs; grind [IsValid.isValid]
  toIdeal_toRepresents := by simp
  toRepresents_toIdeal := by simp

/-
TODO Provisional simp
-/
attribute [simp, grind =] Convert.toIdeal_toRepresents Convert.toRepresents_toIdeal

lemma toIdeal_def {varStore} {x} :
  Convert.toIdeal (representsT := FB p) (idealT := Bool) varStore x =
  (FB.toBool x varStore) := rfl

lemma toRepresents_def {x} :
  Convert.toRepresents p (representsT := FB p) (idealT := Bool) x =
  FB.ofBool p x := rfl

-- TODO rename
@[grind .]
lemma isValid_iff_oddly_specific
  {x : FB p} {varStore : VarStore p}
:
  x.isValid varStore ↔ (
    ∃ b,
    [varStore|x] = [varStore|FB.ofBool p b]
  )
:= by
  simp [isValid, eval_true, eval_false]

-- This is breaking the instance abstraction layer
-- and secretly proving something only about the specific
-- Convert FB p Bool instance isn't it?
-- Seems bad
@[grind .]
lemma toIdeal_isSome_of_eval_eq_true
  {varStore : VarStore p}
  {a : FB p}
  (h : [varStore|a] = [varStore|true p])
:
  (Convert.toIdeal (idealT := Bool) varStore a).isSome = Bool.true
:= by
  have := Convert.isValid_iff_isSome_toIdeal varStore a (idealT := Bool)
  rw [this.mp]
  have := isValid_iff_oddly_specific (x := a) (varStore := varStore)
  unfold_projs
  grind

@[grind .]
lemma toIdeal_isSome_of_eval_eq_false
  {varStore : VarStore p}
  {a : FB p}
  (h : [varStore|a] = [varStore|false p])
:
  (Convert.toIdeal (idealT := Bool) varStore a).isSome = Bool.true
:= by
  have := Convert.isValid_iff_isSome_toIdeal varStore a (idealT := Bool)
  rw [this.mp]
  have := isValid_iff_oddly_specific (x := a) (varStore := varStore)
  unfold_projs
  grind

@[grind =]
lemma toIdeal_true_iff_eval_eq_true
  {varStore : VarStore p}
  {a : FB p}
:
  ([varStore|a] = [varStore|true p]) ↔
  ((Convert.toIdeal varStore a) = .some Bool.true)
:= by
  unfold_projs
  simp [toBool]
  obtain _ | x := [varStore|a]
  <;> grind

@[grind =]
lemma toIdeal_false_of_eval_eq_false
  {varStore : VarStore p}
  {a : FB p}
:
  ([varStore|a] = [varStore|false p]) ↔
  ((Convert.toIdeal varStore a) = .some Bool.false)
:= by
  unfold_projs
  simp [toBool]
  obtain _ | x := [varStore|a]
  <;> grind

end FB

end Clap.Edsl.Lang
