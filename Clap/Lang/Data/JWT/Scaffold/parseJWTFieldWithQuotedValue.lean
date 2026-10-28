import Clap.RandomOracle.HashFn
import Clap.Lang.Core.F.mkF
import Clap.Lang.Core.F.mkAdd
import Clap.Lang.Core.F.mkSub
import Clap.Lang.Core.F.mkMul
import Clap.Lang.Core.F.lessThan
import Clap.Lang.Core.F.conditionalSwap
import Clap.Lang.Core.FB.eq
import Clap.Lang.Core.FB.not
import Clap.Lang.Core.FB.or
import Clap.Lang.Data.F8.isWhitespace
import Clap.Lang.Gate.isZero
import Clap.Lang.Core.Combinators.scanlM
import Clap.Lang.Core.Combinators.mapM
import Clap.Lang.Core.Combinators.foldlM
import Clap.Model.Convert.PaddedVector
import Clap.Lang.Core.FUnit.guardedEq0
import Clap.Util.Primes
import Clap.Lang.Data.HashToField.hashBytesToField
import Clap.Lang.Data.FString.isSubstring
import Clap.Lang.Data.FArray.selectArrayValue
import Clap.Lang.Data.FArray.arraySelectorComplex
import Clap.Lang.Data.FArray.arraySelector
import Clap.Lang.Core.FUnit.guardedAssertEq
import Clap.Lang.Data.JWT.parseJWTFieldSharedLogic
import Clap.Lang.Data.JWT.Basic
import Mathlib.Data.List.GetD

namespace Clap.Lang

open Primes

/-- `Vector.zipWithM` plumbing — same situation and fix as the other two JWT files' copies of this
section (`Clap/Lang/Poseidon/Poseidon.lean` sits above `Lang/Core/Combinators/` in the import
order, so a lemma about it can't live there without a layering violation). The dependencies
(`Vector.zipWithM_zero`/`_succ`, `FArray.converts_cons`) stay `private`, used only inside this
lemma's own proof. `convertsM_zipWithM_or` itself is suffixed `_quoted`: `parseEmailVerifiedField`'s
own Scaffold file already exposes a non-private lemma under the unsuffixed name, and since
`Clap/Lang/All.lean` transitively imports every gadget file, a second non-private declaration under
that same name would collide the moment both Scaffold files load together. -/

private lemma Vector.zipWithM_zero {m} [Monad m] [LawfulMonad m] {α β φ : Type}
    (f : α → β → m φ) :
  Vector.zipWithM f (#v[] : Vector α 0) (#v[] : Vector β 0) = pure #v[]
:= by
  unfold Vector.zipWithM
  simp

private lemma Vector.zipWithM_succ {m} [Monad m] {n} {α β φ : Type}
    (f : α → β → m φ) (a : α) (b : β) (xs : Vector α n) (ys : Vector β n) :
  Vector.zipWithM f (⟨⟨a :: xs.toList⟩, by simp⟩ : Vector α (n+1))
                    (⟨⟨b :: ys.toList⟩, by simp⟩ : Vector β (n+1))
  = (do
      let z ← f a b
      let zs ← xs.zipWithM f ys
      pure (⟨⟨z :: zs.toList⟩, by simp⟩ : Vector φ (n+1)))
:= by
  conv_lhs => unfold Vector.zipWithM
  simp [Vector.head, List.take_of_length_le Vector.length_toList.le, Vector.toArray_toList]

private lemma FArray.converts_cons
  {p : ℕ} {k} {state : ClapMState p}
  {expr : FB p} {val : Bool}
  {exprs : FArray p k} {vals : Vector Bool k}
  (h_expr : Converts FB.conversion state expr val)
  (h_exprs : Converts FArray.conversion state exprs vals)
:
  Converts FArray.conversion state (⟨⟨expr :: exprs.toList⟩, by simp⟩ : Vector (FB p) (k + 1))
    (⟨⟨val :: vals.toList⟩, by simp⟩ : Vector Bool (k + 1))
:= by
  rewrite [FArray.converts_iff_FB_converts] at h_exprs ⊢
  intro ⟨i, h_i⟩
  match i, h_i with
  | 0, h_i => simpa using h_expr
  | i + 1, h_i =>
    have h := h_exprs ⟨i, by omega⟩
    simpa using h

/-- `Vector.zipWithM FB.or`: a `True`-constraint, pointwise-OR combinator. -/
lemma convertsM_zipWithM_or_quoted
  {p : ℕ} [p.AtLeastTwo]
  {k} {state : ClapMState p}
  {xs ys : Vector (FB p) k} {xvals yvals : Vector Bool k}
  (h_x : ∀ i : Fin k, Converts FB.conversion state xs[i] xvals[i])
  (h_y : ∀ i : Fin k, Converts FB.conversion state ys[i] yvals[i])
:
  ConvertsM FArray.conversion (xs.zipWithM FB.or ys) state
    (Vector.ofFn (fun i : Fin k => xvals[i] || yvals[i])) True
:= by
  induction k generalizing state with
  | zero =>
    have hxs : xs = #v[] := by grind
    have hys : ys = #v[] := by grind
    subst hxs hys
    rw [Vector.zipWithM_zero]
    apply convertsM_pure
    . have h_eq : (Vector.ofFn (fun i : Fin 0 => xvals[i] || yvals[i]) : Vector Bool 0) = #v[] := by
        ext i hi; omega
      rw [h_eq]
      exact FArray.converts_empty
    . trivial
  | succ k ih =>
    have h_head_x : Converts FB.conversion state xs[0] xvals[0] := h_x ⟨0, by omega⟩
    have h_head_y : Converts FB.conversion state ys[0] yvals[0] := h_y ⟨0, by omega⟩
    have h_tail_x : ∀ i : Fin k, Converts FB.conversion state
        (xs.tail.cast (by omega) : Vector (FB p) k)[i] (xvals.tail.cast (by omega) : Vector Bool k)[i] := by
      intro ⟨i, h_i⟩
      have h1 : (xs.tail.cast (by omega) : Vector (FB p) k)[i]'(by omega)
          = xs[i+1]'(by omega) := by simp [Nat.add_comm]
      have h2 : (xvals.tail.cast (by omega) : Vector Bool k)[i]'(by omega)
          = xvals[i+1]'(by omega) := by simp [Nat.add_comm]
      simp only [Fin.getElem_fin]
      rw [h1, h2]
      exact h_x ⟨i+1, by omega⟩
    have h_tail_y : ∀ i : Fin k, Converts FB.conversion state
        (ys.tail.cast (by omega) : Vector (FB p) k)[i] (yvals.tail.cast (by omega) : Vector Bool k)[i] := by
      intro ⟨i, h_i⟩
      have h1 : (ys.tail.cast (by omega) : Vector (FB p) k)[i]'(by omega)
          = ys[i+1]'(by omega) := by simp [Nat.add_comm]
      have h2 : (yvals.tail.cast (by omega) : Vector Bool k)[i]'(by omega)
          = yvals[i+1]'(by omega) := by simp [Nat.add_comm]
      simp only [Fin.getElem_fin]
      rw [h1, h2]
      exact h_y ⟨i+1, by omega⟩
    rw [Vector.eq_cons xs, Vector.eq_cons ys, Vector.zipWithM_succ]
    have h_action := FB.or.convertsM h_head_x h_head_y
    have h_tail_x' := fun i ↦ converts_skip h_action (h_tail_x i)
    have h_tail_y' := fun i ↦ converts_skip h_action (h_tail_y i)
    step h_action as z
    step (ih h_tail_x' h_tail_y') as zs
    apply convertsM_pure
    . have h_cons := FArray.converts_cons h_z h_zs
      have h_vals : Vector.ofFn (fun i : Fin (k+1) => xvals[i] || yvals[i])
          = (⟨⟨(xvals[0] || yvals[0]) :: (Vector.ofFn (fun i : Fin k =>
              (xvals.tail.cast (by omega) : Vector Bool k)[i] ||
              (yvals.tail.cast (by omega) : Vector Bool k)[i])).toList⟩, by simp⟩
             : Vector Bool (k+1)) := by
        ext i hi
        rcases i with _ | i
        · simp
        · simp [Nat.add_comm]
      rw [h_vals]
      simpa using h_cons
    . trivial

/-- `F8.isWhitespace`'s *unchecked* raw value equals the plain-`ℕ` `isWs` predicate, given the byte
is known `< 2^8`. Suffixed `_quoted` for the same reason as `convertsM_zipWithM_or_quoted` above:
`parseEmailVerifiedField`'s Scaffold file already exposes a non-private lemma under the unsuffixed
name. -/
lemma lessThanRaw_isWs_eq_quoted {c_val : ZMod bn254} (h_c8 : c_val.val < 2 ^ 8) :
    ((lessThan.lessThanRaw 8 8 c_val && lessThan.lessThanRaw 8 c_val 14) || c_val == 32)
      = isWs c_val.val := by
  have hw9 : (2:ℕ) ^ (8 + 1) < bn254 := by decide
  have h8v : (8 : ZMod bn254).val = 8 := by decide
  have h14v : (14 : ZMod bn254).val = 14 := by decide
  have h8lt : (8 : ZMod bn254).val < 2 ^ 8 := by decide
  have h14lt : (14 : ZMod bn254).val < 2 ^ 8 := by decide
  have h32eq : (c_val == (32 : ZMod bn254)) = decide (c_val.val = 32) := by
    have h32v : (32 : ZMod bn254).val = 32 := by decide
    by_cases h : c_val.val = 32
    · have hc : c_val = 32 := ZMod.val_injective bn254 (by rw [h32v]; exact h)
      simp [hc, h32v]
    · have hne : c_val ≠ 32 := fun hc => h (by rw [hc, h32v])
      simp [hne, h]
  rw [lessThan.lessThanRaw_eq h8lt h_c8 hw9, lessThan.lessThanRaw_eq h_c8 h14lt hw9, h32eq, h8v, h14v]
  simp [isWs]

/-- A pairing conversion for two bit-valued (`FB`) positions, mirroring `FPair.conversion`
(`Clap/Model/Convert/Specialised.lean`) which only pairs `F`-valued (`ZMod`) positions. Needed by
`checkStringBodies.convertsM` (`parseJWTFieldWithQuotedValue.lean`), which zips two bit vectors
(a name/value selector and `fieldStringBodies`) and feeds each pair into the generic
`convertsM_foldlM_ctx_constraints` combinator — that combinator needs a single `Conversion` for
the element type it folds over, and `FPair.conversion`'s `ZMod`-valued `IdealT` doesn't typecheck
for a pair of bits. -/
abbrev FBPair.conversion : Conversion bn254 (FB bn254 × FB bn254) where
  IdealT := Bool × Bool
  toExprs xy := [xy.1, xy.2]
  conversion xy := [if xy.1 then 1 else 0, if xy.2 then 1 else 0]

lemma FBPair.converts_intro
  {state : ClapMState bn254} {x y : FB bn254} {xv yv : Bool}
  (h_x : Converts FB.conversion state x xv)
  (h_y : Converts FB.conversion state y yv)
:
  Converts FBPair.conversion state (x, y) (xv, yv)
:= by
  obtain ⟨_, x_varSet, x_wf, x_val⟩ := h_x
  obtain ⟨_, y_varSet, y_wf, y_val⟩ := h_y
  simp at x_varSet x_wf x_val y_varSet y_wf y_val
  refine ⟨by simp, ?_, ?_, ?_⟩ <;>
  · intro ⟨ib, h_ib⟩
    simp [FBPair.conversion] at h_ib ⊢
    interval_cases ib <;> simp [*]

lemma FBPair.converts_fst
  {state : ClapMState bn254} {xy : FB bn254 × FB bn254} {xy_val : Bool × Bool}
  (h : Converts FBPair.conversion state xy xy_val)
:
  Converts FB.conversion state xy.1 xy_val.1
:= by
  have v0 := h.varSet_wf ⟨0, by simp⟩
  have w0 := h.expr_wf ⟨0, by simp⟩
  have a0 := h.value_eq ⟨0, by simp⟩
  simp [FBPair.conversion] at v0 w0 a0
  exact ⟨by simp, fun _ ↦ by simpa using v0, fun _ ↦ by simpa using w0,
         fun _ ↦ by simpa using a0⟩

lemma FBPair.converts_snd
  {state : ClapMState bn254} {xy : FB bn254 × FB bn254} {xy_val : Bool × Bool}
  (h : Converts FBPair.conversion state xy xy_val)
:
  Converts FB.conversion state xy.2 xy_val.2
:= by
  have v1 := h.varSet_wf ⟨1, by simp⟩
  have w1 := h.expr_wf ⟨1, by simp⟩
  have a1 := h.value_eq ⟨1, by simp⟩
  simp [FBPair.conversion] at v1 w1 a1
  exact ⟨by simp, fun _ ↦ by simpa using v1, fun _ ↦ by simpa using w1,
         fun _ ↦ by simpa using a1⟩

lemma FBPair.converts_zip
  {k : ℕ} {i : ℕ} {state : ClapMState bn254} {a b : FArray bn254 k} {a_vals b_vals : Vector Bool k}
  (h_a : Converts FArray.conversion state a a_vals)
  (h_b : Converts FArray.conversion state b b_vals)
  (h_i : i < k)
:
  Converts FBPair.conversion state (a.zip b)[i] ((a_vals.zip b_vals)[i])
:= by
  have h := FBPair.converts_intro
    (FArray.converts_iff_FB_converts.mp h_a ⟨i, h_i⟩)
    (FArray.converts_iff_FB_converts.mp h_b ⟨i, h_i⟩)
  simpa [Vector.getElem_zip] using h

/-- `guardedEq0 perform (← a.and (← not b))`: when `perform`, asserts `a = true → b = true`. -/
lemma guardedAndNotEq0_convertsM
  {state : ClapMState bn254} {perform a b : F bn254}
  {perform_val : Bool} {a_val : ZMod bn254} {b_val : Bool}
  (h_perform : Converts FB.conversion state perform perform_val)
  (h_a : Converts F.conversion state a a_val)
  (h_b : Converts FB.conversion state b b_val)
:
  ConvertsM FUnit.conversion
    (not b >>= fun nb => FB.and a nb >>= fun prod => guardedEq0 perform prod)
    state ()
    (perform_val = true → a_val * (if b_val then (0:ZMod bn254) else 1) = 0)
:= by
  step not.convertsM h_b as nb
  unfold FB.and
  rw [mul_def]
  refine convertsM_bind (mkMul.convertsM h_a (F.converts_of_FB_converts h_nb)) ?_ (fun _ => trivial)
  have hMul := mkMul.convertsM h_a (F.converts_of_FB_converts h_nb)
  replace h_perform := converts_skip hMul h_perform
  apply convertsM_of_convertsM (guardedEq0.convertsM h_perform hMul.result) rfl
    (by cases b_val <;> simp)

/-- `guardedEq0 perform (← (← not a).and b)`: when `perform`, asserts `b = true → a = true`. -/
lemma guardedNotAndEq0_convertsM
  {state : ClapMState bn254} {perform b : F bn254} {a : FB bn254}
  {perform_val : Bool} {b_val : ZMod bn254} {a_val : Bool}
  (h_perform : Converts FB.conversion state perform perform_val)
  (h_a : Converts FB.conversion state a a_val)
  (h_b : Converts F.conversion state b b_val)
:
  ConvertsM FUnit.conversion
    (not a >>= fun na => FB.and na b >>= fun prod => guardedEq0 perform prod)
    state ()
    (perform_val = true → (if a_val then (0:ZMod bn254) else 1) * b_val = 0)
:= by
  step not.convertsM h_a as na
  unfold FB.and
  rw [mul_def]
  refine convertsM_bind (mkMul.convertsM (F.converts_of_FB_converts h_na) h_b) ?_ (fun _ => trivial)
  have hMul := mkMul.convertsM (F.converts_of_FB_converts h_na) h_b
  replace h_perform := converts_skip hMul h_perform
  apply convertsM_of_convertsM (guardedEq0.convertsM h_perform hMul.result) rfl
    (by cases a_val <;> simp)

-- The per-position step: `nv = true ↔ sb = true`, asserted as two guarded implications.
lemma guardedStringBodyCheck_convertsM
  {state : ClapMState bn254} {perform nv sb : F bn254} {perform_val : Bool} {nv_val sb_val : Bool}
  (h_perform : Converts FB.conversion state perform perform_val)
  (h_nv : Converts FB.conversion state nv nv_val)
  (h_sb : Converts FB.conversion state sb sb_val)
:
  ConvertsM FUnit.conversion
    (not sb >>= fun x1 => FB.and nv x1 >>= fun y1 => guardedEq0 perform y1 >>= fun _ =>
      not nv >>= fun x2 => FB.and x2 sb >>= fun y2 => guardedEq0 perform y2)
    state ()
    ( (perform_val = true → nv_val = true → sb_val = true) ∧
      (perform_val = true → sb_val = true → nv_val = true) )
:= by
  have h1 := guardedAndNotEq0_convertsM h_perform (F.converts_of_FB_converts h_nv) h_sb
  -- Abstract `h1`'s action before reframing through it, for the same reason as
  -- `parseJWTFieldWithQuotedValue.lean`'s `checkValueQuotes.convertsM`'s `hAct1` — see its comment.
  generalize hAct1 : (not sb >>= fun nb => FB.and nv nb >>= fun prod => guardedEq0 perform prod) = act1
    at h1
  have h_perform' := converts_skip h1 h_perform
  have h_nv' := converts_skip h1 h_nv
  have h_sb' := converts_skip h1 h_sb
  have h2 := guardedNotAndEq0_convertsM h_perform' h_nv' (F.converts_of_FB_converts h_sb')
  have hcomb := parseJWTFieldSharedLogic.seqUnit_convertsM h1 h2
  rw [← hAct1] at hcomb
  simp only [bind_assoc] at hcomb
  apply convertsM_of_convertsM hcomb rfl
  constructor
  · rintro ⟨h1', h2'⟩
    refine ⟨fun hp hnv => ?_, fun hp hsb => ?_⟩
    · by_contra hsb
      simp [hnv, hsb] at h1'
      simp [hp] at h1'
    · by_contra hnv
      simp [hsb, hnv] at h2'
      simp [hp] at h2'
  · rintro ⟨hfwd, hbwd⟩
    constructor
    · intro hp
      by_cases hnv : nv_val = true
      · simp [hnv, hfwd hp hnv]
      · simp [hnv]
    · intro hp
      by_cases hsb : sb_val = true
      · simp [hsb, hbwd hp hsb]
      · simp [hsb]

end Clap.Lang
