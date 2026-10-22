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

/-- JWT field with an unquoted value (iat). -/
structure UnquotedFieldInput (maxPairLen maxNameLen maxValueLen : ℕ) where
  field      : FString bn254 maxPairLen
  name       : FString bn254 maxNameLen
  value      : FString bn254 maxValueLen
  nameIndex  : F bn254
  colonIndex : F bn254
  valueIndex : F bn254

/-! ## Generic logic helpers

A fixed guard (`perform`) commutes with a position-indexed `∀`: the guard does not depend on the
index, so "for every position, if guarded then P" is the same as "if guarded then for every
position, P". Used to pull `perform_val = true →` outside the `∀ i` produced by the `foldlM`
combinators below. -/

private lemma forall_guard_comm {ι : Type} {g : Prop} {B : ι → Prop} :
    (∀ i, g → B i) ↔ (g → ∀ i, B i) :=
  ⟨fun h hg i => h i hg, fun h i hg => h hg i⟩

private lemma forall_and_guard_comm {ι : Type} {A : ι → Prop} {g : Prop} {B : ι → Prop} :
    (∀ i, A i ∧ (g → B i)) ↔ (∀ i, A i) ∧ (g → ∀ i, B i) :=
  ⟨fun h => ⟨fun i => (h i).1, fun hg i => (h i).2 hg⟩,
   fun h i => ⟨h.1 i, fun hg => h.2 hg i⟩⟩

/-! ## `Vector.zipWithM`: a combinator lemma with nowhere layering-safe to live

Same situation, and the same fix, as `parseEmailVerifiedField.lean`'s own copy of this section:
`Vector.zipWithM` (`Clap/Lang/Poseidon/Poseidon.lean`) is generic, model-agnostic `Vector`
plumbing that happens to live in a Poseidon file. `Lang/Core/Combinators/` sits *below*
`Lang/Poseidon` in the import order, so a lemma about it cannot live there without a layering
violation; `Lang/Data/JWT` sits above `Lang/Poseidon`, so each JWT file that needs it keeps its own
private copy (per `parseEmailVerifiedField.lean`'s own doc comment, which names this file as its
second intended user). -/

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

/-- `Vector.zipWithM FB.or`: a `True`-constraint, pointwise-OR combinator. Covers both zone
merges in `checkWhitespaceZones` below. -/
private lemma convertsM_zipWithM_or
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

/-- `convertsM_foldlM_constraints` (`Clap/Lang/Core/Combinators/foldlM.lean`) for a step that also
reads a fixed context `ctx` — here, the guard `perform`, allocated once before each loop in this
file and threaded through every iteration's guarded assertion. No existing combinator covers both
context-threading (`convertsM_foldlM_ctx`) and a real per-step constraint
(`convertsM_foldlM_constraints`) at once; this merges the two inductions. -/
private lemma convertsM_foldlM_ctx_constraints
  {p : ℕ} {k} {α γ δ}
  {C_ctx : Conversion p δ}
  {C_acc : Conversion p α}
  {C_elem : Conversion p γ}
  {f : δ → α → γ → ClapM p α}
  {f_spec : C_ctx.IdealT → C_acc.IdealT → C_elem.IdealT → C_acc.IdealT}
  {step_constraints : C_ctx.IdealT → C_elem.IdealT → Prop}
  {state : ClapMState p}
  {ctx : δ}
  {ctx_val : C_ctx.IdealT}
  {v : Vector γ k}
  {vals : Vector C_elem.IdealT k}
  {init : α}
  {init_val : C_acc.IdealT}
  (h_ctx : Converts C_ctx state ctx ctx_val)
  (h_v : ∀ i : Fin k, Converts C_elem state v[i] vals[i])
  (h_init : Converts C_acc state init init_val)
  (h_f : ∀ {state' : ClapMState p} {acc acc_val x x_val},
          Converts C_ctx state' ctx ctx_val →
          Converts C_acc state' acc acc_val →
          Converts C_elem state' x x_val →
          ConvertsM C_acc (f ctx acc x) state' (f_spec ctx_val acc_val x_val)
            (step_constraints ctx_val x_val))
:
  ConvertsM C_acc (v.foldlM (f ctx) init) state (vals.foldl (f_spec ctx_val) init_val)
    (∀ i : Fin k, step_constraints ctx_val vals[i])
:= by
  induction' k with k h_k
  . have h_empty : Vector.foldlM (m := ClapM p) (f ctx) init v = pure init := by
      convert Vector.foldlM_empty
      obtain ⟨⟨_⟩, _⟩ := v
      grind
    simp [h_empty]
    apply convertsM_pure
    . have : vals = #v[] := by grind
      simp [this]
      assumption
    . trivial
  . set v_base := Vector.cast (m := k) (by trivial) v.pop with h_v_base_def
    set vals_base := Vector.cast (m := k) (by trivial) vals.pop with h_vals_base_def

    have h_eq : ∀ (j : ℕ) (hj : j < k), vals_base[j]'hj = vals[j]'(by omega) := by
      intro j hj
      simp [vals_base]

    have h_v_base : ∀ i : Fin k, Converts C_elem state v_base[i] vals_base[i] := by
      intro ⟨i, h_i⟩
      have h1 : v_base[i]'h_i = v[i]'(by omega) := by simp [v_base]
      simp only [Fin.getElem_fin]
      rw [h1, h_eq i h_i]
      exact h_v ⟨i, by omega⟩

    have h_vals : vals = vals_base.push vals[k] := by
      ext
      rewrite [Vector.getElem_push]
      split
      . simp [vals_base]
      . grind

    have h_push : v = v_base.push v[k] := by
      ext
      rewrite [Vector.getElem_push]
      split
      . simp [v_base]
      . grind

    have h_last := h_v ⟨k, Nat.lt_succ_self k⟩
    have h_ih := h_k h_v_base

    rewrite [h_push]
    simp only [Vector.foldlM_push]

    apply convertsM_of_convertsM
      (convertsM_bind_and h_ih
        (h_f (converts_skip h_ih h_ctx) h_ih.result (converts_skip h_ih h_last)))
    . conv_rhs => rewrite [h_vals]
      simp
    . constructor
      . rintro ⟨h_prefix, h_elem⟩ ⟨i, h_i⟩
        by_cases h : i = k
        . subst h
          exact h_elem
        . have h_lt : i < k := by grind
          have h1 := h_prefix ⟨i, h_lt⟩
          simp only [Fin.getElem_fin] at h1
          rwa [h_eq i h_lt] at h1
      . intro h
        refine ⟨fun ⟨i, h_i⟩ ↦ ?_, h ⟨k, Nat.lt_succ_self k⟩⟩
        have h1 := h ⟨i, by grind⟩
        simp only [Fin.getElem_fin] at h1 ⊢
        rwa [← h_eq i h_i] at h1

/-! ## Zone construction

Three "gap" zones must be whitespace: between the name's closing quote and the colon, between the
colon and the (unquoted) value, and between the value and the terminator. Unlike
`parseEmailVerifiedField.lean`'s quoted sibling, there is no opening/closing quote around the
value to skip past, so zone B ends at `valueIndex` directly (not `valueIndex - 1`) and zone C
starts at `valueIndex + valueLen` directly (not `+ 1`). -/

private def zoneADef (maxKVPairLen : ℕ) (nameLen two colonIndex : F bn254) :
    ClapM bn254 (FArray bn254 maxKVPairLen) := do
  let s ← mkAdd nameLen two
  arraySelectorComplex maxKVPairLen s colonIndex

private def zoneBDef (maxKVPairLen : ℕ) (one colonIndex valueIndex : F bn254) :
    ClapM bn254 (FArray bn254 maxKVPairLen) := do
  let s ← mkAdd colonIndex one
  arraySelectorComplex maxKVPairLen s valueIndex

private def zoneCDef (maxKVPairLen : ℕ) (one valueIndex valueLen fieldLen : F bn254) :
    ClapM bn254 (FArray bn254 maxKVPairLen) := do
  let s ← mkAdd valueIndex valueLen
  let e ← mkSub fieldLen one
  arraySelectorComplex maxKVPairLen s e

private def inZoneDef (maxKVPairLen : ℕ) (nameLen colonIndex valueIndex valueLen fieldLen : F bn254) :
    ClapM bn254 (FArray bn254 maxKVPairLen) := do
  let one ← mkF 1
  let two ← mkF 2
  let zoneA ← zoneADef maxKVPairLen nameLen two colonIndex
  let zoneB ← zoneBDef maxKVPairLen one colonIndex valueIndex
  let zoneC ← zoneCDef maxKVPairLen one valueIndex valueLen fieldLen
  let inZoneAB ← zoneA.zipWithM FB.or zoneB
  inZoneAB.zipWithM FB.or zoneC

private lemma zoneA_convertsM
  {maxKVPairLen : ℕ} {state : ClapMState bn254}
  {nameLen two colonIndex : F bn254} {name_len colon_index_val : ZMod bn254}
  (h_nl : Converts F.conversion state nameLen name_len)
  (h_two : Converts F.conversion state two (2 : ZMod bn254))
  (h_ci : Converts F.conversion state colonIndex colon_index_val)
  (h_maxKV : maxKVPairLen < bn254)
:
  ConvertsM FArray.conversion
    (zoneADef maxKVPairLen nameLen two colonIndex)
    state
    (Vector.ofFn (fun i : Fin maxKVPairLen =>
      decide (0 < (name_len + 2).val ∧ (name_len + 2).val ≤ i.val) && decide (i.val < colon_index_val.val)))
    (0 < (name_len + 2).val ∧ (name_len + 2).val ≤ maxKVPairLen ∧ colon_index_val.val < maxKVPairLen)
:= by
  unfold zoneADef
  step mkAdd.convertsM h_nl h_two as s
  apply convertsM_of_convertsM (arraySelectorComplex.convertsM h_s h_ci h_maxKV) rfl
  simp only [true_implies]

private lemma zoneB_convertsM
  {maxKVPairLen : ℕ} {state : ClapMState bn254}
  {one colonIndex valueIndex : F bn254} {colon_index_val value_index_val : ZMod bn254}
  (h_one : Converts F.conversion state one (1 : ZMod bn254))
  (h_ci : Converts F.conversion state colonIndex colon_index_val)
  (h_vi : Converts F.conversion state valueIndex value_index_val)
  (h_maxKV : maxKVPairLen < bn254)
:
  ConvertsM FArray.conversion
    (zoneBDef maxKVPairLen one colonIndex valueIndex)
    state
    (Vector.ofFn (fun i : Fin maxKVPairLen =>
      decide (0 < (colon_index_val + 1).val ∧ (colon_index_val + 1).val ≤ i.val) &&
        decide (i.val < value_index_val.val)))
    (0 < (colon_index_val + 1).val ∧ (colon_index_val + 1).val ≤ maxKVPairLen ∧
      value_index_val.val < maxKVPairLen)
:= by
  unfold zoneBDef
  step mkAdd.convertsM h_ci h_one as s
  apply convertsM_of_convertsM (arraySelectorComplex.convertsM h_s h_vi h_maxKV) rfl
  simp only [true_implies]

private lemma zoneC_convertsM
  {maxKVPairLen : ℕ} {state : ClapMState bn254}
  {one valueIndex valueLen fieldLen : F bn254}
  {value_index_val value_len field_len : ZMod bn254}
  (h_one : Converts F.conversion state one (1 : ZMod bn254))
  (h_vi : Converts F.conversion state valueIndex value_index_val)
  (h_vl : Converts F.conversion state valueLen value_len)
  (h_fl : Converts F.conversion state fieldLen field_len)
  (h_maxKV : maxKVPairLen < bn254)
:
  ConvertsM FArray.conversion
    (zoneCDef maxKVPairLen one valueIndex valueLen fieldLen)
    state
    (Vector.ofFn (fun i : Fin maxKVPairLen =>
      decide (0 < (value_index_val + value_len).val ∧ (value_index_val + value_len).val ≤ i.val) &&
        decide (i.val < (field_len - 1).val)))
    (0 < (value_index_val + value_len).val ∧ (value_index_val + value_len).val ≤ maxKVPairLen ∧
      (field_len - 1).val < maxKVPairLen)
:= by
  unfold zoneCDef
  step mkAdd.convertsM h_vi h_vl as s
  step mkSub.convertsM h_fl h_one as e
  apply convertsM_of_convertsM (arraySelectorComplex.convertsM h_s h_e h_maxKV) rfl
  simp only [true_implies]

private lemma zonesTail_convertsM
  {maxKVPairLen : ℕ} {state : ClapMState bn254}
  {zoneA zoneB : FArray bn254 maxKVPairLen}
  {zoneA_val zoneB_val : Vector Bool maxKVPairLen}
  {one valueIndex valueLen fieldLen : F bn254}
  {value_index_val value_len field_len : ZMod bn254}
  (h_zoneA_pw : ∀ i : Fin maxKVPairLen, Converts FB.conversion state zoneA[i] zoneA_val[i])
  (h_zoneB_pw : ∀ i : Fin maxKVPairLen, Converts FB.conversion state zoneB[i] zoneB_val[i])
  (h_one : Converts F.conversion state one (1 : ZMod bn254))
  (h_vi : Converts F.conversion state valueIndex value_index_val)
  (h_vl : Converts F.conversion state valueLen value_len)
  (h_fl : Converts F.conversion state fieldLen field_len)
  (h_maxKV : maxKVPairLen < bn254)
:
  ConvertsM FArray.conversion
    (zoneCDef maxKVPairLen one valueIndex valueLen fieldLen >>= fun zoneC =>
      zoneA.zipWithM FB.or zoneB >>= fun inZoneAB =>
      inZoneAB.zipWithM FB.or zoneC)
    state
    (Vector.ofFn (fun i : Fin maxKVPairLen => zoneA_val[i] || zoneB_val[i] ||
      (decide (0 < (value_index_val + value_len).val ∧
          (value_index_val + value_len).val ≤ i.val) && decide (i.val < (field_len - 1).val))))
    (0 < (value_index_val + value_len).val ∧ (value_index_val + value_len).val ≤ maxKVPairLen ∧
        (field_len - 1).val < maxKVPairLen)
:= by
  have hC := zoneC_convertsM h_one h_vi h_vl h_fl h_maxKV
  replace h_zoneA_pw := fun i ↦ converts_skip hC (h_zoneA_pw i)
  replace h_zoneB_pw := fun i ↦ converts_skip hC (h_zoneB_pw i)
  have h_zoneC_pw := FArray.converts_iff_FB_converts.mp hC.result
  step hC as zoneCR
  step (convertsM_zipWithM_or h_zoneA_pw h_zoneB_pw) as inZoneAB
  replace h_zoneC_pw := fun i ↦ converts_skip (convertsM_zipWithM_or h_zoneA_pw h_zoneB_pw) (h_zoneC_pw i)
  have h_inZoneAB_pw := FArray.converts_iff_FB_converts.mp h_inZoneAB
  apply convertsM_of_convertsM (convertsM_zipWithM_or h_inZoneAB_pw h_zoneC_pw)
  · ext i
    simp [Vector.getElem_ofFn]
  · exact iff_of_true trivial (fun _ h => h)

private lemma zones_convertsM
  {maxKVPairLen : ℕ} {state : ClapMState bn254}
  {nameLen colonIndex valueIndex valueLen fieldLen : F bn254}
  {name_len colon_index_val value_index_val value_len field_len : ZMod bn254}
  (h_nl : Converts F.conversion state nameLen name_len)
  (h_ci : Converts F.conversion state colonIndex colon_index_val)
  (h_vi : Converts F.conversion state valueIndex value_index_val)
  (h_vl : Converts F.conversion state valueLen value_len)
  (h_fl : Converts F.conversion state fieldLen field_len)
  (h_maxKV : maxKVPairLen < bn254)
:
  ConvertsM FArray.conversion
    (inZoneDef maxKVPairLen nameLen colonIndex valueIndex valueLen fieldLen)
    state
    (Vector.ofFn (fun i : Fin maxKVPairLen =>
      (decide (0 < (name_len + 2).val ∧ (name_len + 2).val ≤ i.val) && decide (i.val < colon_index_val.val)) ||
      (decide (0 < (colon_index_val + 1).val ∧ (colon_index_val + 1).val ≤ i.val) &&
        decide (i.val < value_index_val.val)) ||
      (decide (0 < (value_index_val + value_len).val ∧
          (value_index_val + value_len).val ≤ i.val) && decide (i.val < (field_len - 1).val))))
    ( (0 < (name_len + 2).val ∧ (name_len + 2).val ≤ maxKVPairLen ∧ colon_index_val.val < maxKVPairLen) ∧
      (0 < (colon_index_val + 1).val ∧ (colon_index_val + 1).val ≤ maxKVPairLen ∧
        value_index_val.val < maxKVPairLen) ∧
      (0 < (value_index_val + value_len).val ∧ (value_index_val + value_len).val ≤ maxKVPairLen ∧
        (field_len - 1).val < maxKVPairLen) )
:= by
  unfold inZoneDef
  step mkF.convertsM as one
  step mkF.convertsM as two
  simp only [true_implies]
  have hA := zoneA_convertsM h_nl h_two h_ci h_maxKV
  have h_zoneA_pw := FArray.converts_iff_FB_converts.mp hA.result
  replace h_one := converts_skip hA h_one
  replace h_ci := converts_skip hA h_ci
  replace h_vi := converts_skip hA h_vi
  replace h_vl := converts_skip hA h_vl
  replace h_fl := converts_skip hA h_fl
  apply convertsM_bind_and hA
  have hB := zoneB_convertsM h_one h_ci h_vi h_maxKV
  replace h_zoneA_pw := fun i ↦ converts_skip hB (h_zoneA_pw i)
  have h_zoneB_pw := FArray.converts_iff_FB_converts.mp hB.result
  replace h_vi := converts_skip hB h_vi
  replace h_vl := converts_skip hB h_vl
  replace h_fl := converts_skip hB h_fl
  replace h_one := converts_skip hB h_one
  apply convertsM_bind_and hB
  apply convertsM_of_convertsM (zonesTail_convertsM h_zoneA_pw h_zoneB_pw h_one h_vi h_vl h_fl h_maxKV)
  · ext i
    simp [Vector.getElem_ofFn]
  · rfl

/-- `F8.isWhitespace`'s *unchecked* raw value equals the plain-`ℕ` `isWs` predicate, given the byte
is known `< 2^8`. Copied from `parseEmailVerifiedField.lean`'s identical private lemma (per this
file's convention of duplicating small per-file proof infrastructure rather than sharing it across
JWT files). -/
private lemma lessThanRaw_isWs_eq {c_val : ZMod bn254} (h_c8 : c_val.val < 2 ^ 8) :
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

/-- The `foldlM` step: whitespace-or-not for one position, given its zone-membership bit `z` and
field character `c` as *general* field elements (not necessarily typed bits/bytes) — the
combinator's per-element hypothesis has no room to carry a per-index byte-range fact, so this uses
`F8.isWhitespace`'s *unchecked* form and `FB.and`'s underlying `mkMul` directly. Guarded analogue
of `parseEmailVerifiedField.lean`'s `whitespaceCheck_convertsM`: the assertion only fires when
`perform` holds. -/
private lemma guardedWhitespaceCheck_convertsM
  {state : ClapMState bn254} {perform z c : F bn254} {perform_val : Bool} {z_val c_val : ZMod bn254}
  (h_perform : Converts FB.conversion state perform perform_val)
  (h_z : Converts F.conversion state z z_val)
  (h_c : Converts F.conversion state c c_val)
:
  ConvertsM FUnit.conversion
    (F8.isWhitespace c >>= fun ws => not ws >>= fun notws => FB.and z notws >>= fun prod =>
      guardedEq0 perform prod)
    state ()
    ( (lessThan.lessThanOk 8 8 c_val ∧ lessThan.lessThanOk 8 c_val 14) ∧
      (perform_val = true → z_val * (if ((lessThan.lessThanRaw 8 8 c_val && lessThan.lessThanRaw 8 c_val 14) ||
        c_val == 32) then (0:ZMod bn254) else 1) = 0) )
:= by
  have hWs := F8.isWhitespace.convertsM_unchecked h_c
  replace h_z := converts_skip hWs h_z
  replace h_perform := converts_skip hWs h_perform
  apply convertsM_bind_and hWs
  refine convertsM_bind (not.convertsM hWs.result) ?_ (fun _ => trivial)
  have hNot := not.convertsM hWs.result
  replace h_z := converts_skip hNot h_z
  replace h_perform := converts_skip hNot h_perform
  unfold FB.and
  rw [mul_def]
  refine convertsM_bind (mkMul.convertsM h_z (F.converts_of_FB_converts hNot.result)) ?_ (fun _ => trivial)
  have hMul := mkMul.convertsM h_z (F.converts_of_FB_converts hNot.result)
  replace h_perform := converts_skip hMul h_perform
  apply convertsM_of_convertsM (guardedEq0.convertsM h_perform hMul.result)
  · rfl
  · by_cases h : (lessThan.lessThanRaw 8 8 c_val && lessThan.lessThanRaw 8 c_val 14) || c_val == 32 <;>
      simp [h]

/-- Every position in the three "gap" zones (between name/colon, colon/value, value/terminator)
must be whitespace, guarded by `perform` so `skipChecks` can bypass it. -/
private def checkWhitespaceZones {maxKVPairLen : ℕ}
    (field_data : FVec bn254 maxKVPairLen) (perform : FB bn254)
    (nameLen colonIndex valueIndex valueLen fieldLen : F bn254) : ClapM bn254 Unit := do
  let inZone ← inZoneDef maxKVPairLen nameLen colonIndex valueIndex valueLen fieldLen
  (inZone.zip field_data).foldlM (b := ()) fun _ (z, c) ↦ do
    let ws ← F8.isWhitespace c
    guardedEq0 perform (← z.and (← not ws))

lemma checkWhitespaceZones.convertsM
  {maxKVPairLen : ℕ} {state : ClapMState bn254}
  {field_data : FVec bn254 maxKVPairLen} {perform : FB bn254}
  {nameLen colonIndex valueIndex valueLen fieldLen : F bn254}
  {field_vals : Vector (ZMod bn254) maxKVPairLen}
  {perform_val : Bool}
  {name_len colon_index_val value_index_val value_len field_len : ZMod bn254}
  (h_field_val : Converts FVec.conversion state field_data field_vals)
  (h_perform : Converts FB.conversion state perform perform_val)
  (h_nl : Converts F.conversion state nameLen name_len)
  (h_ci : Converts F.conversion state colonIndex colon_index_val)
  (h_vi : Converts F.conversion state valueIndex value_index_val)
  (h_vl : Converts F.conversion state valueLen value_len)
  (h_fl : Converts F.conversion state fieldLen field_len)
  (h_maxKV : maxKVPairLen < bn254)
:
  ConvertsM FUnit.conversion
    (checkWhitespaceZones field_data perform nameLen colonIndex valueIndex valueLen fieldLen)
    state ()
    ( ( (0 < (name_len + 2).val ∧ (name_len + 2).val ≤ maxKVPairLen ∧ colon_index_val.val < maxKVPairLen) ∧
        (0 < (colon_index_val + 1).val ∧ (colon_index_val + 1).val ≤ maxKVPairLen ∧
          value_index_val.val < maxKVPairLen) ∧
        (0 < (value_index_val + value_len).val ∧ (value_index_val + value_len).val ≤ maxKVPairLen ∧
          (field_len - 1).val < maxKVPairLen) ) ∧
      (∀ i : Fin maxKVPairLen,
        lessThan.lessThanOk 8 8 field_vals[i] ∧ lessThan.lessThanOk 8 field_vals[i] 14) ∧
      (perform_val = true → ∀ i : Fin maxKVPairLen,
        (if ((decide (0 < (name_len + 2).val ∧ (name_len + 2).val ≤ i.val) &&
                decide (i.val < colon_index_val.val)) ||
             (decide (0 < (colon_index_val + 1).val ∧ (colon_index_val + 1).val ≤ i.val) &&
                decide (i.val < value_index_val.val)) ||
             (decide (0 < (value_index_val + value_len).val ∧
                  (value_index_val + value_len).val ≤ i.val) &&
                decide (i.val < (field_len - 1).val)))
           then (1 : ZMod bn254) else 0) *
          (if ((lessThan.lessThanRaw 8 8 field_vals[i] && lessThan.lessThanRaw 8 field_vals[i] 14) ||
                field_vals[i] == 32) then (0 : ZMod bn254) else 1) = 0) )
:= by
  unfold checkWhitespaceZones
  have hZones := zones_convertsM h_nl h_ci h_vi h_vl h_fl h_maxKV
  have h_field_val' := converts_skip hZones h_field_val
  have h_perform' := converts_skip hZones h_perform
  apply convertsM_bind_and hZones
  have h_inZoneF := FVec.converts_of_FArray_converts hZones.result
  have h_pair := fun i : Fin maxKVPairLen => FVec.converts_zip h_inZoneF h_field_val' i.isLt
  apply convertsM_of_convertsM
    (convertsM_foldlM_ctx_constraints (C_ctx := FB.conversion) (C_acc := FUnit.conversion)
      (init_val := ())
      (f_spec := fun (_ : Bool) (_ : Unit) (_ : ZMod bn254 × ZMod bn254) => ())
      (step_constraints := fun (g : Bool) (xv : ZMod bn254 × ZMod bn254) =>
        (lessThan.lessThanOk 8 8 xv.2 ∧ lessThan.lessThanOk 8 xv.2 14) ∧
        (g = true → xv.1 * (if ((lessThan.lessThanRaw 8 8 xv.2 && lessThan.lessThanRaw 8 xv.2 14) ||
          xv.2 == 32) then (0 : ZMod bn254) else 1) = 0))
      h_perform' h_pair FUnit.converts
      (fun h_ctx h_acc h_x => guardedWhitespaceCheck_convertsM h_ctx
        (FPair.converts_fst h_x) (FPair.converts_snd h_x)))
  · rfl
  · rw [forall_and_guard_comm]
    constructor
    · rintro ⟨hA, hB⟩
      refine ⟨fun i => ?_, fun hg i => ?_⟩
      · simpa [Vector.getElem_zip, Vector.getElem_ofFn, Vector.getElem_map] using hA i
      · simpa [Vector.getElem_zip, Vector.getElem_ofFn, Vector.getElem_map] using hB hg i
    · rintro ⟨hA, hB⟩
      refine ⟨fun i => ?_, fun hg i => ?_⟩
      · simpa [Vector.getElem_zip, Vector.getElem_ofFn, Vector.getElem_map] using hA i
      · simpa [Vector.getElem_zip, Vector.getElem_ofFn, Vector.getElem_map] using hB hg i

/-! ## Forbidden-character check

The value must not contain `,`, `}`, or `"`. Simpler than the whitespace check: `eq` compares
field elements directly (`a_val == b_val`), with no `UInt8`/`lessThan` machinery, so there is no
byte-range side-condition to carry here. -/

private lemma zmod_beq_eq_val_beq (c lit : ZMod bn254) (n : ℕ) (hlit : lit.val = n) :
    (c == lit) = (c.val == n) := by
  by_cases h : c.val = n
  · have hc : c = lit := ZMod.val_injective bn254 (by rw [hlit]; exact h)
    simp [hc, hlit]
  · have hne : c ≠ lit := fun hc => h (by rw [hc, hlit])
    simp [hne, h]

private lemma isForbidden_eq_false_iff {c_val : ZMod bn254} :
    (((c_val == (44:ZMod bn254)) || (c_val == (125:ZMod bn254))) || (c_val == (34:ZMod bn254))) = false
      ↔ c_val.val ∉ [44, 125, 34] := by
  have h44v : (44 : ZMod bn254).val = 44 := by decide
  have h125v : (125 : ZMod bn254).val = 125 := by decide
  have h34v : (34 : ZMod bn254).val = 34 := by decide
  rw [zmod_beq_eq_val_beq c_val 44 44 h44v, zmod_beq_eq_val_beq c_val 125 125 h125v,
      zmod_beq_eq_val_beq c_val 34 34 h34v]
  simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq, List.mem_cons,
    List.not_mem_nil, or_false, not_or]
  tauto

private lemma xor_le_iff_interval {a b i : ℕ} (hab : a < b) :
    (decide (a ≤ i) ^^ decide (b ≤ i)) = true ↔ a ≤ i ∧ i < b := by
  by_cases hai : a ≤ i <;> by_cases hib : b ≤ i <;> simp [hai, hib] <;> omega

/-- The per-element guarded check: `sel` (a zone/range-membership bit, as a general field element)
`and`ed with `isForbidden` (the three-way `eq`/`or` chain), then `guardedEq0`. -/
private lemma guardedForbiddenCheck_convertsM
  {state : ClapMState bn254} {perform sel : FB bn254} {c : F bn254}
  {perform_val : Bool} {sel_val c_val : ZMod bn254}
  (h_perform : Converts FB.conversion state perform perform_val)
  (h_sel : Converts F.conversion state sel sel_val)
  (h_c : Converts F.conversion state c c_val)
:
  ConvertsM FUnit.conversion
    (mkF (','.toNat : ZMod bn254) >>= fun comma =>
      eq c comma >>= fun e1 =>
      mkF ('}'.toNat : ZMod bn254) >>= fun brace =>
      eq c brace >>= fun e2 =>
      FB.or e1 e2 >>= fun or1 =>
      mkF ('\"'.toNat : ZMod bn254) >>= fun quote =>
      eq c quote >>= fun e3 =>
      FB.or or1 e3 >>= fun isForbidden =>
      sel.and isForbidden >>= fun prod =>
      guardedEq0 perform prod)
    state ()
    (perform_val = true →
      sel_val * (if (((c_val == (44:ZMod bn254)) || (c_val == (125:ZMod bn254))) ||
        (c_val == (34:ZMod bn254))) then (1:ZMod bn254) else 0) = 0)
:= by
  step mkF.convertsM as comma
  step eq.convertsM h_c h_comma as e1
  step mkF.convertsM as brace
  step eq.convertsM h_c h_brace as e2
  step FB.or.convertsM h_e1 h_e2 as or1
  step mkF.convertsM as quote
  step eq.convertsM h_c h_quote as e3
  step FB.or.convertsM h_or1 h_e3 as isForbidden
  unfold FB.and
  rw [mul_def]
  refine convertsM_bind (mkMul.convertsM h_sel (F.converts_of_FB_converts h_isForbidden)) ?_
    (fun _ => trivial)
  have hMul := mkMul.convertsM h_sel (F.converts_of_FB_converts h_isForbidden)
  replace h_perform := converts_skip hMul h_perform
  apply convertsM_of_convertsM (guardedEq0.convertsM h_perform hMul.result)
  · rfl
  · by_cases h : (((c_val == (44:ZMod bn254)) || (c_val == (125:ZMod bn254))) ||
      (c_val == (34:ZMod bn254))) <;> simp [h]

/-- The whole forbidden-character check: compute the `[valueIndex, valueIndex+valueLen)` selector,
then guard-check every position. -/
private lemma forbiddenCheckFull_convertsM
  {maxKVPairLen : ℕ} {state : ClapMState bn254}
  {field_data : FVec bn254 maxKVPairLen} {perform valueIndex valueLen : F bn254}
  {field_vals : Vector (ZMod bn254) maxKVPairLen} {perform_val : Bool}
  {value_index_val value_len : ZMod bn254}
  (h_field_val : Converts FVec.conversion state field_data field_vals)
  (h_perform : Converts FB.conversion state perform perform_val)
  (h_vi : Converts F.conversion state valueIndex value_index_val)
  (h_vl : Converts F.conversion state valueLen value_len)
  (h_maxKV : maxKVPairLen < bn254)
  (hw : 2 ^ (minBits' maxKVPairLen + 1) < bn254)
:
  ConvertsM FUnit.conversion
    (mkAdd valueIndex valueLen >>= fun viPlusVl =>
      arraySelector maxKVPairLen valueIndex viPlusVl >>= fun (valueSel : FArray bn254 maxKVPairLen) =>
      (valueSel.zip field_data).foldlM (b := ()) (fun (_ : Unit) ((sel, c) : FB bn254 × F bn254) =>
        mkF (','.toNat : ZMod bn254) >>= fun comma =>
        eq c comma >>= fun e1 =>
        mkF ('}'.toNat : ZMod bn254) >>= fun brace =>
        eq c brace >>= fun e2 =>
        FB.or e1 e2 >>= fun or1 =>
        mkF ('\"'.toNat : ZMod bn254) >>= fun quote =>
        eq c quote >>= fun e3 =>
        FB.or or1 e3 >>= fun isForbidden =>
        sel.and isForbidden >>= fun prod =>
        guardedEq0 perform prod))
    state ()
    ( ( value_index_val.val < 2 ^ minBits' maxKVPairLen ∧
        (value_index_val + value_len).val < 2 ^ minBits' maxKVPairLen ∧
        value_index_val.val < maxKVPairLen ∧
        value_index_val.val < (value_index_val + value_len).val ) ∧
      (perform_val = true → ∀ i : Fin maxKVPairLen,
        (if (decide (value_index_val.val ≤ i.val) ^^ decide ((value_index_val + value_len).val ≤ i.val))
            then (1 : ZMod bn254) else 0) *
          (if (((field_vals[i] == (44:ZMod bn254)) || (field_vals[i] == (125:ZMod bn254))) ||
              (field_vals[i] == (34:ZMod bn254))) then (1:ZMod bn254) else 0) = 0) )
:= by
  step mkAdd.convertsM h_vi h_vl as viPlusVl
  simp only [true_implies]
  have hSel := arraySelector.convertsM h_vi h_viPlusVl h_maxKV hw
  replace h_field_val := converts_skip hSel h_field_val
  replace h_perform := converts_skip hSel h_perform
  apply convertsM_bind_and hSel
  have h_selF := FVec.converts_of_FArray_converts hSel.result
  have h_pair := fun i : Fin maxKVPairLen => FVec.converts_zip h_selF h_field_val i.isLt
  apply convertsM_of_convertsM
    (convertsM_foldlM_ctx_constraints (C_ctx := FB.conversion) (C_acc := FUnit.conversion)
      (init_val := ())
      (f_spec := fun (_ : Bool) (_ : Unit) (_ : ZMod bn254 × ZMod bn254) => ())
      (step_constraints := fun (g : Bool) (xv : ZMod bn254 × ZMod bn254) =>
        g = true → xv.1 * (if (((xv.2 == (44:ZMod bn254)) || (xv.2 == (125:ZMod bn254))) ||
          (xv.2 == (34:ZMod bn254))) then (1:ZMod bn254) else 0) = 0)
      h_perform h_pair FUnit.converts
      (fun h_ctx h_acc h_x => guardedForbiddenCheck_convertsM h_ctx
        (FPair.converts_fst h_x) (FPair.converts_snd h_x)))
  · rfl
  · rw [forall_guard_comm]
    constructor
    · intro h hg i
      simpa [Vector.getElem_zip, Vector.getElem_ofFn, Vector.getElem_map] using h hg i
    · intro h hg i
      simpa [Vector.getElem_zip, Vector.getElem_ofFn, Vector.getElem_map] using h hg i

def parseJWTFieldWithUnquotedValue
  {maxKVPairLen maxNameLen maxValueLen : ℕ}
  (fi : UnquotedFieldInput maxKVPairLen maxNameLen maxValueLen)
  (h_name  : maxNameLen  ≤ maxKVPairLen)
  (h_value : maxValueLen ≤ maxKVPairLen)
  (skipChecks  : FB bn254) :
  ClapM bn254 Unit
:= do
  -- Delegate shared structural checks
  parseJWTFieldSharedLogic h_name h_value fi.field fi.name fi.value fi.colonIndex fi.valueIndex skipChecks
  let perform : FB bn254 ← not skipChecks
  -- Check 1: whitespace in three zones
  checkWhitespaceZones fi.field.data perform fi.name.len fi.colonIndex fi.valueIndex fi.value.len fi.field.len
  -- Check 2: value must not contain ',', '}', or '"'
  -- valueSelector: 1s at [valueIndex, valueIndex + value_len)
  let valueSel ← arraySelector maxKVPairLen fi.valueIndex (← fi.valueIndex + fi.value.len)
  (valueSel.zip fi.field.data).foldlM (b := ()) fun _ (sel, c) ↦ do
    let isForbidden ←
      FB.or
        (← FB.or (← eq c (← mkF ','.toNat)) (← eq c (← mkF '}'.toNat)))
        (← eq c (← mkF '\"'.toNat))
    -- If in value range, character must not be forbidden
    guardedEq0 perform (← sel.and isForbidden)

namespace parseJWTFieldWithUnquotedValue

open Poseidon RandomOracle Primes FiatShamir

open FString

def parses (H : HashFn) {maxKVPairLen maxNameLen maxValueLen : ℕ}
  (field_vals : Vector (ZMod bn254) maxKVPairLen)
  (field_len : ZMod bn254)
  (name_vals : Vector (ZMod bn254) maxNameLen)
  (name_len : ZMod bn254)
  (value_vals : Vector (ZMod bn254) maxValueLen)
  (value_len : ZMod bn254)
  (colon_index_val value_index_val : ZMod bn254)
  (skipChecks_val  : Bool) :
  Prop
:=
  ¬skipChecks_val →
    parseJWTFieldSharedLogic.parses H field_vals field_len name_vals name_len
      value_vals
      value_len
      colon_index_val
      value_index_val
      false
    ∧
    (∀ i : Fin maxKVPairLen,
      ((name_len + 2).val ≤ i.val ∧ i.val < colon_index_val.val) ∨
      (colon_index_val.val + 1 ≤ i.val ∧ i.val < value_index_val.val) ∨
      ((value_index_val + value_len).val ≤ i.val ∧ i.val < (field_len - 1).val) →
      isWs field_vals[i].val
    ) ∧
    ∀ i : Fin maxKVPairLen,
      value_index_val.val ≤ i.val ∧ i.val < (value_index_val + value_len).val →
        field_vals[i].val ∉ [44, 125, 34] -- [',', '}', '"']

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 4000 in
lemma convertsM
  {H : HashFn}
  (h_H : Computes H)
  {state : ClapMState bn254}
  -- Circuit arguments
  {maxKVPairLen maxNameLen maxValueLen : ℕ}
  (h_name_len_lt  : maxNameLen  ≤ maxKVPairLen)
  (h_value_len_lt : maxValueLen ≤ maxKVPairLen)
  -- Needed by `hashBytesToField.convertsM` (`numBytes ≤ 1953`) and, via `h_name_len_lt` /
  -- `h_value_len_lt` and `maxKVPairLen ≤ 1953 ≪ bn254`, by `isSubstring.convertsM`'s
  -- `m ≤ 1953`, `n < bn254` and `2 ^ (minBits' n + 1) < bn254` for both substring checks.
  (h_len_bound    : maxKVPairLen ≤ 1953)
  {unquoted :     UnquotedFieldInput maxKVPairLen maxNameLen maxValueLen}
  {skipChecks  : FB bn254}
  -- Ideal values
  {field_vals : Vector (ZMod bn254) maxKVPairLen}
  {field_len : ZMod bn254}
  {name_vals : Vector (ZMod bn254) maxNameLen}
  {name_len : ZMod bn254}
  {value_vals : Vector (ZMod bn254) maxValueLen}
  {value_len : ZMod bn254}
  {colon_index_val value_index_val : ZMod bn254}
  {skipChecks_val  : Bool}
  -- Conversion hypotheses
  (h_field_val : Converts FVec.conversion state unquoted.field.data field_vals)
  (h_field_len : Converts F.conversion state unquoted.field.len field_len)
  (h_name_val : Converts FVec.conversion state unquoted.name.data name_vals)
  (h_name_len : Converts F.conversion state unquoted.name.len name_len)
  (h_value_val : Converts FVec.conversion state unquoted.value.data value_vals)
  (h_value_len : Converts F.conversion state unquoted.value.len value_len)
  (h_ci : Converts F.conversion state unquoted.colonIndex colon_index_val)
  (h_vi : Converts F.conversion state unquoted.valueIndex value_index_val)
  (h_sk : Converts FB.conversion state skipChecks skipChecks_val)
  -- Range bounds (`w := 20` is hard-coded in the body)
  (h_name_len_w : name_len.val < 2 ^ 20)
  (h_colon_index_w : colon_index_val.val < 2 ^ 20)
  (h_value_index_w : value_index_val.val < 2 ^ 20)
  (h_field_len_w : field_len.val < 2 ^ 20)
  (h_sum_len_w : (name_len + value_len).val < 2 ^ 20)
  -- `checkWhitespaceZones`'s zone C (`arraySelectorComplex maxKVPairLen (valueIndex+valueLen)
  -- (fieldLen-1)`) is computed *unconditionally*, regardless of `skipChecks` — unlike
  -- `parseJWTFieldSharedLogic`'s own checks, it is not itself behind a `guardedEq0`. Its emitted
  -- constraint needs `(value_index_val+value_len).val ≤ maxKVPairLen`, which — when
  -- `skipChecks_val = true` — `parseJWTFieldSharedLogic.parses`'s check 2
  -- (`field_len > name_len + value_len`) is unavailable to supply (it sits behind that same
  -- `¬skipChecks_val →`). So, unlike the quoted sibling (which hardcodes `skipChecks := false`
  -- for `parseJWTFieldSharedLogic` and can always reach for check 2), this bound must be taken
  -- as an explicit hypothesis here.
  (h_value_window : (value_index_val + value_len).val ≤ maxKVPairLen)
  :
  ConvertsM FUnit.conversion
    (parseJWTFieldWithUnquotedValue unquoted h_name_len_lt h_value_len_lt
      skipChecks
    )
    state
    ()
    ( (∀ i : Fin maxKVPairLen, field_vals[i].val < 2^8) ∧
      (∀ i : Fin maxNameLen, name_vals[i].val < 2^8) ∧
      (∀ i : Fin maxValueLen, value_vals[i].val < 2^8) ∧

      name_len.val + 1 < maxKVPairLen ∧
      -- /- redundant -/ 0 < maxKVPairLen ∧
      colon_index_val.val < maxKVPairLen ∧
      (field_len - 1).val < maxKVPairLen ∧

      -- /- redundant -/ 1 < 2 ^ minBits' maxKVPairLen ∧
      -- /- redundant -/ (1 + name_len).val < 2 ^ minBits' maxKVPairLen ∧
      -- /- redundant -/ 1 < maxKVPairLen ∧
      -- 1 < (1 + name_len).val ∧ /- equivalent -/
      0 < name_len.val ∧

      -- /- redundant -/ value_index_val.val < 2 ^ minBits' maxKVPairLen ∧
      (value_index_val + value_len).val < 2 ^ minBits' maxKVPairLen ∧
      value_index_val.val < maxKVPairLen ∧
      -- NOT redundant, unlike the name case: `name_len.val + 1 < maxKVPairLen` above is a bound
      -- on `name_len.val` itself, so `0 < name_len.val` alone is enough to rebuild this window's
      -- `1 < (1 + name_len).val` (no wraparound, since `name_len.val` is already known small).
      -- Here `(value_index_val + value_len).val < 2 ^ minBits' maxKVPairLen` only bounds the
      -- *wrapped* sum, not `value_len.val` itself, so `0 < value_len.val` is not enough to rule
      -- out `value_len.val` being adversarially close to `bn254` (wrapping the sum back down);
      -- keep the window fact itself.
      value_index_val.val < (value_index_val + value_len).val ∧
      0 < value_len.val ∧

      parses H field_vals field_len name_vals name_len value_vals value_len
        colon_index_val
        value_index_val
        skipChecks_val
    )
:= by
  have h_maxKV : maxKVPairLen < bn254 := by
    have h1953 : (1953:ℕ) < bn254 := by decide
    omega
  have hw : 2 ^ (minBits' maxKVPairLen + 1) < bn254 := by
    have h11 : minBits' maxKVPairLen ≤ 11 := by
      unfold minBits'
      split
      · omega
      · rename_i hx
        have hx11 : maxKVPairLen < 2 ^ 11 := by omega
        have := (Nat.log2_lt hx).mpr hx11
        omega
    have h2 : (2:ℕ) ^ (minBits' maxKVPairLen + 1) ≤ 2 ^ 12 :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have h4096 : (2:ℕ)^12 < bn254 := by decide
    omega
  unfold parseJWTFieldWithUnquotedValue
  refine convertsM_of_convertsM
    (constraints1 :=
      ( ( (∀ i : Fin maxKVPairLen, field_vals[i].val < 2^8) ∧
          (∀ i : Fin maxNameLen, name_vals[i].val < 2^8) ∧
          (∀ i : Fin maxValueLen, value_vals[i].val < 2^8) ∧
          name_len.val + 1 < maxKVPairLen ∧
          colon_index_val.val < maxKVPairLen ∧
          (field_len - 1).val < maxKVPairLen ∧
          0 < name_len.val ∧
          (value_index_val + value_len).val < 2 ^ minBits' maxKVPairLen ∧
          value_index_val.val < maxKVPairLen ∧
          value_index_val.val < (value_index_val + value_len).val ∧
          0 < value_len.val ∧
          parseJWTFieldSharedLogic.parses H field_vals field_len name_vals name_len value_vals value_len
            colon_index_val value_index_val skipChecks_val ) ∧
        ( ( (0 < (name_len + 2).val ∧ (name_len + 2).val ≤ maxKVPairLen ∧ colon_index_val.val < maxKVPairLen) ∧
            (0 < (colon_index_val + 1).val ∧ (colon_index_val + 1).val ≤ maxKVPairLen ∧
              value_index_val.val < maxKVPairLen) ∧
            (0 < (value_index_val + value_len).val ∧ (value_index_val + value_len).val ≤ maxKVPairLen ∧
              (field_len - 1).val < maxKVPairLen) ) ∧
          (∀ i : Fin maxKVPairLen,
            lessThan.lessThanOk 8 8 field_vals[i] ∧ lessThan.lessThanOk 8 field_vals[i] 14) ∧
          ((!skipChecks_val) = true → ∀ i : Fin maxKVPairLen,
            (if ((decide (0 < (name_len + 2).val ∧ (name_len + 2).val ≤ i.val) &&
                    decide (i.val < colon_index_val.val)) ||
                 (decide (0 < (colon_index_val + 1).val ∧ (colon_index_val + 1).val ≤ i.val) &&
                    decide (i.val < value_index_val.val)) ||
                 (decide (0 < (value_index_val + value_len).val ∧
                      (value_index_val + value_len).val ≤ i.val) &&
                    decide (i.val < (field_len - 1).val)))
               then (1 : ZMod bn254) else 0) *
              (if ((lessThan.lessThanRaw 8 8 field_vals[i] && lessThan.lessThanRaw 8 field_vals[i] 14) ||
                    field_vals[i] == 32) then (0 : ZMod bn254) else 1) = 0) ) ∧
        ( ( value_index_val.val < 2 ^ minBits' maxKVPairLen ∧
            (value_index_val + value_len).val < 2 ^ minBits' maxKVPairLen ∧
            value_index_val.val < maxKVPairLen ∧
            value_index_val.val < (value_index_val + value_len).val ) ∧
          ((!skipChecks_val) = true → ∀ i : Fin maxKVPairLen,
            (if (decide (value_index_val.val ≤ i.val) ^^ decide ((value_index_val + value_len).val ≤ i.val))
                then (1 : ZMod bn254) else 0) *
              (if (((field_vals[i] == (44:ZMod bn254)) || (field_vals[i] == (125:ZMod bn254))) ||
                  (field_vals[i] == (34:ZMod bn254))) then (1:ZMod bn254) else 0) = 0) ) ) )
    ?_ rfl ?hiff
  · have hSL := parseJWTFieldSharedLogic.convertsM h_H h_name_len_lt h_value_len_lt h_len_bound
      h_field_val h_field_len h_name_val h_name_len h_value_val h_value_len h_ci h_vi h_sk
      h_name_len_w h_colon_index_w h_value_index_w h_field_len_w h_sum_len_w
    replace h_field_val := converts_skip hSL h_field_val
    replace h_name_len := converts_skip hSL h_name_len
    replace h_ci := converts_skip hSL h_ci
    replace h_vi := converts_skip hSL h_vi
    replace h_value_len := converts_skip hSL h_value_len
    replace h_field_len := converts_skip hSL h_field_len
    replace h_sk := converts_skip hSL h_sk
    apply convertsM_bind_and hSL
    have hNot := not.convertsM h_sk
    replace h_field_val := converts_skip hNot h_field_val
    replace h_name_len := converts_skip hNot h_name_len
    replace h_ci := converts_skip hNot h_ci
    replace h_vi := converts_skip hNot h_vi
    replace h_value_len := converts_skip hNot h_value_len
    replace h_field_len := converts_skip hNot h_field_len
    refine convertsM_bind hNot ?_ (fun _ => trivial)
    simp only [true_implies]
    have h_perform := hNot.result
    have hCheckWS := checkWhitespaceZones.convertsM h_field_val h_perform h_name_len h_ci h_vi
      h_value_len h_field_len h_maxKV
    replace h_field_val := converts_skip hCheckWS h_field_val
    replace h_vi := converts_skip hCheckWS h_vi
    replace h_value_len := converts_skip hCheckWS h_value_len
    replace h_perform := converts_skip hCheckWS h_perform
    exact convertsM_bind_and hCheckWS
      (forbiddenCheckFull_convertsM h_field_val h_perform h_vi h_value_len h_maxKV hw)
  case hiff =>
    have hskf_of_neg : ¬skipChecks_val → skipChecks_val = false := by
      intro hneg
      revert hneg
      cases skipChecks_val <;> simp
    constructor
    · rintro ⟨⟨hB1, hB2, hB3, hW1, hW2, hW3, hP1, hV1, hV2, hV3, hP2, hSLparses⟩,
        ⟨⟨hZA, hZB, hZC⟩, hZok, hZarith⟩, ⟨⟨hFV1, hFV2, hFV3, hFV4⟩, hFarith⟩⟩
      refine ⟨hB1, hB2, hB3, hW1, hW2, hW3, hP1, hV1, hV2, hV3, hP2, ?_⟩
      intro hneg
      have hskf := hskf_of_neg hneg
      have hguard : (!skipChecks_val) = true := by simp [hskf]
      have h2v : (2 : ZMod bn254).val = 2 := by decide
      have h1v : (1 : ZMod bn254).val = 1 := by decide
      have h_name2 : (name_len + 2).val = name_len.val + 2 := by
        have hlt : name_len.val + (2 : ZMod bn254).val < bn254 := by rw [h2v]; omega
        rw [ZMod.val_add_of_lt hlt, h2v]
      have h_ci1 : (colon_index_val + 1).val = colon_index_val.val + 1 := by
        have hlt : colon_index_val.val + (1 : ZMod bn254).val < bn254 := by rw [h1v]; omega
        rw [ZMod.val_add_of_lt hlt, h1v]
      have h_vv : (value_index_val + value_len).val = value_index_val.val + value_len.val := by
        have hvi_lt : value_index_val.val < bn254 := ZMod.val_lt _
        have hvl_lt : value_len.val < bn254 := ZMod.val_lt _
        have hmod : (value_index_val + value_len).val
            = (value_index_val.val + value_len.val) % bn254 := ZMod.val_add _ _
        rcases lt_or_ge (value_index_val.val + value_len.val) bn254 with hlt | hge
        · rw [hmod, Nat.mod_eq_of_lt hlt]
        · exfalso
          have h1 : value_index_val.val + value_len.val - bn254 < bn254 := by omega
          have h2 : value_index_val.val + value_len.val
              = bn254 + (value_index_val.val + value_len.val - bn254) := by omega
          have heq : (value_index_val.val + value_len.val) % bn254
              = value_index_val.val + value_len.val - bn254 := by
            conv_lhs => rw [h2]
            rw [Nat.add_mod_left, Nat.mod_eq_of_lt h1]
          omega
      refine ⟨fun _ => hSLparses hneg, ?_, ?_⟩
      · intro i hranges
        have hzarith_i := hZarith hguard i
        have hzone_true :
            ((decide (0 < (name_len + 2).val ∧ (name_len + 2).val ≤ i.val) &&
                  decide (i.val < colon_index_val.val)) ||
              (decide (0 < (colon_index_val + 1).val ∧ (colon_index_val + 1).val ≤ i.val) &&
                  decide (i.val < value_index_val.val)) ||
              (decide (0 < (value_index_val + value_len).val ∧
                    (value_index_val + value_len).val ≤ i.val) &&
                  decide (i.val < (field_len - 1).val))) = true := by
          simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
          rcases hranges with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inl (Or.inl ⟨⟨by omega, by omega⟩, h2⟩)
          · exact Or.inl (Or.inr ⟨⟨by omega, by omega⟩, h2⟩)
          · exact Or.inr ⟨⟨by omega, by omega⟩, h2⟩
        rw [hzone_true] at hzarith_i
        simp only [if_true, one_mul] at hzarith_i
        by_contra hws
        have hraw : ((lessThan.lessThanRaw 8 8 field_vals[i] && lessThan.lessThanRaw 8 field_vals[i] 14) ||
            field_vals[i] == 32) = false := by
          rw [lessThanRaw_isWs_eq (hB1 i)]
          simpa using hws
        rw [hraw] at hzarith_i
        simp at hzarith_i
      · intro i hrange
        have hfarith_i := hFarith hguard i
        have hxor_true :
            (decide (value_index_val.val ≤ i.val) ^^ decide ((value_index_val + value_len).val ≤ i.val)) = true :=
          (xor_le_iff_interval hV3).mpr hrange
        rw [hxor_true] at hfarith_i
        simp only [if_true, one_mul] at hfarith_i
        intro hforbidden
        have hraw : (((field_vals[i] == (44:ZMod bn254)) || (field_vals[i] == (125:ZMod bn254))) ||
            (field_vals[i] == (34:ZMod bn254))) = true := by
          by_contra hc
          exact absurd hforbidden (isForbidden_eq_false_iff.mp (by simpa using hc))
        rw [hraw] at hfarith_i
        simp at hfarith_i
    · rintro ⟨hB1, hB2, hB3, hW1, hW2, hW3, hP1, hV1, hV2, hV3, hP2, hparses⟩
      have hZA' : 0 < (name_len + 2).val ∧ (name_len + 2).val ≤ maxKVPairLen ∧
          colon_index_val.val < maxKVPairLen := by
        have h2v : (2 : ZMod bn254).val = 2 := by decide
        have hlt : name_len.val + (2 : ZMod bn254).val < bn254 := by rw [h2v]; omega
        rw [ZMod.val_add_of_lt hlt, h2v]
        omega
      have hZB' : 0 < (colon_index_val + 1).val ∧ (colon_index_val + 1).val ≤ maxKVPairLen ∧
          value_index_val.val < maxKVPairLen := by
        have h1v : (1 : ZMod bn254).val = 1 := by decide
        have hlt : colon_index_val.val + (1 : ZMod bn254).val < bn254 := by rw [h1v]; omega
        rw [ZMod.val_add_of_lt hlt, h1v]
        omega
      have hZC' : 0 < (value_index_val + value_len).val ∧ (value_index_val + value_len).val ≤ maxKVPairLen ∧
          (field_len - 1).val < maxKVPairLen := ⟨by omega, h_value_window, hW3⟩
      have hFmb1 : value_index_val.val < 2 ^ minBits' maxKVPairLen := minBits_lt hV2
      have hFmb2 : (value_index_val + value_len).val < 2 ^ minBits' maxKVPairLen := hV1
      refine ⟨⟨hB1, hB2, hB3, hW1, hW2, hW3, hP1, hV1, hV2, hV3, hP2, ?_⟩,
        ⟨⟨hZA', hZB', hZC'⟩, fun i => ⟨lessThan.lessThanOk_of
          (show (8 : ZMod bn254).val < 2 ^ 8 by decide) (hB1 i) (by decide),
          lessThan.lessThanOk_of (hB1 i) (show (14 : ZMod bn254).val < 2 ^ 8 by decide) (by decide)⟩, ?_⟩,
        ⟨⟨hFmb1, hFmb2, hV2, hV3⟩, ?_⟩⟩
      · intro hneg
        exact (hparses hneg).1 (by decide)
      · intro hguard i
        by_cases hzone :
            ((decide (0 < (name_len + 2).val ∧ (name_len + 2).val ≤ i.val) &&
                  decide (i.val < colon_index_val.val)) ||
              (decide (0 < (colon_index_val + 1).val ∧ (colon_index_val + 1).val ≤ i.val) &&
                  decide (i.val < value_index_val.val)) ||
              (decide (0 < (value_index_val + value_len).val ∧
                    (value_index_val + value_len).val ≤ i.val) &&
                  decide (i.val < (field_len - 1).val))) = true
        · have hneg : ¬skipChecks_val := by
            intro h; rw [h] at hguard; simp at hguard
          have h1v : (1 : ZMod bn254).val = 1 := by decide
          have h_ci1 : (colon_index_val + 1).val = colon_index_val.val + 1 := by
            have hlt : colon_index_val.val + (1 : ZMod bn254).val < bn254 := by rw [h1v]; omega
            rw [ZMod.val_add_of_lt hlt, h1v]
          have h_vv : (value_index_val + value_len).val = value_index_val.val + value_len.val := by
            have hvi_lt : value_index_val.val < bn254 := ZMod.val_lt _
            have hvl_lt : value_len.val < bn254 := ZMod.val_lt _
            have hmod : (value_index_val + value_len).val
                = (value_index_val.val + value_len.val) % bn254 := ZMod.val_add _ _
            rcases lt_or_ge (value_index_val.val + value_len.val) bn254 with hlt | hge
            · rw [hmod, Nat.mod_eq_of_lt hlt]
            · exfalso
              have h1 : value_index_val.val + value_len.val - bn254 < bn254 := by omega
              have h2 : value_index_val.val + value_len.val
                  = bn254 + (value_index_val.val + value_len.val - bn254) := by omega
              have heq : (value_index_val.val + value_len.val) % bn254
                  = value_index_val.val + value_len.val - bn254 := by
                conv_lhs => rw [h2]
                rw [Nat.add_mod_left, Nat.mod_eq_of_lt h1]
              omega
          have hranges_i :
              ((name_len + 2).val ≤ i.val ∧ i.val < colon_index_val.val) ∨
              (colon_index_val.val + 1 ≤ i.val ∧ i.val < value_index_val.val) ∨
              ((value_index_val + value_len).val ≤ i.val ∧ i.val < (field_len - 1).val) := by
            simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hzone
            rcases hzone with (⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩
            · exact Or.inl ⟨h1.2, h2⟩
            · exact Or.inr (Or.inl ⟨by omega, h2⟩)
            · exact Or.inr (Or.inr ⟨by omega, h2⟩)
          have hws_i := (hparses hneg).2.1 i hranges_i
          rw [hzone]
          rw [lessThanRaw_isWs_eq (hB1 i)]
          simpa using hws_i
        · simp only [Bool.not_eq_true] at hzone
          rw [hzone]
          simp
      · intro hguard i
        by_cases hxor :
            (decide (value_index_val.val ≤ i.val) ^^ decide ((value_index_val + value_len).val ≤ i.val)) = true
        · have hneg : ¬skipChecks_val := by
            intro h; rw [h] at hguard; simp at hguard
          have hrange_i : value_index_val.val ≤ i.val ∧ i.val < (value_index_val + value_len).val :=
            (xor_le_iff_interval hV3).mp hxor
          have hnf_i := (hparses hneg).2.2 i hrange_i
          rw [hxor]
          rw [show (((field_vals[i] == (44:ZMod bn254)) || (field_vals[i] == (125:ZMod bn254))) ||
              (field_vals[i] == (34:ZMod bn254))) = false from isForbidden_eq_false_iff.mpr hnf_i]
          simp
        · simp only [Bool.not_eq_true] at hxor
          rw [hxor]
          simp

theorem sound {nF nN nV} (field name value : String)
  (colonIndex valueIndex : ZMod bn254)
  (h_fieldLen : field.length ≤ nF) (h_nameLen : name.length ≤ nN) (h_valueLen : value.length ≤ nV)
  (h_namePos : 0 < name.length) (h_valuePos : 0 < value.length)
  (h_nF_name : 1 < nF) (h_valueIndex : valueIndex.val < nF)
  (h_nm_name : nF + nN < bn254) (h_nm_value : nF + nV < bn254)
  (h_fieldBytes : ∀ c ∈ field.toList, c.toNat < 256)
  (h_nameBytes : ∀ c ∈ name.toList, 0 < c.toNat ∧ c.toNat < 256)
  (h_valueBytes : ∀ c ∈ value.toList, 0 < c.toNat ∧ c.toNat < 256)
  (h_bad :
    ¬ (1 + name.length ≤ field.length ∧ name.toList <+: field.toList.drop 1) ∨
    ¬ (valueIndex.val + value.length ≤ field.length ∧
        value.toList <+: field.toList.drop valueIndex.val
      )
  )
  :
  randomOracle.toOuterMeasure
    {f |
      parses (skipChecks_val := false) (Query.toHashFn f)
        (encodeV nF field)
        field.length
        (encodeV nN name)
        name.length
        (encodeV nV value)
        value.length
        colonIndex
        valueIndex
        } ≤ (((nF - 1) + (max nN nV - 1) + 50 : ℕ) : ENNReal) / bn254
:= by
  have h_sub : {f : Query → ZMod bn254 |
      parses (skipChecks_val := false) (Query.toHashFn f) (encodeV nF field) field.length
        (encodeV nN name) name.length (encodeV nV value) value.length colonIndex valueIndex} ⊆
      {f | parseJWTFieldSharedLogic.parses (Query.toHashFn f) (encodeV nF field) field.length
        (encodeV nN name) name.length (encodeV nV value) value.length colonIndex valueIndex
        false} := by
    intro f hf
    unfold parses at hf
    obtain ⟨h1, -, -⟩ := hf (by decide)
    exact h1
  exact (MeasureTheory.measure_mono h_sub).trans
    (parseJWTFieldSharedLogic.sound field name value colonIndex valueIndex h_fieldLen h_nameLen
      h_valueLen h_namePos h_valuePos h_nF_name h_valueIndex h_nm_name h_nm_value h_fieldBytes
      h_nameBytes h_valueBytes h_bad)

end parseJWTFieldWithUnquotedValue
