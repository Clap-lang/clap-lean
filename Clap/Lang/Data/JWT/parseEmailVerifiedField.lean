import Clap.RandomOracle.HashFn
import Clap.Lang.Core.F.mkF
import Clap.Lang.Core.F.mkSub
import Clap.Lang.Core.F.mkAdd
import Clap.Lang.Core.F.lessThan
import Clap.Lang.Core.F.conditionalSwap
import Clap.Lang.Core.FB.eq
import Clap.Lang.Core.FB.not
import Clap.Lang.Core.FB.or
import Clap.Lang.Data.F8.isWhitespace
import Clap.Lang.Gate.isZero
import Clap.Lang.Gate.eq0
import Clap.Lang.Core.Combinators.scanlM
import Clap.Lang.Core.Combinators.mapM
import Clap.Lang.Core.Combinators.foldlM
import Clap.Lang.Poseidon.Poseidon
import Clap.Util.Wheels
import Clap.Model.Convert.PaddedVector
import Clap.Lang.Core.FUnit.guardedEq0
import Clap.Util.Primes
import Clap.Lang.Data.HashToField.hashBytesToField
import Clap.Lang.Data.FString.isSubstring
import Clap.Lang.Data.FArray.selectArrayValue
import Clap.Lang.Data.FArray.arraySelectorComplex
import Clap.Lang.Core.FUnit.guardedAssertEq
import Clap.Lang.Data.JWT.parseJWTFieldSharedLogic
import Clap.Lang.Data.JWT.Basic
import Mathlib.Data.List.GetD

namespace Clap.Lang

open Primes

/-- `field_vals.getD idx 0` is always a byte: in range it is `field_vals[idx]`, out of range it
is the default `0`. -/
private lemma getD_byte_bound {k : ℕ} {field_vals : Vector (ZMod bn254) k}
    (h_byte : ∀ i : Fin k, field_vals[i].val < 2 ^ 8) (idx : ℕ) :
    (field_vals.getD idx 0).val < 2 ^ 8 := by
  by_cases h : idx < k
  · have := h_byte ⟨idx, h⟩
    simpa [Vector.getD, h] using this
  · simp [Vector.getD, h]

/-- `F8.isWhitespace`'s checked value (`UInt8` comparisons against a byte known `< 2^8`) equals
the plain-`ℕ` `isWs` predicate used throughout this file's specs. -/
private lemma isWhitespace_val_eq {c_val : ZMod bn254} (h_c8 : c_val.val < 2 ^ 8) :
    ((UInt8.ofNat c_val.val) > 8 && (UInt8.ofNat c_val.val) < 14 || (UInt8.ofNat c_val.val) = 32)
      = isWs c_val.val := by
  have h32 : (UInt8.toNat 32) = 32 := by decide
  have h8 : (UInt8.toNat 8) = 8 := by decide
  have h14 : (UInt8.toNat 14) = 14 := by decide
  simp only [isWs, UInt8.lt_iff_toNat_lt, ← UInt8.toNat_inj, UInt8.toNat_ofNat',
    h32, h8, h14, Nat.mod_eq_of_lt h_c8]

/-- `F8.isWhitespace`'s *unchecked* raw value (in terms of `lessThan.lessThanRaw`, for a byte
consumed without a typed `F8.conversion` fact) equals the plain-`ℕ` `isWs` predicate, given the
byte is known `< 2^8`. Companion to `isWhitespace_val_eq` above, which does the same for the
*checked*, `UInt8`-typed form; `checkWhitespaceZones`'s per-element `foldlM` step can only use the
unchecked form (its combinator has no way to thread a per-index range hypothesis), hence needs
this version instead. -/
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

/-! ## `Vector.zipWithM`: a combinator lemma with nowhere layering-safe to live

`Vector.zipWithM` (`Clap/Lang/Poseidon/Poseidon.lean`) is generic, model-agnostic Vector plumbing
that happens to be defined in a Poseidon file. `Lang/Core/Combinators/` (where the other
`convertsM_*` combinator lemmas live) sits *below* `Lang/Poseidon` in the import order
(`Gate → Core → Poseidon → Data`), so a lemma about it cannot live there without a layering
violation. `Lang/Data/JWT` sits above `Lang/Poseidon`, so it is kept here, private to this file's
only two current uses (`checkWhitespaceZones` below, and `parseJWTFieldWithUnquotedValue`'s
identical zone merge later). -/

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

/-- Checks the character just before the value: it must be a quote, whitespace, or there is no
gap (the value starts right after the colon). Returns `beforeIsQuote`, reused by the
no-mismatched-quotes check in the main body. -/
private def checkCharBeforeValue.notOrDef (isQuote : FB bn254) (c one : F bn254) :
    ClapM bn254 (F bn254) := do
  let isWhitespace ← F8.isWhitespace c
  let isWsOrQuote ← FB.or isQuote isWhitespace
  mkSub one isWsOrQuote

private def checkCharBeforeValue.restDef (notOr colonIndex valueIndex one : F bn254) :
    ClapM bn254 Unit := do
  let vMinus1 ← mkSub valueIndex one
  let diff ← mkSub vMinus1 colonIndex
  eq0 (← mkMul notOr diff)

private def checkCharBeforeValue {maxKVPairLen : ℕ}
    (field_data : FVec bn254 maxKVPairLen) (colonIndex valueIndex : F bn254) :
    ClapM bn254 (FB bn254) := do
  let one ← mkF 1
  let charBeforeValue ← selectArrayValue maxKVPairLen field_data (← valueIndex - one)
  let beforeIsQuote ← eq charBeforeValue (← mkF '\"'.toNat)
  let notOr ← checkCharBeforeValue.notOrDef beforeIsQuote charBeforeValue one
  checkCharBeforeValue.restDef notOr colonIndex valueIndex one
  return beforeIsQuote

-- `notOrDef`'s own proof: combines `F8.isWhitespace`'s *unchecked* form (no byte-range hypothesis
-- — see `checkWhitespaceZones`'s own comment for why) with `FB.or`/`mkSub`, three actions deep.
-- Kept as its own lemma (not inlined into `tail_convertsM`) with a *concrete* stated conclusion:
-- combining all six real-and-trivial actions of the full tail in one tactic block (as an earlier
-- version of this proof did) caused a severe `whnf`/stack-depth blowup when threading `isQuote`'s
-- own `Converts` fact all the way to the end — the same `whnf` wall `docs/proving-circuits.md`
-- describes, fixed the same way `zonesTail_convertsM` above is: split, prove each concrete piece
-- on its own, and only ever `apply convertsM_bind_and <fact>` directly against a live goal.
private lemma checkCharBeforeValue.notOrDef.convertsM
  {state : ClapMState bn254} {isQuote : FB bn254} {c one : F bn254}
  {isQuote_val : Bool} {c_val : ZMod bn254}
  (h_isQuote : Converts FB.conversion state isQuote isQuote_val)
  (h_c : Converts F.conversion state c c_val)
  (h_one : Converts F.conversion state one (1 : ZMod bn254))
:
  ConvertsM F.conversion
    (checkCharBeforeValue.notOrDef isQuote c one)
    state
    (1 - (if (isQuote_val ||
        ((lessThan.lessThanRaw 8 8 c_val && lessThan.lessThanRaw 8 c_val 14) || c_val == 32))
      then (1 : ZMod bn254) else 0))
    ((lessThan.lessThanOk 8 8 c_val ∧ lessThan.lessThanOk 8 c_val 14) ∧ True)
:= by
  unfold checkCharBeforeValue.notOrDef
  have hWs := F8.isWhitespace.convertsM_unchecked h_c
  replace h_isQuote := converts_skip hWs h_isQuote
  replace h_one := converts_skip hWs h_one
  apply convertsM_bind_and hWs
  refine convertsM_bind (FB.or.convertsM h_isQuote hWs.result) ?_ (fun _ => trivial)
  have hOr := FB.or.convertsM h_isQuote hWs.result
  replace h_one := converts_skip hOr h_one
  have hOrF := F.converts_of_FB_converts hOr.result
  apply convertsM_of_convertsM (mkSub.convertsM h_one hOrF) rfl
  simp only [true_implies]

-- The purely-arithmetic rest of `checkCharBeforeValue`'s tail, given `notOr` as a plain value
-- (never touching `F8.isWhitespace`, hence no un-opaque state and `step` behaves normally here).
private lemma checkCharBeforeValue.restDef.convertsM
  {state : ClapMState bn254} {notOr colonIndex valueIndex one : F bn254}
  {notOr_val colon_index_val value_index_val : ZMod bn254}
  (h_notOr : Converts F.conversion state notOr notOr_val)
  (h_ci : Converts F.conversion state colonIndex colon_index_val)
  (h_vi : Converts F.conversion state valueIndex value_index_val)
  (h_one : Converts F.conversion state one (1 : ZMod bn254))
:
  ConvertsM FUnit.conversion
    (checkCharBeforeValue.restDef notOr colonIndex valueIndex one)
    state ()
    (notOr_val * (value_index_val - 1 - colon_index_val) = 0)
:= by
  unfold checkCharBeforeValue.restDef
  step mkSub.convertsM h_vi h_one as vMinus1
  step mkSub.convertsM h_vMinus1 h_ci as diff
  step mkMul.convertsM h_notOr h_diff as prod
  simp only [true_implies]
  exact eq0.convertsM h_prod

private lemma checkCharBeforeValue.tail_convertsM
  {state : ClapMState bn254} {c one colonIndex valueIndex : F bn254}
  {c_val colon_index_val value_index_val : ZMod bn254}
  (h_c : Converts F.conversion state c c_val)
  (h_one : Converts F.conversion state one (1 : ZMod bn254))
  (h_ci : Converts F.conversion state colonIndex colon_index_val)
  (h_vi : Converts F.conversion state valueIndex value_index_val)
:
  ConvertsM FB.conversion
    (mkF ('\"'.toNat : ZMod bn254) >>= fun q =>
      eq c q >>= fun isQuote =>
      checkCharBeforeValue.notOrDef isQuote c one >>= fun notOr =>
      checkCharBeforeValue.restDef notOr colonIndex valueIndex one >>= fun _ =>
      pure isQuote)
    state (c_val == (34 : ZMod bn254))
    ( (lessThan.lessThanOk 8 8 c_val ∧ lessThan.lessThanOk 8 c_val 14) ∧
      ( c_val.val = 34 ∨
        ((lessThan.lessThanRaw 8 8 c_val && lessThan.lessThanRaw 8 c_val 14) || c_val == 32) = true ∨
        value_index_val - 1 = colon_index_val ) )
:= by
  step mkF.convertsM as q
  step eq.convertsM h_c h_q as isQuote
  set isQuote_val := (c_val == ('\"'.toNat : ZMod bn254)) with hiq_def
  simp only [true_implies]
  have hNotOr :
      ConvertsM F.conversion (checkCharBeforeValue.notOrDef isQuote_result c one) isQuote_state
        (1 - (if (isQuote_val ||
            ((lessThan.lessThanRaw 8 8 c_val && lessThan.lessThanRaw 8 c_val 14) || c_val == 32))
          then (1 : ZMod bn254) else 0))
        (lessThan.lessThanOk 8 8 c_val ∧ lessThan.lessThanOk 8 c_val 14) :=
    convertsM_of_convertsM (checkCharBeforeValue.notOrDef.convertsM h_isQuote h_c h_one) rfl (by simp)
  replace h_isQuote := converts_skip hNotOr h_isQuote
  replace h_ci := converts_skip hNotOr h_ci
  replace h_vi := converts_skip hNotOr h_vi
  replace h_one := converts_skip hNotOr h_one
  apply convertsM_bind_and hNotOr
  have hRest := checkCharBeforeValue.restDef.convertsM hNotOr.result h_ci h_vi h_one
  replace h_isQuote := converts_skip hRest h_isQuote
  have h_quote_iff : isQuote_val = true ↔ c_val.val = 34 := by
    rw [hiq_def, beq_iff_eq]
    constructor
    · intro h; rw [h]; decide
    · intro h
      have h' : c_val.val = (('\"'.toNat : ZMod bn254)).val := by rw [h]; decide
      exact ZMod.val_injective bn254 h'
  have h_target_iff :
      (1 - if (isQuote_val ||
          ((lessThan.lessThanRaw 8 8 c_val && lessThan.lessThanRaw 8 c_val 14) || c_val == 32))
            then (1 : ZMod bn254) else 0) *
          (value_index_val - 1 - colon_index_val) = 0
        ↔ (c_val.val = 34 ∨
            ((lessThan.lessThanRaw 8 8 c_val && lessThan.lessThanRaw 8 c_val 14) || c_val == 32) = true ∨
            value_index_val - 1 = colon_index_val) := by
    rw [mul_eq_zero, sub_eq_zero, sub_eq_zero]
    cases h1 : isQuote_val <;>
      cases h2 : ((lessThan.lessThanRaw 8 8 c_val && lessThan.lessThanRaw 8 c_val 14) || c_val == 32) <;>
      simp_all [Bool.or_eq_true]
  refine convertsM_bind (convertsM_of_convertsM hRest rfl h_target_iff) ?_ id
  apply convertsM_pure
  · exact h_isQuote
  · exact id

lemma checkCharBeforeValue.convertsM
  {maxKVPairLen : ℕ} {state : ClapMState bn254}
  {field_data : FVec bn254 maxKVPairLen} {colonIndex valueIndex : F bn254}
  {field_vals : Vector (ZMod bn254) maxKVPairLen} {colon_index_val value_index_val : ZMod bn254}
  (h_field_val : Converts FVec.conversion state field_data field_vals)
  (h_ci : Converts F.conversion state colonIndex colon_index_val)
  (h_vi : Converts F.conversion state valueIndex value_index_val)
  (h_maxKV : maxKVPairLen < bn254)
:
  ConvertsM FB.conversion (checkCharBeforeValue field_data colonIndex valueIndex) state
    (field_vals.getD (value_index_val - 1).val 0 == (34 : ZMod bn254))
    ( (value_index_val - 1).val < maxKVPairLen ∧
      (let v := field_vals.getD (value_index_val - 1).val 0
       (lessThan.lessThanOk 8 8 v ∧ lessThan.lessThanOk 8 v 14) ∧
       ( v.val = 34 ∨
         ((lessThan.lessThanRaw 8 8 v && lessThan.lessThanRaw 8 v 14) || v == 32) = true ∨
         value_index_val - 1 = colon_index_val )) )
:= by
  unfold checkCharBeforeValue
  step mkF.convertsM as one
  step mkSub.convertsM h_vi h_one as vMinus1
  have hSel := selectArrayValue.convertsM h_vMinus1 h_field_val h_maxKV
  have h_one' := converts_skip hSel h_one
  have h_ci' := converts_skip hSel h_ci
  have h_vi' := converts_skip hSel h_vi
  apply convertsM_of_convertsM
    (convertsM_bind_and hSel
      (checkCharBeforeValue.tail_convertsM hSel.result h_one' h_ci' h_vi'))
  · rfl
  · simp only [true_implies]

-- The purely-arithmetic rest of `checkCharAfterValue`'s tail, given `notOr` as a plain value —
-- symmetric to `checkCharBeforeValue.restDef`. Reuses `checkCharBeforeValue.notOrDef` for the
-- `isWhitespace`/`FB.or`/`mkSub` prefix (identical computation in both directions), so only this
-- arithmetic tail needs its own `def`. Defined before `checkCharAfterValue` itself, which calls it.
private def checkCharAfterValue.restDef (notOr fieldLen valueIndex valueLen one : F bn254) :
    ClapM bn254 Unit := do
  let flMinus1 ← mkSub fieldLen one
  let flMinus1MinusVi ← mkSub flMinus1 valueIndex
  let diff ← mkSub flMinus1MinusVi valueLen
  eq0 (← mkMul notOr diff)

/-- Checks the character just after the value: symmetric to `checkCharBeforeValue`. Returns
`afterIsQuote`. -/
private def checkCharAfterValue {maxKVPairLen : ℕ}
    (field_data : FVec bn254 maxKVPairLen) (valueLen fieldLen valueIndex : F bn254) :
    ClapM bn254 (FB bn254) := do
  let one ← mkF 1
  let charAfterValue ← selectArrayValue maxKVPairLen field_data (← valueIndex + valueLen)
  let afterIsQuote ← eq charAfterValue (← mkF '\"'.toNat)
  let notOr ← checkCharBeforeValue.notOrDef afterIsQuote charAfterValue one
  checkCharAfterValue.restDef notOr fieldLen valueIndex valueLen one
  return afterIsQuote

private lemma checkCharAfterValue.restDef.convertsM
  {state : ClapMState bn254} {notOr fieldLen valueIndex valueLen one : F bn254}
  {notOr_val field_len value_index_val value_len : ZMod bn254}
  (h_notOr : Converts F.conversion state notOr notOr_val)
  (h_fl : Converts F.conversion state fieldLen field_len)
  (h_vi : Converts F.conversion state valueIndex value_index_val)
  (h_vl : Converts F.conversion state valueLen value_len)
  (h_one : Converts F.conversion state one (1 : ZMod bn254))
:
  ConvertsM FUnit.conversion
    (checkCharAfterValue.restDef notOr fieldLen valueIndex valueLen one)
    state ()
    (notOr_val * (field_len - 1 - value_index_val - value_len) = 0)
:= by
  unfold checkCharAfterValue.restDef
  step mkSub.convertsM h_fl h_one as flMinus1
  step mkSub.convertsM h_flMinus1 h_vi as flMinus1MinusVi
  step mkSub.convertsM h_flMinus1MinusVi h_vl as diff
  step mkMul.convertsM h_notOr h_diff as prod
  simp only [true_implies]
  exact eq0.convertsM h_prod

private lemma checkCharAfterValue.tail_convertsM
  {state : ClapMState bn254} {c one fieldLen valueIndex valueLen : F bn254}
  {c_val field_len value_index_val value_len : ZMod bn254}
  (h_c : Converts F.conversion state c c_val)
  (h_one : Converts F.conversion state one (1 : ZMod bn254))
  (h_fl : Converts F.conversion state fieldLen field_len)
  (h_vi : Converts F.conversion state valueIndex value_index_val)
  (h_vl : Converts F.conversion state valueLen value_len)
:
  ConvertsM FB.conversion
    (mkF ('\"'.toNat : ZMod bn254) >>= fun q =>
      eq c q >>= fun isQuote =>
      checkCharBeforeValue.notOrDef isQuote c one >>= fun notOr =>
      checkCharAfterValue.restDef notOr fieldLen valueIndex valueLen one >>= fun _ =>
      pure isQuote)
    state (c_val == (34 : ZMod bn254))
    ( (lessThan.lessThanOk 8 8 c_val ∧ lessThan.lessThanOk 8 c_val 14) ∧
      ( c_val.val = 34 ∨
        ((lessThan.lessThanRaw 8 8 c_val && lessThan.lessThanRaw 8 c_val 14) || c_val == 32) = true ∨
        field_len = value_index_val + value_len + 1 ) )
:= by
  step mkF.convertsM as q
  step eq.convertsM h_c h_q as isQuote
  set isQuote_val := (c_val == ('\"'.toNat : ZMod bn254)) with hiq_def
  simp only [true_implies]
  have hNotOr :
      ConvertsM F.conversion (checkCharBeforeValue.notOrDef isQuote_result c one) isQuote_state
        (1 - (if (isQuote_val ||
            ((lessThan.lessThanRaw 8 8 c_val && lessThan.lessThanRaw 8 c_val 14) || c_val == 32))
          then (1 : ZMod bn254) else 0))
        (lessThan.lessThanOk 8 8 c_val ∧ lessThan.lessThanOk 8 c_val 14) :=
    convertsM_of_convertsM (checkCharBeforeValue.notOrDef.convertsM h_isQuote h_c h_one) rfl (by simp)
  replace h_isQuote := converts_skip hNotOr h_isQuote
  replace h_fl := converts_skip hNotOr h_fl
  replace h_vi := converts_skip hNotOr h_vi
  replace h_vl := converts_skip hNotOr h_vl
  replace h_one := converts_skip hNotOr h_one
  apply convertsM_bind_and hNotOr
  have hRest := checkCharAfterValue.restDef.convertsM hNotOr.result h_fl h_vi h_vl h_one
  replace h_isQuote := converts_skip hRest h_isQuote
  have h_quote_iff : isQuote_val = true ↔ c_val.val = 34 := by
    rw [hiq_def, beq_iff_eq]
    constructor
    · intro h; rw [h]; decide
    · intro h
      have h' : c_val.val = (('\"'.toNat : ZMod bn254)).val := by rw [h]; decide
      exact ZMod.val_injective bn254 h'
  have h_target_iff :
      (1 - if (isQuote_val ||
          ((lessThan.lessThanRaw 8 8 c_val && lessThan.lessThanRaw 8 c_val 14) || c_val == 32))
            then (1 : ZMod bn254) else 0) *
          (field_len - 1 - value_index_val - value_len) = 0
        ↔ (c_val.val = 34 ∨
            ((lessThan.lessThanRaw 8 8 c_val && lessThan.lessThanRaw 8 c_val 14) || c_val == 32) = true ∨
            field_len = value_index_val + value_len + 1) := by
    rw [mul_eq_zero]
    have h_diff_eq : field_len - 1 - value_index_val - value_len = 0 ↔
        field_len = value_index_val + value_len + 1 := by
      constructor
      · intro h; have := sub_eq_zero.mp h; linear_combination this
      · intro h; rw [h]; ring
    rw [h_diff_eq]
    cases h1 : isQuote_val <;>
      cases h2 : ((lessThan.lessThanRaw 8 8 c_val && lessThan.lessThanRaw 8 c_val 14) || c_val == 32) <;>
      simp_all [Bool.or_eq_true]
  refine convertsM_bind (convertsM_of_convertsM hRest rfl h_target_iff) ?_ id
  apply convertsM_pure
  · exact h_isQuote
  · exact id

lemma checkCharAfterValue.convertsM
  {maxKVPairLen : ℕ} {state : ClapMState bn254}
  {field_data : FVec bn254 maxKVPairLen} {valueLen fieldLen valueIndex : F bn254}
  {field_vals : Vector (ZMod bn254) maxKVPairLen} {value_len field_len value_index_val : ZMod bn254}
  (h_field_val : Converts FVec.conversion state field_data field_vals)
  (h_vl : Converts F.conversion state valueLen value_len)
  (h_fl : Converts F.conversion state fieldLen field_len)
  (h_vi : Converts F.conversion state valueIndex value_index_val)
  (h_maxKV : maxKVPairLen < bn254)
:
  ConvertsM FB.conversion (checkCharAfterValue field_data valueLen fieldLen valueIndex) state
    (field_vals.getD (value_index_val + value_len).val 0 == (34 : ZMod bn254))
    ( (value_index_val + value_len).val < maxKVPairLen ∧
      (let v := field_vals.getD (value_index_val + value_len).val 0
       (lessThan.lessThanOk 8 8 v ∧ lessThan.lessThanOk 8 v 14) ∧
       ( v.val = 34 ∨
         ((lessThan.lessThanRaw 8 8 v && lessThan.lessThanRaw 8 v 14) || v == 32) = true ∨
         field_len = value_index_val + value_len + 1 )) )
:= by
  unfold checkCharAfterValue
  step mkF.convertsM as one
  step mkAdd.convertsM h_vi h_vl as viPlusVl
  have hSel := selectArrayValue.convertsM h_viPlusVl h_field_val h_maxKV
  have h_one' := converts_skip hSel h_one
  have h_fl' := converts_skip hSel h_fl
  have h_vi' := converts_skip hSel h_vi
  have h_vl' := converts_skip hSel h_vl
  apply convertsM_of_convertsM
    (convertsM_bind_and hSel
      (checkCharAfterValue.tail_convertsM hSel.result h_one' h_fl' h_vi' h_vl'))
  · rfl
  · simp only [true_implies]

/-- Opaque names for the three zone computations, so the combined proof in `zones_convertsM`
reasons about fixed function applications (trivially equal to themselves) rather than inlined
nested `do`-blocks (requiring expensive `whnf` unfolding to confirm two mentions of "the state
after zone X" agree). This is the same wall `docs/proving-circuits.md` describes for
`Base64Len/base64UrlLookup.lean`; wrapping each piece as its own named `def` (as
`parseJWTFieldSharedLogic.lean`'s `checkIndexOrdering` etc. already do) is the fix. -/
private def zoneADef (maxKVPairLen : ℕ) (nameLen two colonIndex : F bn254) :
    ClapM bn254 (FArray bn254 maxKVPairLen) := do
  let s ← mkAdd nameLen two
  arraySelectorComplex maxKVPairLen s colonIndex

private def zoneBDef (maxKVPairLen : ℕ) (one colonIndex valueIndex : F bn254) :
    ClapM bn254 (FArray bn254 maxKVPairLen) := do
  let s ← mkAdd colonIndex one
  let e ← mkSub valueIndex one
  arraySelectorComplex maxKVPairLen s e

private def zoneCDef (maxKVPairLen : ℕ) (one valueIndex valueLen fieldLen : F bn254) :
    ClapM bn254 (FArray bn254 maxKVPairLen) := do
  let t ← mkAdd valueIndex valueLen
  let s ← mkAdd t one
  let e ← mkSub fieldLen one
  arraySelectorComplex maxKVPairLen s e

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

/-- Zone B construction: `arraySelectorComplex maxKVPairLen (colonIndex+one) (valueIndex-one)`,
given the shared `one`. -/
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
        decide (i.val < (value_index_val - 1).val)))
    (0 < (colon_index_val + 1).val ∧ (colon_index_val + 1).val ≤ maxKVPairLen ∧
      (value_index_val - 1).val < maxKVPairLen)
:= by
  unfold zoneBDef
  step mkAdd.convertsM h_ci h_one as s
  step mkSub.convertsM h_vi h_one as e
  apply convertsM_of_convertsM (arraySelectorComplex.convertsM h_s h_e h_maxKV) rfl
  simp only [true_implies]

/-- Zone C construction: `arraySelectorComplex maxKVPairLen ((valueIndex+valueLen)+one)
(fieldLen-one)`, given the shared `one`. -/
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
      decide (0 < (value_index_val + value_len + 1).val ∧ (value_index_val + value_len + 1).val ≤ i.val) &&
        decide (i.val < (field_len - 1).val)))
    (0 < (value_index_val + value_len + 1).val ∧ (value_index_val + value_len + 1).val ≤ maxKVPairLen ∧
      (field_len - 1).val < maxKVPairLen)
:= by
  unfold zoneCDef
  step mkAdd.convertsM h_vi h_vl as t
  step mkAdd.convertsM h_t h_one as s
  step mkSub.convertsM h_fl h_one as e
  apply convertsM_of_convertsM (arraySelectorComplex.convertsM h_s h_e h_maxKV) rfl
  simp only [true_implies]

/-- Zone C's computation plus the two `zipWithM` merges, taking zone A's and zone B's pointwise
facts as given. Proved as its own lemma (not inlined into `zones_convertsM`'s tactic chain) so its
target constraint is concrete from the start: `step`ing a real-constraint action against a goal
whose own constraint slot is still an unresolved metavariable (as it would be mid-way through
`zones_convertsM`'s outer `convertsM_bind_and` chain) is what caused the `whnf` blowup here. -/
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
      (decide (0 < (value_index_val + value_len + 1).val ∧
          (value_index_val + value_len + 1).val ≤ i.val) && decide (i.val < (field_len - 1).val))))
    (0 < (value_index_val + value_len + 1).val ∧ (value_index_val + value_len + 1).val ≤ maxKVPairLen ∧
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

/-- The whole zone-construction prefix of `checkWhitespaceZones`, also wrapped as its own opaque
name: `checkWhitespaceZones` itself calls this (rather than inlining the five steps) so that its
own `convertsM` proof can combine `zones_convertsM`'s fact with the `foldlM` part via a single
top-level bind, matching this symbol syntactically — never needing `bind_assoc` to re-associate a
right-nested `do`-block, which (confirmed experimentally) `simp` cannot do predictably at this
depth without producing a differently-shaped term that is no longer `hZones`-shaped. -/
private def inZoneDef (maxKVPairLen : ℕ) (nameLen colonIndex valueIndex valueLen fieldLen : F bn254) :
    ClapM bn254 (FArray bn254 maxKVPairLen) := do
  let one ← mkF 1
  let two ← mkF 2
  let zoneA ← zoneADef maxKVPairLen nameLen two colonIndex
  let zoneB ← zoneBDef maxKVPairLen one colonIndex valueIndex
  let zoneC ← zoneCDef maxKVPairLen one valueIndex valueLen fieldLen
  let inZoneAB ← zoneA.zipWithM FB.or zoneB
  inZoneAB.zipWithM FB.or zoneC

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
        decide (i.val < (value_index_val - 1).val)) ||
      (decide (0 < (value_index_val + value_len + 1).val ∧
          (value_index_val + value_len + 1).val ≤ i.val) && decide (i.val < (field_len - 1).val))))
    ( (0 < (name_len + 2).val ∧ (name_len + 2).val ≤ maxKVPairLen ∧ colon_index_val.val < maxKVPairLen) ∧
      (0 < (colon_index_val + 1).val ∧ (colon_index_val + 1).val ≤ maxKVPairLen ∧
        (value_index_val - 1).val < maxKVPairLen) ∧
      (0 < (value_index_val + value_len + 1).val ∧ (value_index_val + value_len + 1).val ≤ maxKVPairLen ∧
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

/-- The `foldlM` step: whitespace-or-not for one position, given its `and`-selector bit `z` and
field character `c` as *general* field elements (not necessarily typed bits/bytes) — the
combinator's per-element hypothesis has no room to carry a per-index byte-range fact, so this uses
`F8.isWhitespace`'s *unchecked* form and `FB.and`'s underlying `mkMul` directly, matching how
`checkCharBeforeValue`'s tail handles its own "not actually known to be a bit" product. -/
private lemma whitespaceCheck_convertsM
  {state : ClapMState bn254} {z c : F bn254} {z_val c_val : ZMod bn254}
  (h_z : Converts F.conversion state z z_val)
  (h_c : Converts F.conversion state c c_val)
:
  ConvertsM FUnit.conversion
    (F8.isWhitespace c >>= fun ws => not ws >>= fun notws => FB.and z notws >>= fun prod => eq0 prod)
    state ()
    ( (lessThan.lessThanOk 8 8 c_val ∧ lessThan.lessThanOk 8 c_val 14) ∧
      z_val * (if ((lessThan.lessThanRaw 8 8 c_val && lessThan.lessThanRaw 8 c_val 14) ||
        c_val == 32) then (0:ZMod bn254) else 1) = 0 )
:= by
  have hWs := F8.isWhitespace.convertsM_unchecked h_c
  replace h_z := converts_skip hWs h_z
  apply convertsM_bind_and hWs
  refine convertsM_bind (not.convertsM hWs.result) ?_ (fun _ => trivial)
  have hNot := not.convertsM hWs.result
  replace h_z := converts_skip hNot h_z
  unfold FB.and
  rw [mul_def]
  refine convertsM_bind (mkMul.convertsM h_z (F.converts_of_FB_converts hNot.result)) ?_ (fun _ => trivial)
  apply convertsM_of_convertsM
    (eq0.convertsM (mkMul.convertsM h_z (F.converts_of_FB_converts hNot.result)).result)
  · rfl
  · by_cases h : (lessThan.lessThanRaw 8 8 c_val && lessThan.lessThanRaw 8 c_val 14) || c_val == 32 <;>
      simp [h]

/-- Every position in the three "gap" zones (between name/colon, colon/value, value/terminator)
must be whitespace. -/
private def checkWhitespaceZones {maxKVPairLen : ℕ}
    (field_data : FVec bn254 maxKVPairLen)
    (nameLen colonIndex valueIndex valueLen fieldLen : F bn254) : ClapM bn254 Unit := do
  let inZone ← inZoneDef maxKVPairLen nameLen colonIndex valueIndex valueLen fieldLen
  (inZone.zip field_data).foldlM (b := ()) fun _ (z, c) ↦ do
    let ws ← F8.isWhitespace c
    eq0 (← z.and (← not ws))

lemma checkWhitespaceZones.convertsM
  {maxKVPairLen : ℕ} {state : ClapMState bn254}
  {field_data : FVec bn254 maxKVPairLen}
  {nameLen colonIndex valueIndex valueLen fieldLen : F bn254}
  {field_vals : Vector (ZMod bn254) maxKVPairLen}
  {name_len colon_index_val value_index_val value_len field_len : ZMod bn254}
  (h_field_val : Converts FVec.conversion state field_data field_vals)
  (h_nl : Converts F.conversion state nameLen name_len)
  (h_ci : Converts F.conversion state colonIndex colon_index_val)
  (h_vi : Converts F.conversion state valueIndex value_index_val)
  (h_vl : Converts F.conversion state valueLen value_len)
  (h_fl : Converts F.conversion state fieldLen field_len)
  (h_maxKV : maxKVPairLen < bn254)
:
  ConvertsM FUnit.conversion
    (checkWhitespaceZones field_data nameLen colonIndex valueIndex valueLen fieldLen)
    state ()
    ( ( (0 < (name_len + 2).val ∧ (name_len + 2).val ≤ maxKVPairLen ∧ colon_index_val.val < maxKVPairLen) ∧
        (0 < (colon_index_val + 1).val ∧ (colon_index_val + 1).val ≤ maxKVPairLen ∧
          (value_index_val - 1).val < maxKVPairLen) ∧
        (0 < (value_index_val + value_len + 1).val ∧ (value_index_val + value_len + 1).val ≤ maxKVPairLen ∧
          (field_len - 1).val < maxKVPairLen) ) ∧
      (∀ i : Fin maxKVPairLen,
        (lessThan.lessThanOk 8 8 field_vals[i] ∧ lessThan.lessThanOk 8 field_vals[i] 14) ∧
        (if ((decide (0 < (name_len + 2).val ∧ (name_len + 2).val ≤ i.val) &&
                decide (i.val < colon_index_val.val)) ||
             (decide (0 < (colon_index_val + 1).val ∧ (colon_index_val + 1).val ≤ i.val) &&
                decide (i.val < (value_index_val - 1).val)) ||
             (decide (0 < (value_index_val + value_len + 1).val ∧
                  (value_index_val + value_len + 1).val ≤ i.val) &&
                decide (i.val < (field_len - 1).val)))
           then (1 : ZMod bn254) else 0) *
          (if ((lessThan.lessThanRaw 8 8 field_vals[i] && lessThan.lessThanRaw 8 field_vals[i] 14) ||
                field_vals[i] == 32) then (0 : ZMod bn254) else 1) = 0) )
:= by
  unfold checkWhitespaceZones
  have hZones := zones_convertsM h_nl h_ci h_vi h_vl h_fl h_maxKV
  have h_field_val' := converts_skip hZones h_field_val
  apply convertsM_bind_and hZones
  have h_inZoneF := FVec.converts_of_FArray_converts hZones.result
  have h_pair := fun i : Fin maxKVPairLen => FVec.converts_zip h_inZoneF h_field_val' i.isLt
  apply convertsM_of_convertsM
    (convertsM_foldlM_constraints (C_acc := FUnit.conversion) (init_val := ())
      (f_spec := fun (_ : Unit) (_ : ZMod bn254 × ZMod bn254) => ())
      (step_constraints := fun xv : ZMod bn254 × ZMod bn254 =>
        (lessThan.lessThanOk 8 8 xv.2 ∧ lessThan.lessThanOk 8 xv.2 14) ∧
        xv.1 * (if ((lessThan.lessThanRaw 8 8 xv.2 && lessThan.lessThanRaw 8 xv.2 14) ||
          xv.2 == 32) then (0 : ZMod bn254) else 1) = 0)
      h_pair FUnit.converts
      (fun h_acc h_x => whitespaceCheck_convertsM (FPair.converts_fst h_x) (FPair.converts_snd h_x)))
  · rfl
  · have h_xv : ∀ i : Fin maxKVPairLen,
        (((Vector.ofFn (fun i : Fin maxKVPairLen =>
            (decide (0 < (name_len + 2).val ∧ (name_len + 2).val ≤ i.val) &&
                decide (i.val < colon_index_val.val)) ||
            (decide (0 < (colon_index_val + 1).val ∧ (colon_index_val + 1).val ≤ i.val) &&
                decide (i.val < (value_index_val - 1).val)) ||
            (decide (0 < (value_index_val + value_len + 1).val ∧
                  (value_index_val + value_len + 1).val ≤ i.val) &&
                decide (i.val < (field_len - 1).val)))).map
          (fun b => if b then (1 : ZMod bn254) else 0)).zip field_vals)[i]
          = (if ((decide (0 < (name_len + 2).val ∧ (name_len + 2).val ≤ i.val) &&
                    decide (i.val < colon_index_val.val)) ||
                 (decide (0 < (colon_index_val + 1).val ∧ (colon_index_val + 1).val ≤ i.val) &&
                    decide (i.val < (value_index_val - 1).val)) ||
                 (decide (0 < (value_index_val + value_len + 1).val ∧
                      (value_index_val + value_len + 1).val ≤ i.val) &&
                    decide (i.val < (field_len - 1).val)))
               then (1 : ZMod bn254) else 0, field_vals[i]) := by
      intro i
      simp [Vector.getElem_zip, Vector.getElem_ofFn]
    constructor
    · intro h i; have hi := h i; rw [h_xv i] at hi; exact hi
    · intro h i; rw [h_xv i]; exact h i

def parseEmailVerifiedField
  {maxKVPairLen maxNameLen maxValueLen : ℕ}
  (h_name_len  : maxNameLen  ≤ maxKVPairLen)
  (h_value_len : maxValueLen ≤ maxKVPairLen)
  (field       : FString bn254 maxKVPairLen)
  (name        : FString bn254 maxNameLen)
  (value       : FString bn254 maxValueLen)
  (colonIndex : F bn254)
  (valueIndex : F bn254)
  : ClapM bn254 Unit
:= do
  -- Delegate shared structural checks
  let f ← FB.ofBool false
  parseJWTFieldSharedLogic (skipChecks := f) h_name_len h_value_len field name
    value
    colonIndex
    valueIndex
  let beforeIsQuote ← checkCharBeforeValue field.data colonIndex valueIndex
  let afterIsQuote ← checkCharAfterValue field.data value.len field.len valueIndex
  -- No mismatched quotes
  assert_eq beforeIsQuote afterIsQuote
  checkWhitespaceZones field.data name.len colonIndex valueIndex value.len field.len

namespace parseEmailVerifiedField

open Poseidon RandomOracle Primes FiatShamir

open FString

def parses (H : HashFn) {maxKVPairLen maxNameLen maxValueLen : ℕ}
  (field_vals : Vector (ZMod bn254) maxKVPairLen)
  (field_len : ZMod bn254)
  (name_vals : Vector (ZMod bn254) maxNameLen)
  (name_len : ZMod bn254)
  (value_vals : Vector (ZMod bn254) maxValueLen)
  (value_len : ZMod bn254)
  (colon_index_val value_index_val : ZMod bn254) :
  Prop
:=
  let charBeforeValue := field_vals.getD (value_index_val - 1).val 0 |>.val
  let charAfterValue := field_vals.getD (value_index_val + value_len).val 0 |>.val
  parseJWTFieldSharedLogic.parses H field_vals field_len name_vals name_len
    value_vals
    value_len
    colon_index_val
    value_index_val
    false
  ∧
  (charBeforeValue = /- quotes -/ 34 ∨ isWs charBeforeValue ∨
    value_index_val = colon_index_val + 1
  ) ∧
  (charAfterValue = /- quotes -/ 34 ∨ isWs charAfterValue ∨
    field_len = value_index_val + value_len + 1
  ) ∧
  ((charBeforeValue == 34) = (charAfterValue == 34)) ∧
  ∀ i : Fin maxKVPairLen,
    ((name_len + 2).val ≤ i.val ∧ i.val < colon_index_val.val) ∨
    (colon_index_val.val + 1 ≤ i.val ∧ i.val < (value_index_val - 1).val) ∨
    ((value_index_val + value_len).val + 1 ≤ i.val ∧ i.val < (field_len - 1).val) →
    isWs field_vals[i].val

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
  {field       : FString bn254 maxKVPairLen}
  {name        : FString bn254 maxNameLen}
  {value       : FString bn254 maxValueLen}
  {colon_index : F bn254}
  {value_index : F bn254}
  -- Ideal values
  {field_vals : Vector (ZMod bn254) maxKVPairLen}
  {field_len : ZMod bn254}
  {name_vals : Vector (ZMod bn254) maxNameLen}
  {name_len : ZMod bn254}
  {value_vals : Vector (ZMod bn254) maxValueLen}
  {value_len : ZMod bn254}
  {colon_index_val value_index_val : ZMod bn254}
  -- Conversion hypotheses
  (h_field_val : Converts FVec.conversion state field.data field_vals)
  (h_field_len : Converts F.conversion state field.len field_len)
  (h_name_val : Converts FVec.conversion state name.data name_vals)
  (h_name_len : Converts F.conversion state name.len name_len)
  (h_value_val : Converts FVec.conversion state value.data value_vals)
  (h_value_len : Converts F.conversion state value.len value_len)
  (h_ci : Converts F.conversion state colon_index colon_index_val)
  (h_vi : Converts F.conversion state value_index value_index_val)
  -- Range bounds (`w := 20` is hard-coded in the body)
  (h_name_len_w : name_len.val < 2 ^ 20)
  (h_colon_index_w : colon_index_val.val < 2 ^ 20)
  (h_value_index_w : value_index_val.val < 2 ^ 20)
  (h_field_len_w : field_len.val < 2 ^ 20)
  (h_sum_len_w : (name_len + value_len).val < 2 ^ 20)
  :
  ConvertsM FUnit.conversion
    (parseEmailVerifiedField h_name_len_lt h_value_len_lt field name value
      colon_index
      value_index
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
      (value_index_val + value_len).val < maxKVPairLen ∧
      -- /- redundant -/ value_index_val.val < maxKVPairLen ∧
      value_index_val.val < (value_index_val + value_len).val ∧
      0 < value_len.val ∧

      parses H field_vals field_len name_vals name_len value_vals value_len
        colon_index_val
        value_index_val
    )
:= by
  have h_maxKV : maxKVPairLen < bn254 := by
    have h1953 : (1953:ℕ) < bn254 := by decide
    omega
  unfold parseEmailVerifiedField
  step (FB.ofBool.convertsM (p := bn254)) as f
  simp only [true_implies]
  refine convertsM_of_convertsM
    (constraints1 :=
      ( (∀ i : Fin maxKVPairLen, field_vals[i].val < 2 ^ 8) ∧
        (∀ i : Fin maxNameLen, name_vals[i].val < 2 ^ 8) ∧
        (∀ i : Fin maxValueLen, value_vals[i].val < 2 ^ 8) ∧
        name_len.val + 1 < maxKVPairLen ∧
        colon_index_val.val < maxKVPairLen ∧
        (field_len - 1).val < maxKVPairLen ∧
        0 < name_len.val ∧
        (value_index_val + value_len).val < 2 ^ minBits' maxKVPairLen ∧
        value_index_val.val < maxKVPairLen ∧
        value_index_val.val < (value_index_val + value_len).val ∧
        0 < value_len.val ∧
        parseJWTFieldSharedLogic.parses H field_vals field_len name_vals name_len value_vals value_len
          colon_index_val value_index_val false ) ∧
      ( (value_index_val - 1).val < maxKVPairLen ∧
        (let v := field_vals.getD (value_index_val - 1).val 0
         (lessThan.lessThanOk 8 8 v ∧ lessThan.lessThanOk 8 v 14) ∧
         ( v.val = 34 ∨
           ((lessThan.lessThanRaw 8 8 v && lessThan.lessThanRaw 8 v 14) || v == 32) = true ∨
           value_index_val - 1 = colon_index_val )) ) ∧
      ( (value_index_val + value_len).val < maxKVPairLen ∧
        (let v := field_vals.getD (value_index_val + value_len).val 0
         (lessThan.lessThanOk 8 8 v ∧ lessThan.lessThanOk 8 v 14) ∧
         ( v.val = 34 ∨
           ((lessThan.lessThanRaw 8 8 v && lessThan.lessThanRaw 8 v 14) || v == 32) = true ∨
           field_len = value_index_val + value_len + 1 )) ) ∧
      ( (if (field_vals.getD (value_index_val - 1).val 0 == (34 : ZMod bn254)) then (1 : ZMod bn254) else 0) =
        (if (field_vals.getD (value_index_val + value_len).val 0 == (34 : ZMod bn254)) then (1 : ZMod bn254) else 0) ) ∧
      ( ( (0 < (name_len + 2).val ∧ (name_len + 2).val ≤ maxKVPairLen ∧ colon_index_val.val < maxKVPairLen) ∧
          (0 < (colon_index_val + 1).val ∧ (colon_index_val + 1).val ≤ maxKVPairLen ∧
            (value_index_val - 1).val < maxKVPairLen) ∧
          (0 < (value_index_val + value_len + 1).val ∧ (value_index_val + value_len + 1).val ≤ maxKVPairLen ∧
            (field_len - 1).val < maxKVPairLen) ) ∧
        (∀ i : Fin maxKVPairLen,
          (lessThan.lessThanOk 8 8 field_vals[i] ∧ lessThan.lessThanOk 8 field_vals[i] 14) ∧
          (if ((decide (0 < (name_len + 2).val ∧ (name_len + 2).val ≤ i.val) &&
                  decide (i.val < colon_index_val.val)) ||
               (decide (0 < (colon_index_val + 1).val ∧ (colon_index_val + 1).val ≤ i.val) &&
                  decide (i.val < (value_index_val - 1).val)) ||
               (decide (0 < (value_index_val + value_len + 1).val ∧
                    (value_index_val + value_len + 1).val ≤ i.val) &&
                  decide (i.val < (field_len - 1).val)))
             then (1 : ZMod bn254) else 0) *
            (if ((lessThan.lessThanRaw 8 8 field_vals[i] && lessThan.lessThanRaw 8 field_vals[i] 14) ||
                  field_vals[i] == 32) then (0 : ZMod bn254) else 1) = 0) ) )
    ?_ rfl ?hiff
  have hSL := parseJWTFieldSharedLogic.convertsM h_H h_name_len_lt h_value_len_lt h_len_bound
    h_field_val h_field_len h_name_val h_name_len h_value_val h_value_len h_ci h_vi h_f
    h_name_len_w h_colon_index_w h_value_index_w h_field_len_w h_sum_len_w
  replace h_field_val := converts_skip hSL h_field_val
  replace h_name_len := converts_skip hSL h_name_len
  replace h_ci := converts_skip hSL h_ci
  replace h_vi := converts_skip hSL h_vi
  replace h_value_len := converts_skip hSL h_value_len
  replace h_field_len := converts_skip hSL h_field_len
  apply convertsM_bind_and hSL
  have hBefore := checkCharBeforeValue.convertsM h_field_val h_ci h_vi h_maxKV
  replace h_field_val := converts_skip hBefore h_field_val
  replace h_name_len := converts_skip hBefore h_name_len
  replace h_ci := converts_skip hBefore h_ci
  replace h_vi := converts_skip hBefore h_vi
  replace h_value_len := converts_skip hBefore h_value_len
  replace h_field_len := converts_skip hBefore h_field_len
  apply convertsM_bind_and hBefore
  have hAfter := checkCharAfterValue.convertsM h_field_val h_value_len h_field_len h_vi h_maxKV
  have hBeforeR := converts_skip hAfter hBefore.result
  replace h_field_val := converts_skip hAfter h_field_val
  replace h_name_len := converts_skip hAfter h_name_len
  replace h_ci := converts_skip hAfter h_ci
  replace h_vi := converts_skip hAfter h_vi
  replace h_value_len := converts_skip hAfter h_value_len
  replace h_field_len := converts_skip hAfter h_field_len
  apply convertsM_bind_and hAfter
  have hAssertEq := assert_eq.convertsM (F.converts_of_FB_converts hBeforeR)
    (F.converts_of_FB_converts hAfter.result)
  replace h_field_val := converts_skip hAssertEq h_field_val
  replace h_name_len := converts_skip hAssertEq h_name_len
  replace h_ci := converts_skip hAssertEq h_ci
  replace h_vi := converts_skip hAssertEq h_vi
  replace h_value_len := converts_skip hAssertEq h_value_len
  replace h_field_len := converts_skip hAssertEq h_field_len
  apply convertsM_bind_and hAssertEq
  exact checkWhitespaceZones.convertsM h_field_val h_name_len h_ci h_vi h_value_len h_field_len h_maxKV
  · have hv_b8 : ∀ (h_byte_f : ∀ i : Fin maxKVPairLen, field_vals[i].val < 2 ^ 8),
        (field_vals.getD (value_index_val - 1).val 0).val < 2 ^ 8 :=
      fun h_byte_f => getD_byte_bound h_byte_f _
    have hv_a8 : ∀ (h_byte_f : ∀ i : Fin maxKVPairLen, field_vals[i].val < 2 ^ 8),
        (field_vals.getD (value_index_val + value_len).val 0).val < 2 ^ 8 :=
      fun h_byte_f => getD_byte_bound h_byte_f _
    have h_vsub_add : value_index_val - 1 = colon_index_val ↔ value_index_val = colon_index_val + 1 :=
      sub_eq_iff_eq_add
    have h_bool_eq : ∀ a b : Bool,
        (if a then (1 : ZMod bn254) else 0) = (if b then (1 : ZMod bn254) else 0) ↔ a = b := by
      intro a b
      cases a <;> cases b <;> simp
    have h_beq34 : ∀ v : ZMod bn254, (v == (34 : ZMod bn254)) = (v.val == 34) := by
      intro v
      have h34v : (34 : ZMod bn254).val = 34 := by decide
      by_cases h : v.val = 34
      · have hv : v = 34 := ZMod.val_injective bn254 (by rw [h34v]; exact h)
        simp [hv, h34v]
      · have hne : v ≠ 34 := fun hc => h (by rw [hc, h34v])
        simp [hne, h]
    constructor
    · rintro ⟨⟨hSL_byte_f, hSL_byte_n, hSL_byte_v, hSL_nl1, hSL_ci, hSL_fl1, hSL_nlpos, hSL_vvbound,
        hSL_vimax, hSL_vivl, hSL_vlpos, hSL_parses⟩,
        ⟨hB_idx, hB_ltok, hB_disj⟩, ⟨hA_idx, hA_ltok, hA_disj⟩, hAssertEq', ⟨⟨hZA, hZB, hZC⟩, hZpw⟩⟩
      refine ⟨hSL_byte_f, hSL_byte_n, hSL_byte_v, hSL_nl1, hSL_ci, hSL_fl1, hSL_nlpos, hA_idx,
        hSL_vivl, hSL_vlpos, hSL_parses, ?_, ?_, ?_, ?_⟩
      · rcases hB_disj with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl (by rw [← lessThanRaw_isWs_eq (hv_b8 hSL_byte_f)]; simpa using h))
        · exact Or.inr (Or.inr (h_vsub_add.mp h))
      · rcases hA_disj with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl (by rw [← lessThanRaw_isWs_eq (hv_a8 hSL_byte_f)]; simpa using h))
        · exact Or.inr (Or.inr h)
      · have hbe := (h_bool_eq _ _).mp hAssertEq'
        simpa [h_beq34] using hbe
      · intro i hranges
        obtain ⟨_, hmul⟩ := hZpw i
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
        have h_vivl1 : (value_index_val + value_len + 1).val = value_index_val.val + value_len.val + 1 := by
          have hlt : (value_index_val + value_len).val + (1 : ZMod bn254).val < bn254 := by
            rw [h_vv, h1v]; omega
          rw [ZMod.val_add_of_lt hlt, h_vv, h1v]
        have hzone_true :
            ((decide (0 < (name_len + 2).val ∧ (name_len + 2).val ≤ i.val) &&
                  decide (i.val < colon_index_val.val)) ||
              (decide (0 < (colon_index_val + 1).val ∧ (colon_index_val + 1).val ≤ i.val) &&
                  decide (i.val < (value_index_val - 1).val)) ||
              (decide (0 < (value_index_val + value_len + 1).val ∧
                    (value_index_val + value_len + 1).val ≤ i.val) &&
                  decide (i.val < (field_len - 1).val))) = true := by
          simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
          rcases hranges with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inl (Or.inl ⟨⟨by omega, by omega⟩, h2⟩)
          · exact Or.inl (Or.inr ⟨⟨by omega, by omega⟩, h2⟩)
          · exact Or.inr ⟨⟨by omega, by omega⟩, h2⟩
        rw [hzone_true] at hmul
        simp only [if_true, one_mul] at hmul
        by_contra hws
        have hraw : ((lessThan.lessThanRaw 8 8 field_vals[i] && lessThan.lessThanRaw 8 field_vals[i] 14) ||
            field_vals[i] == 32) = false := by
          rw [lessThanRaw_isWs_eq (hSL_byte_f i)]
          simpa using hws
        rw [hraw] at hmul
        simp at hmul
    · rintro ⟨hT_byte_f, hT_byte_n, hT_byte_v, hT_nl1, hT_ci, hT_fl1, hT_nlpos, hT_vvbound, hT_vivl,
        hT_vlpos, hSL_parses, hT_before, hT_after, hT_booleq, hT_zonefa⟩
      have h1v : (1 : ZMod bn254).val = 1 := by decide
      have hSL_body := hSL_parses (by decide)
      obtain ⟨hno1, hno2, hno3, -⟩ := hSL_body
      have h_vm1 : (value_index_val - 1).val = value_index_val.val - 1 :=
        ZMod.val_sub (by rw [h1v]; omega)
      have h_vimax : value_index_val.val < maxKVPairLen := by omega
      have hA_idx : (value_index_val + value_len).val < 2 ^ minBits' maxKVPairLen :=
        minBits_lt hT_vvbound
      refine ⟨⟨hT_byte_f, hT_byte_n, hT_byte_v, hT_nl1, hT_ci, hT_fl1, hT_nlpos, hA_idx, h_vimax,
          hT_vivl, hT_vlpos, hSL_parses⟩, ?_, ?_, ?_, ?_⟩
      · refine ⟨by omega, ⟨?_, ?_⟩, ?_⟩
        · exact lessThan.lessThanOk_of (show (8 : ZMod bn254).val < 2 ^ 8 by decide) (hv_b8 hT_byte_f)
            (by decide)
        · exact lessThan.lessThanOk_of (hv_b8 hT_byte_f) (show (14 : ZMod bn254).val < 2 ^ 8 by decide)
            (by decide)
        · rcases hT_before with h | h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl (by rw [lessThanRaw_isWs_eq (hv_b8 hT_byte_f)]; simpa using h))
          · exact Or.inr (Or.inr (h_vsub_add.mpr h))
      · refine ⟨hT_vvbound, ⟨?_, ?_⟩, ?_⟩
        · exact lessThan.lessThanOk_of (show (8 : ZMod bn254).val < 2 ^ 8 by decide) (hv_a8 hT_byte_f)
            (by decide)
        · exact lessThan.lessThanOk_of (hv_a8 hT_byte_f) (show (14 : ZMod bn254).val < 2 ^ 8 by decide)
            (by decide)
        · rcases hT_after with h | h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl (by rw [lessThanRaw_isWs_eq (hv_a8 hT_byte_f)]; simpa using h))
          · exact Or.inr (Or.inr h)
      · apply (h_bool_eq _ _).mpr
        have hbe : (field_vals.getD (value_index_val - 1).val 0 == (34 : ZMod bn254)) =
            (field_vals.getD (value_index_val + value_len).val 0 == (34 : ZMod bn254)) := by
          simpa [h_beq34] using hT_booleq
        exact hbe
      · have h2v : (2 : ZMod bn254).val = 2 := by decide
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
        have h_vivl1 : (value_index_val + value_len + 1).val = value_index_val.val + value_len.val + 1 := by
          have hlt : (value_index_val + value_len).val + (1 : ZMod bn254).val < bn254 := by
            rw [h_vv, h1v]; omega
          rw [ZMod.val_add_of_lt hlt, h_vv, h1v]
        refine ⟨⟨⟨by omega, by omega, hT_ci⟩, ⟨by omega, by omega, by rw [h_vm1]; omega⟩,
          ⟨by omega, by omega, hT_fl1⟩⟩, ?_⟩
        intro i
        have hltok : lessThan.lessThanOk 8 8 field_vals[i] ∧ lessThan.lessThanOk 8 field_vals[i] 14 :=
          ⟨lessThan.lessThanOk_of (show (8 : ZMod bn254).val < 2 ^ 8 by decide) (hT_byte_f i) (by decide),
            lessThan.lessThanOk_of (hT_byte_f i) (show (14 : ZMod bn254).val < 2 ^ 8 by decide) (by decide)⟩
        refine ⟨hltok, ?_⟩
        by_cases hzone :
            ((decide (0 < (name_len + 2).val ∧ (name_len + 2).val ≤ i.val) &&
                  decide (i.val < colon_index_val.val)) ||
              (decide (0 < (colon_index_val + 1).val ∧ (colon_index_val + 1).val ≤ i.val) &&
                  decide (i.val < (value_index_val - 1).val)) ||
              (decide (0 < (value_index_val + value_len + 1).val ∧
                    (value_index_val + value_len + 1).val ≤ i.val) &&
                  decide (i.val < (field_len - 1).val))) = true
        · have hranges_i :
              ((name_len + 2).val ≤ i.val ∧ i.val < colon_index_val.val) ∨
              (colon_index_val.val + 1 ≤ i.val ∧ i.val < (value_index_val - 1).val) ∨
              ((value_index_val + value_len).val + 1 ≤ i.val ∧ i.val < (field_len - 1).val) := by
            simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hzone
            rcases hzone with (⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩
            · exact Or.inl ⟨h1.2, h2⟩
            · exact Or.inr (Or.inl ⟨by omega, h2⟩)
            · exact Or.inr (Or.inr ⟨by omega, h2⟩)
          have hws_i := hT_zonefa i hranges_i
          rw [hzone]
          rw [lessThanRaw_isWs_eq (hT_byte_f i)]
          simpa using hws_i
        · simp only [Bool.not_eq_true] at hzone
          rw [hzone]
          simp

end parseEmailVerifiedField

end Clap.Lang
