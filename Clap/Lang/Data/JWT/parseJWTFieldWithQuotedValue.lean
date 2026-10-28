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

/-- JWT field with a quoted value (aud, uid, iss, nonce). -/
structure QuotedFieldInput (maxPairLen maxNameLen maxValueLen : ℕ) where
  field             : FString bn254 maxPairLen
  name              : FString bn254 maxNameLen
  value             : FString bn254 maxValueLen
  fieldStringBodies : PaddedVector (FB bn254) bn254 maxPairLen
  nameIndex         : F bn254
  colonIndex        : F bn254
  valueIndex        : F bn254

/-! ## Generic logic helpers

Copied verbatim from `parseJWTFieldWithUnquotedValue.lean` (per that file's own convention of
duplicating small per-file proof infrastructure rather than sharing it across JWT files — see its
doc comments). -/

private lemma forall_guard_comm {ι : Type} {g : Prop} {B : ι → Prop} :
    (∀ i, g → B i) ↔ (g → ∀ i, B i) :=
  ⟨fun h hg i => h i hg, fun h i hg => h hg i⟩

private lemma forall_and_guard_comm {ι : Type} {A : ι → Prop} {g : Prop} {B : ι → Prop} :
    (∀ i, A i ∧ (g → B i)) ↔ (∀ i, A i) ∧ (g → ∀ i, B i) :=
  ⟨fun h => ⟨fun i => (h i).1, fun hg i => (h i).2 hg⟩,
   fun h i => ⟨h.1 i, fun hg => h.2 hg i⟩⟩

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

/-- `convertsM_foldlM_constraints` for a step that also reads a fixed context `ctx` — same merge
of context-threading and real per-step constraints as `parseJWTFieldWithUnquotedValue.lean`'s copy
of this lemma. -/
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

private lemma xor_le_iff_interval {a b i : ℕ} (hab : a < b) :
    (decide (a ≤ i) ^^ decide (b ≤ i)) = true ↔ a ≤ i ∧ i < b := by
  by_cases hai : a ≤ i <;> by_cases hib : b ≤ i <;> simp [hai, hib] <;> omega

/-- Bridges a `List.getElem?` fact at a string position into a `Vector.getD` fact over `encodeV`.
Copied from `parseJWTFieldSharedLogic.lean`'s identical private lemma (not visible across files). -/
private lemma encodeV_getD_of_lt {w i : ℕ} {S : String} (hw : i < w) (hs : i < S.toList.length) :
    (FString.encodeV (p := bn254) w S).getD i 0 =
      (((S.toList.getD i default).toUInt8.toNat : ℕ) : ZMod bn254) := by
  rw [show (FString.encodeV (p := bn254) w S).getD i 0 =
      (FString.encodeV (p := bn254) w S)[i]'hw from by
    simp [Vector.getD, hw]]
  rw [FString.encodeV_getElem_of_lt hw hs, show S.toList[i]'hs = S.toList.getD i default from by
    simp [List.getD_eq_getElem?_getD, hs]]

/-- `F8.isWhitespace`'s *unchecked* raw value equals the plain-`ℕ` `isWs` predicate, given the byte
is known `< 2^8`. Copied from `parseJWTFieldWithUnquotedValue.lean`'s identical private lemma. -/
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
field character `c` as *general* field elements. Copied from `parseJWTFieldWithUnquotedValue.lean`. -/
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

/-- `mkF lit >>= fun c => guardedAssertEq perform x c`: when `perform`, asserts `x.val = lit`.
Copied from `parseJWTFieldSharedLogic.lean`'s identical private lemma. -/
private lemma assertEqLit_convertsM
  {state : ClapMState bn254} {x perform : F bn254} {lit : ZMod bn254}
  {x_val : ZMod bn254} {perform_val : Bool}
  (h_x : Converts F.conversion state x x_val)
  (h_perform : Converts FB.conversion state perform perform_val)
:
  ConvertsM FUnit.conversion
    (mkF lit >>= fun c => guardedAssertEq perform x c)
    state () (perform_val = true → x_val = lit)
:= by
  step mkF.convertsM as c
  apply convertsM_of_convertsM (guardedAssertEq.convertsM h_perform h_x h_c)
  · rfl
  · simp

/-- `action >>= fun _ => step`, generic in `step`. Copied from `parseJWTFieldSharedLogic.lean`. -/
private lemma seqUnit_convertsM
  {β : Type} {conversion2 : Conversion bn254 β}
  {action : ClapM bn254 Unit} {state : ClapMState bn254} {Cprev : Prop}
  (h_action : ConvertsM FUnit.conversion action state () Cprev)
  {step : ClapM bn254 β} {stepVal : conversion2.IdealT} {Cstep : Prop}
  (h_step : ConvertsM conversion2 step (action.getState state) stepVal Cstep)
:
  ConvertsM conversion2 (action >>= fun _ => step) state stepVal (Cprev ∧ Cstep)
:= convertsM_bind_and h_action h_step

/-! ## Value-quote checks

`field[value_index - 1] = '"'` and `field[value_index + value_len] = '"'`, the quotes around the
value. Wrapped in its own `private def` purely to keep `parseJWTFieldWithQuotedValue`'s own
top-level `do` block short — see `parseJWTFieldSharedLogic.lean`'s identical rationale for
`checkNameClosingQuote`/`checkLastCharDelimiter`. -/

private def checkValueQuotes {maxKVPairLen : ℕ}
  (field_data : FVec bn254 maxKVPairLen)
  (perform : FB bn254)
  (valueIndex valueLen : F bn254) :
  ClapM bn254 Unit
:= do
  let one ← mkF 1
  let valueFirstQuote ← selectArrayValue maxKVPairLen field_data (← valueIndex - one)
  guardedAssertEq perform valueFirstQuote (← mkF 34)
  let valueSecondQuote ← selectArrayValue maxKVPairLen field_data (← valueIndex + valueLen)
  guardedAssertEq perform valueSecondQuote (← mkF 34)

private lemma checkValueQuotes.convertsM
  {maxKVPairLen : ℕ} {state : ClapMState bn254}
  {field_data : FVec bn254 maxKVPairLen} {perform valueIndex valueLen : F bn254}
  {field_vals : Vector (ZMod bn254) maxKVPairLen} {perform_val : Bool}
  {value_index_val value_len : ZMod bn254}
  (h_field_val : Converts FVec.conversion state field_data field_vals)
  (h_perform : Converts FB.conversion state perform perform_val)
  (h_vi : Converts F.conversion state valueIndex value_index_val)
  (h_vl : Converts F.conversion state valueLen value_len)
  (h_maxKV : maxKVPairLen < bn254)
:
  ConvertsM FUnit.conversion
    (checkValueQuotes field_data perform valueIndex valueLen)
    state ()
    ( ( (value_index_val - 1).val < maxKVPairLen ∧
        (perform_val = true → field_vals.getD (value_index_val - 1).val 0 = 34) ) ∧
      ( (value_index_val + value_len).val < maxKVPairLen ∧
        (perform_val = true → field_vals.getD (value_index_val + value_len).val 0 = 34) ) )
:= by
  unfold checkValueQuotes
  step mkF.convertsM as one
  step mkSub.convertsM h_vi h_one as s1
  simp only [true_implies]
  have hSel1 := selectArrayValue.convertsM h_s1 h_field_val h_maxKV
  have hCheck1 := convertsM_bind_and (function := fun delimChar => mkF (34 : ZMod bn254) >>= fun c =>
      guardedAssertEq perform delimChar c)
    hSel1 (assertEqLit_convertsM (lit := (34 : ZMod bn254)) hSel1.result (converts_skip hSel1 h_perform))
  -- Abstract `hCheck1`'s action into an opaque local constant before reframing hypotheses
  -- through it: `converts_skip hCheck1 h` otherwise has to spell out
  -- `(selectArrayValue ... >>= fun delimChar => mkF 34 >>= ...).getState s1_state` afresh at
  -- every call, and the kernel pays to re-reduce that nested term each time — the same `whnf`
  -- wall as a concrete gadget's `getResult`/`getState` left as a term (see
  -- `docs/proving-circuits.md §Using a range established earlier`, last note).
  generalize hAct1 : (selectArrayValue maxKVPairLen field_data s1_result >>= fun delimChar =>
      mkF (34 : ZMod bn254) >>= fun c => guardedAssertEq perform delimChar c) = act1 at hCheck1
  replace h_field_val := converts_skip hCheck1 h_field_val
  replace h_perform := converts_skip hCheck1 h_perform
  replace h_vi := converts_skip hCheck1 h_vi
  replace h_vl := converts_skip hCheck1 h_vl
  -- `hS2` is built as a standalone term (not via `step`), since the live goal is not being
  -- consumed here — `hCheck1`/`hCheck2` are assembled independently and only combined at the end.
  have hS2 := mkAdd.convertsM h_vi h_vl
  have hSel2 := selectArrayValue.convertsM hS2.result (converts_skip hS2 h_field_val) h_maxKV
  have hCheck2Core := convertsM_bind_and (function := fun delimChar => mkF (34 : ZMod bn254) >>= fun c =>
      guardedAssertEq perform delimChar c)
    hSel2 (assertEqLit_convertsM (lit := (34 : ZMod bn254)) hSel2.result
      (converts_skip hSel2 (converts_skip hS2 h_perform)))
  have hCheck2 := convertsM_bind_and (function := fun s2 =>
      selectArrayValue maxKVPairLen field_data s2 >>= fun delimChar =>
        mkF (34 : ZMod bn254) >>= fun c => guardedAssertEq perform delimChar c)
    hS2 hCheck2Core
  have hcomb := seqUnit_convertsM hCheck1 hCheck2
  rw [← hAct1] at hcomb
  simp only [bind_assoc, true_and] at hcomb
  exact hcomb

/-! ## Zone construction (quoted boundaries)

Three "gap" zones must be whitespace: between the name's closing quote and the colon, between the
colon and the opening value-quote, and between the closing value-quote and the terminator. Unlike
`parseJWTFieldWithUnquotedValue.lean`'s sibling, there *is* an opening/closing quote around the
value to skip past, so zone B ends at `valueIndex - 1` (not `valueIndex`) and zone C starts at
`valueIndex + valueLen + 1` (not `valueIndex + valueLen`). Zone A's boundary is unaffected, so
`zoneADef`/`zoneA_convertsM` are copied unchanged. -/

private def zoneADef (maxKVPairLen : ℕ) (nameLen two colonIndex : F bn254) :
  ClapM bn254 (FArray bn254 maxKVPairLen)
:= do
  let s ← mkAdd nameLen two
  arraySelectorComplex maxKVPairLen s colonIndex

private def zoneBDef' (maxKVPairLen : ℕ) (one colonIndex valueIndex : F bn254) :
  ClapM bn254 (FArray bn254 maxKVPairLen)
:= do
  let s ← mkAdd colonIndex one
  let e ← mkSub valueIndex one
  arraySelectorComplex maxKVPairLen s e

private def zoneCDef' (maxKVPairLen : ℕ) (one valueIndex valueLen fieldLen : F bn254) :
  ClapM bn254 (FArray bn254 maxKVPairLen)
:= do
  let t ← mkAdd valueLen one
  let s ← mkAdd valueIndex t
  let e ← mkSub fieldLen one
  arraySelectorComplex maxKVPairLen s e

private def inZoneDef' (maxKVPairLen : ℕ)
  (nameLen colonIndex valueIndex valueLen fieldLen : F bn254) :
  ClapM bn254 (FArray bn254 maxKVPairLen)
:= do
  let one ← mkF 1
  let two ← mkF 2
  let zoneA ← zoneADef maxKVPairLen nameLen two colonIndex
  let zoneB ← zoneBDef' maxKVPairLen one colonIndex valueIndex
  let zoneC ← zoneCDef' maxKVPairLen one valueIndex valueLen fieldLen
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

private lemma zoneB_convertsM'
  {maxKVPairLen : ℕ} {state : ClapMState bn254}
  {one colonIndex valueIndex : F bn254} {colon_index_val value_index_val : ZMod bn254}
  (h_one : Converts F.conversion state one (1 : ZMod bn254))
  (h_ci : Converts F.conversion state colonIndex colon_index_val)
  (h_vi : Converts F.conversion state valueIndex value_index_val)
  (h_maxKV : maxKVPairLen < bn254)
:
  ConvertsM FArray.conversion
    (zoneBDef' maxKVPairLen one colonIndex valueIndex)
    state
    (Vector.ofFn (fun i : Fin maxKVPairLen =>
      decide (0 < (colon_index_val + 1).val ∧ (colon_index_val + 1).val ≤ i.val) &&
        decide (i.val < (value_index_val - 1).val)))
    (0 < (colon_index_val + 1).val ∧ (colon_index_val + 1).val ≤ maxKVPairLen ∧
      (value_index_val - 1).val < maxKVPairLen)
:= by
  unfold zoneBDef'
  step mkAdd.convertsM h_ci h_one as s
  step mkSub.convertsM h_vi h_one as e
  apply convertsM_of_convertsM (arraySelectorComplex.convertsM h_s h_e h_maxKV) rfl
  simp only [true_implies]

private lemma zoneC_convertsM'
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
    (zoneCDef' maxKVPairLen one valueIndex valueLen fieldLen)
    state
    (Vector.ofFn (fun i : Fin maxKVPairLen =>
      decide (0 < (value_index_val + (value_len + 1)).val ∧
          (value_index_val + (value_len + 1)).val ≤ i.val) &&
        decide (i.val < (field_len - 1).val)))
    (0 < (value_index_val + (value_len + 1)).val ∧
      (value_index_val + (value_len + 1)).val ≤ maxKVPairLen ∧
      (field_len - 1).val < maxKVPairLen)
:= by
  unfold zoneCDef'
  step mkAdd.convertsM h_vl h_one as t
  step mkAdd.convertsM h_vi h_t as s
  step mkSub.convertsM h_fl h_one as e
  apply convertsM_of_convertsM (arraySelectorComplex.convertsM h_s h_e h_maxKV) rfl
  simp only [true_implies]

private lemma zonesTail_convertsM'
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
    (zoneCDef' maxKVPairLen one valueIndex valueLen fieldLen >>= fun zoneC =>
      zoneA.zipWithM FB.or zoneB >>= fun inZoneAB =>
      inZoneAB.zipWithM FB.or zoneC)
    state
    (Vector.ofFn (fun i : Fin maxKVPairLen => zoneA_val[i] || zoneB_val[i] ||
      (decide (0 < (value_index_val + (value_len + 1)).val ∧
          (value_index_val + (value_len + 1)).val ≤ i.val) && decide (i.val < (field_len - 1).val))))
    (0 < (value_index_val + (value_len + 1)).val ∧
        (value_index_val + (value_len + 1)).val ≤ maxKVPairLen ∧
        (field_len - 1).val < maxKVPairLen)
:= by
  have hC := zoneC_convertsM' h_one h_vi h_vl h_fl h_maxKV
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

private lemma zones_convertsM'
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
    (inZoneDef' maxKVPairLen nameLen colonIndex valueIndex valueLen fieldLen)
    state
    (Vector.ofFn (fun i : Fin maxKVPairLen =>
      (decide (0 < (name_len + 2).val ∧ (name_len + 2).val ≤ i.val) && decide (i.val < colon_index_val.val)) ||
      (decide (0 < (colon_index_val + 1).val ∧ (colon_index_val + 1).val ≤ i.val) &&
        decide (i.val < (value_index_val - 1).val)) ||
      (decide (0 < (value_index_val + (value_len + 1)).val ∧
          (value_index_val + (value_len + 1)).val ≤ i.val) && decide (i.val < (field_len - 1).val))))
    ( (0 < (name_len + 2).val ∧ (name_len + 2).val ≤ maxKVPairLen ∧ colon_index_val.val < maxKVPairLen) ∧
      (0 < (colon_index_val + 1).val ∧ (colon_index_val + 1).val ≤ maxKVPairLen ∧
        (value_index_val - 1).val < maxKVPairLen) ∧
      (0 < (value_index_val + (value_len + 1)).val ∧
          (value_index_val + (value_len + 1)).val ≤ maxKVPairLen ∧
        (field_len - 1).val < maxKVPairLen) )
:= by
  unfold inZoneDef'
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
  have hB := zoneB_convertsM' h_one h_ci h_vi h_maxKV
  replace h_zoneA_pw := fun i ↦ converts_skip hB (h_zoneA_pw i)
  have h_zoneB_pw := FArray.converts_iff_FB_converts.mp hB.result
  replace h_vi := converts_skip hB h_vi
  replace h_vl := converts_skip hB h_vl
  replace h_fl := converts_skip hB h_fl
  replace h_one := converts_skip hB h_one
  apply convertsM_bind_and hB
  apply convertsM_of_convertsM (zonesTail_convertsM' h_zoneA_pw h_zoneB_pw h_one h_vi h_vl h_fl h_maxKV)
  · ext i
    simp [Vector.getElem_ofFn]
  · rfl

/-! ## Whitespace check over the quoted zones -/

private def checkWhitespaceZonesQuoted {maxKVPairLen : ℕ}
  (field_data : FVec bn254 maxKVPairLen)
  (perform : FB bn254)
  (nameLen colonIndex valueIndex valueLen fieldLen : F bn254) :
  ClapM bn254 Unit
:= do
  let inZone ← inZoneDef' maxKVPairLen nameLen colonIndex valueIndex valueLen fieldLen
  (inZone.zip field_data).foldlM (b := ()) fun _ (z, c) ↦ do
    let ws ← F8.isWhitespace c
    guardedEq0 perform (← z.and (← not ws))

private lemma checkWhitespaceZonesQuoted.convertsM
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
    (checkWhitespaceZonesQuoted field_data perform nameLen colonIndex valueIndex valueLen fieldLen)
    state ()
    ( ( (0 < (name_len + 2).val ∧ (name_len + 2).val ≤ maxKVPairLen ∧ colon_index_val.val < maxKVPairLen) ∧
        (0 < (colon_index_val + 1).val ∧ (colon_index_val + 1).val ≤ maxKVPairLen ∧
          (value_index_val - 1).val < maxKVPairLen) ∧
        (0 < (value_index_val + (value_len + 1)).val ∧
            (value_index_val + (value_len + 1)).val ≤ maxKVPairLen ∧
          (field_len - 1).val < maxKVPairLen) ) ∧
      (∀ i : Fin maxKVPairLen,
        lessThan.lessThanOk 8 8 field_vals[i] ∧ lessThan.lessThanOk 8 field_vals[i] 14) ∧
      (perform_val = true → ∀ i : Fin maxKVPairLen,
        (if ((decide (0 < (name_len + 2).val ∧ (name_len + 2).val ≤ i.val) &&
                decide (i.val < colon_index_val.val)) ||
             (decide (0 < (colon_index_val + 1).val ∧ (colon_index_val + 1).val ≤ i.val) &&
                decide (i.val < (value_index_val - 1).val)) ||
             (decide (0 < (value_index_val + (value_len + 1)).val ∧
                  (value_index_val + (value_len + 1)).val ≤ i.val) &&
                decide (i.val < (field_len - 1).val)))
           then (1 : ZMod bn254) else 0) *
          (if ((lessThan.lessThanRaw 8 8 field_vals[i] && lessThan.lessThanRaw 8 field_vals[i] 14) ||
                field_vals[i] == 32) then (0 : ZMod bn254) else 1) = 0) )
:= by
  unfold checkWhitespaceZonesQuoted
  have hZones := zones_convertsM' h_nl h_ci h_vi h_vl h_fl h_maxKV
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

/-! ## Name/value selector agreement with `fieldStringBodies`

No direct analogue in the unquoted sibling. `nameSel`/`valueSel` (via `arraySelector`, not
`arraySelectorComplex`) mark the name/value content positions; `fieldStringBodies` must agree with
their union exactly (an `↔`), expressed as two guarded `and`-of-negation checks per position. -/

-- A pairing conversion for two bit-valued (`FB`) positions, mirroring `FPair.conversion`
-- (`Clap/Model/Convert/Specialised.lean`) which only pairs `F`-valued (`ZMod`) positions.
private abbrev FBPair.conversion : Conversion bn254 (FB bn254 × FB bn254) where
  IdealT := Bool × Bool
  toExprs xy := [xy.1, xy.2]
  conversion xy := [if xy.1 then 1 else 0, if xy.2 then 1 else 0]

private lemma FBPair.converts_intro
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

private lemma FBPair.converts_fst
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

private lemma FBPair.converts_snd
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

private lemma FBPair.converts_zip
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
private lemma guardedAndNotEq0_convertsM
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
private lemma guardedNotAndEq0_convertsM
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
private lemma guardedStringBodyCheck_convertsM
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
  -- `checkValueQuotes.convertsM`'s `hAct1` — see its comment.
  generalize hAct1 : (not sb >>= fun nb => FB.and nv nb >>= fun prod => guardedEq0 perform prod) = act1
    at h1
  have h_perform' := converts_skip h1 h_perform
  have h_nv' := converts_skip h1 h_nv
  have h_sb' := converts_skip h1 h_sb
  have h2 := guardedNotAndEq0_convertsM h_perform' h_nv' (F.converts_of_FB_converts h_sb')
  have hcomb := seqUnit_convertsM h1 h2
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

private def checkStringBodies {maxKVPairLen : ℕ}
  (perform : FB bn254)
  (nameLen valueIndex valueLen : F bn254)
  (sb_data : FArray bn254 maxKVPairLen) :
  ClapM bn254 Unit
:= do
  let one ← mkF 1
  let nameSel ← arraySelector maxKVPairLen one (← nameLen + one)
  let valueSel ← arraySelector maxKVPairLen valueIndex (← valueIndex + valueLen)
  let nameOrValue ← nameSel.zipWithM FB.or valueSel
  (nameOrValue.zip sb_data).foldlM (b := ()) fun _ (nv, sb) ↦ do
    guardedEq0 perform (← nv.and (← not sb))
    guardedEq0 perform (← (← not nv).and sb)

private lemma checkStringBodies.convertsM
  {maxKVPairLen : ℕ} {state : ClapMState bn254}
  {perform nameLen valueIndex valueLen : F bn254}
  {sb_data : FArray bn254 maxKVPairLen}
  {perform_val : Bool} {name_len value_index_val value_len : ZMod bn254}
  {sb_vals : Vector Bool maxKVPairLen}
  (h_perform : Converts FB.conversion state perform perform_val)
  (h_nl : Converts F.conversion state nameLen name_len)
  (h_vi : Converts F.conversion state valueIndex value_index_val)
  (h_vl : Converts F.conversion state valueLen value_len)
  (h_sb : Converts FArray.conversion state sb_data sb_vals)
  (h_maxKV : maxKVPairLen < bn254) (hw : 2 ^ (minBits' maxKVPairLen + 1) < bn254)
:
  ConvertsM FUnit.conversion
    (checkStringBodies perform nameLen valueIndex valueLen sb_data)
    state ()
    ( ( (name_len + 1).val < 2 ^ minBits' maxKVPairLen ∧
        (1 : ZMod bn254).val < maxKVPairLen ∧ (1 : ZMod bn254).val < (name_len + 1).val ) ∧
      ( (value_index_val + value_len).val < 2 ^ minBits' maxKVPairLen ∧
        value_index_val.val < maxKVPairLen ∧ value_index_val.val < (value_index_val + value_len).val ) ∧
      True ∧
      (∀ i : Fin maxKVPairLen,
        (perform_val = true →
          ((decide ((1:ZMod bn254).val ≤ i.val) ^^ decide ((name_len + 1).val ≤ i.val)) ||
            (decide (value_index_val.val ≤ i.val) ^^ decide ((value_index_val + value_len).val ≤ i.val)))
          = true → sb_vals[i] = true) ∧
        (perform_val = true → sb_vals[i] = true →
          ((decide ((1:ZMod bn254).val ≤ i.val) ^^ decide ((name_len + 1).val ≤ i.val)) ||
            (decide (value_index_val.val ≤ i.val) ^^ decide ((value_index_val + value_len).val ≤ i.val)))
          = true) ) )
:= by
  unfold checkStringBodies
  step mkF.convertsM as one
  step mkAdd.convertsM h_nl h_one as nameEnd
  simp only [true_implies]
  have hNameSel := arraySelector.convertsM h_one h_nameEnd h_maxKV hw
  clear h_nl h_one h_nameEnd
  replace h_vi := converts_skip hNameSel h_vi
  replace h_vl := converts_skip hNameSel h_vl
  replace h_perform := converts_skip hNameSel h_perform
  replace h_sb := converts_skip hNameSel h_sb
  apply convertsM_bind_and hNameSel
  have h_nameSel_result := hNameSel.result
  clear hNameSel
  step mkAdd.convertsM h_vi h_vl as valueEnd
  simp only [true_implies]
  have hValueSel := arraySelector.convertsM h_vi h_valueEnd h_maxKV hw
  clear h_valueEnd
  have h_nameSel_pw := FArray.converts_iff_FB_converts.mp (converts_skip hValueSel h_nameSel_result)
  replace h_perform := converts_skip hValueSel h_perform
  replace h_sb := converts_skip hValueSel h_sb
  apply convertsM_bind_and hValueSel
  have h_valueSel_pw := FArray.converts_iff_FB_converts.mp hValueSel.result
  have h_nameOrValue := convertsM_zipWithM_or h_nameSel_pw h_valueSel_pw
  replace h_perform := converts_skip h_nameOrValue h_perform
  replace h_sb := converts_skip h_nameOrValue h_sb
  apply convertsM_bind_and h_nameOrValue
  have h_pair := fun i : Fin maxKVPairLen => FBPair.converts_zip h_nameOrValue.result h_sb i.isLt
  apply convertsM_of_convertsM
    (convertsM_foldlM_ctx_constraints (C_ctx := FB.conversion) (C_acc := FUnit.conversion)
      (init_val := ())
      (f_spec := fun (_ : Bool) (_ : Unit) (_ : Bool × Bool) => ())
      (step_constraints := fun (g : Bool) (xv : Bool × Bool) =>
        (g = true → xv.1 = true → xv.2 = true) ∧ (g = true → xv.2 = true → xv.1 = true))
      h_perform h_pair FUnit.converts
      (fun h_ctx h_acc h_x => guardedStringBodyCheck_convertsM h_ctx
        (FBPair.converts_fst h_x) (FBPair.converts_snd h_x)))
  · rfl
  · simp [Vector.getElem_zip, Vector.getElem_ofFn, Fin.getElem_fin]

def parseJWTFieldWithQuotedValue
  {maxKVPairLen maxNameLen maxValueLen : ℕ}
  (fi : QuotedFieldInput maxKVPairLen maxNameLen maxValueLen)
  (h_name  : maxNameLen  ≤ maxKVPairLen)
  (h_value : maxValueLen ≤ maxKVPairLen)
  (skipChecks         : FB bn254) :
  ClapM bn254 Unit
:= do
  -- Delegate shared structural checks
  parseJWTFieldSharedLogic h_name h_value fi.field fi.name fi.value fi.colonIndex fi.valueIndex skipChecks
  let perform : FB bn254 ← not skipChecks
  -- Check 0+1: field[value_index - 1] == '"' and field[value_index + value_len] == '"'
  -- (quotes around the value)
  checkValueQuotes fi.field.data perform fi.valueIndex fi.value.len
  -- Check 2: whitespace in the three "gap" zones
  checkWhitespaceZonesQuoted fi.field.data perform fi.name.len fi.colonIndex fi.valueIndex
    fi.value.len fi.field.len
  -- Check 3: name/value content positions agree exactly with fieldStringBodies
  checkStringBodies perform fi.name.len fi.valueIndex fi.value.len fi.fieldStringBodies.data

namespace parseJWTFieldWithQuotedValue

open Poseidon RandomOracle Primes FiatShamir

open FString

def parses (H : HashFn) {maxKVPairLen maxNameLen maxValueLen : ℕ}
  (field_vals : Vector (ZMod bn254) maxKVPairLen)
  (field_len : ZMod bn254)
  (name_vals : Vector (ZMod bn254) maxNameLen)
  (name_len : ZMod bn254)
  (value_vals : Vector (ZMod bn254) maxValueLen)
  (value_len : ZMod bn254)
  (sb_vals : Vector Bool maxKVPairLen)
  (colon_index_val value_index_val : ZMod bn254)
  (skipChecks_val  : Bool) :
  Prop
:=
  let charBeforeValue := field_vals.getD (value_index_val - 1).val 0 |>.val
  let charAfterValue := field_vals.getD (value_index_val + value_len).val 0 |>.val
  ¬skipChecks_val →
    parseJWTFieldSharedLogic.parses H field_vals field_len name_vals name_len
      value_vals
      value_len
      colon_index_val
      value_index_val
      false
    ∧
    charBeforeValue = /- quotes -/ 34 ∧
    charAfterValue = /- quotes -/ 34 ∧
    (∀ i : Fin maxKVPairLen,
      (name_len + 2).val ≤ i.val ∧ i.val < colon_index_val.val ∨
      (colon_index_val + 1).val ≤ i.val ∧ i.val < (value_index_val - 1).val ∨
      (value_index_val + value_len + 1).val ≤ i.val ∧ i.val < (field_len - 1).val →
        isWs field_vals[i].val
    ) ∧
    ∀ i : Fin maxKVPairLen,
      1 ≤ i.val ∧ i.val < name_len.val + 1 ∨
      value_index_val.val ≤ i.val ∧ i.val < (value_index_val + value_len).val ↔
        sb_vals[i] = true

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
  {quoted : QuotedFieldInput maxKVPairLen maxNameLen maxValueLen}
  {skipChecks  : FB bn254}
  -- Ideal values
  {field_vals : Vector (ZMod bn254) maxKVPairLen}
  {sb_vals : Vector Bool maxKVPairLen}
  {field_len : ZMod bn254}
  {name_vals : Vector (ZMod bn254) maxNameLen}
  {name_len : ZMod bn254}
  {value_vals : Vector (ZMod bn254) maxValueLen}
  {value_len : ZMod bn254}
  {colon_index_val value_index_val : ZMod bn254}
  {skipChecks_val  : Bool}
  -- Conversion hypotheses
  (h_field_val : Converts FVec.conversion state quoted.field.data field_vals)
  (h_sb_val : Converts FArray.conversion state quoted.fieldStringBodies.data sb_vals)
  (h_field_len : Converts F.conversion state quoted.field.len field_len)
  (h_name_val : Converts FVec.conversion state quoted.name.data name_vals)
  (h_name_len : Converts F.conversion state quoted.name.len name_len)
  (h_value_val : Converts FVec.conversion state quoted.value.data value_vals)
  (h_value_len : Converts F.conversion state quoted.value.len value_len)
  (h_ci : Converts F.conversion state quoted.colonIndex colon_index_val)
  (h_vi : Converts F.conversion state quoted.valueIndex value_index_val)
  (h_sk : Converts FB.conversion state skipChecks skipChecks_val)
  -- Range bounds (`w := 20` is hard-coded in the body)
  (h_name_len_w : name_len.val < 2 ^ 20)
  (h_colon_index_w : colon_index_val.val < 2 ^ 20)
  (h_value_index_w : value_index_val.val < 2 ^ 20)
  (h_field_len_w : field_len.val < 2 ^ 20)
  (h_sum_len_w : (name_len + value_len).val < 2 ^ 20) :
  ConvertsM FUnit.conversion
    (parseJWTFieldWithQuotedValue quoted h_name_len_lt h_value_len_lt
      skipChecks
    )
    state
    ()
    ( (∀ i : Fin maxKVPairLen, field_vals[i].val < 2^8) ∧
      (∀ i : Fin maxNameLen, name_vals[i].val < 2^8) ∧
      (∀ i : Fin maxValueLen, value_vals[i].val < 2^8) ∧

      (value_index_val - 1).val < maxKVPairLen ∧
      (value_index_val + value_len).val < maxKVPairLen ∧
      0 < (name_len + 2).val ∧ (name_len + 2).val ≤ maxKVPairLen ∧ colon_index_val.val < maxKVPairLen ∧
      0 < (colon_index_val + 1).val ∧ (colon_index_val + 1).val ≤ maxKVPairLen ∧ (value_index_val - 1).val < maxKVPairLen ∧
      0 < (value_index_val + value_len + 1).val ∧ (value_index_val + value_len + 1).val ≤ maxKVPairLen ∧ (field_len - 1).val < maxKVPairLen ∧
      1 < maxKVPairLen ∧ 1 < (name_len + 1).val ∧
      value_index_val.val < maxKVPairLen ∧ value_index_val.val < (value_index_val + value_len).val ∧

      parses H field_vals field_len name_vals name_len value_vals value_len
        sb_vals
        colon_index_val
        value_index_val
        skipChecks_val
    )
:= by
  have hw20 : (2:ℕ) ^ (20 + 1) < bn254 := by decide
  have h_maxKV_bn254 : maxKVPairLen < bn254 := by
    have h1953 : (1953:ℕ) < bn254 := by decide
    omega
  have hw_minBits : 2 ^ (minBits' maxKVPairLen + 1) < bn254 := by
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
  unfold parseJWTFieldWithQuotedValue
  refine convertsM_of_convertsM
    (constraints1 :=
      ( (∀ i : Fin maxKVPairLen, field_vals[i].val < 2^8) ∧
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
      ( ( (value_index_val - 1).val < maxKVPairLen ∧
          ((!skipChecks_val) = true → field_vals.getD (value_index_val - 1).val 0 = 34) ) ∧
        ( (value_index_val + value_len).val < maxKVPairLen ∧
          ((!skipChecks_val) = true → field_vals.getD (value_index_val + value_len).val 0 = 34) ) ) ∧
      ( ( (0 < (name_len + 2).val ∧ (name_len + 2).val ≤ maxKVPairLen ∧ colon_index_val.val < maxKVPairLen) ∧
          (0 < (colon_index_val + 1).val ∧ (colon_index_val + 1).val ≤ maxKVPairLen ∧
            (value_index_val - 1).val < maxKVPairLen) ∧
          (0 < (value_index_val + (value_len + 1)).val ∧
              (value_index_val + (value_len + 1)).val ≤ maxKVPairLen ∧
            (field_len - 1).val < maxKVPairLen) ) ∧
        (∀ i : Fin maxKVPairLen,
          lessThan.lessThanOk 8 8 field_vals[i] ∧ lessThan.lessThanOk 8 field_vals[i] 14) ∧
        ((!skipChecks_val) = true → ∀ i : Fin maxKVPairLen,
          (if ((decide (0 < (name_len + 2).val ∧ (name_len + 2).val ≤ i.val) &&
                  decide (i.val < colon_index_val.val)) ||
               (decide (0 < (colon_index_val + 1).val ∧ (colon_index_val + 1).val ≤ i.val) &&
                  decide (i.val < (value_index_val - 1).val)) ||
               (decide (0 < (value_index_val + (value_len + 1)).val ∧
                    (value_index_val + (value_len + 1)).val ≤ i.val) &&
                  decide (i.val < (field_len - 1).val)))
             then (1 : ZMod bn254) else 0) *
            (if ((lessThan.lessThanRaw 8 8 field_vals[i] && lessThan.lessThanRaw 8 field_vals[i] 14) ||
                  field_vals[i] == 32) then (0 : ZMod bn254) else 1) = 0) ) ∧
      ( ( (name_len + 1).val < 2 ^ minBits' maxKVPairLen ∧
          (1 : ZMod bn254).val < maxKVPairLen ∧ (1 : ZMod bn254).val < (name_len + 1).val ) ∧
        ( (value_index_val + value_len).val < 2 ^ minBits' maxKVPairLen ∧
          value_index_val.val < maxKVPairLen ∧ value_index_val.val < (value_index_val + value_len).val ) ∧
        True ∧
        (∀ i : Fin maxKVPairLen,
          ((!skipChecks_val) = true →
            ((decide ((1:ZMod bn254).val ≤ i.val) ^^ decide ((name_len + 1).val ≤ i.val)) ||
              (decide (value_index_val.val ≤ i.val) ^^ decide ((value_index_val + value_len).val ≤ i.val)))
            = true → sb_vals[i] = true) ∧
          ((!skipChecks_val) = true → sb_vals[i] = true →
            ((decide ((1:ZMod bn254).val ≤ i.val) ^^ decide ((name_len + 1).val ≤ i.val)) ||
              (decide (value_index_val.val ≤ i.val) ^^ decide ((value_index_val + value_len).val ≤ i.val)))
            = true) ) )
    )
    ?_ rfl ?hiff
  · have hSL := parseJWTFieldSharedLogic.convertsM h_H h_name_len_lt h_value_len_lt h_len_bound
      h_field_val h_field_len h_name_val h_name_len h_value_val h_value_len h_ci h_vi h_sk
      h_name_len_w h_colon_index_w h_value_index_w h_field_len_w h_sum_len_w
    replace h_field_val := converts_skip hSL h_field_val
    replace h_name_val := converts_skip hSL h_name_val
    replace h_name_len := converts_skip hSL h_name_len
    replace h_ci := converts_skip hSL h_ci
    replace h_vi := converts_skip hSL h_vi
    replace h_value_val := converts_skip hSL h_value_val
    replace h_value_len := converts_skip hSL h_value_len
    replace h_field_len := converts_skip hSL h_field_len
    replace h_sk := converts_skip hSL h_sk
    replace h_sb_val := converts_skip hSL h_sb_val
    apply convertsM_bind_and hSL
    clear hSL
    have hNot := not.convertsM h_sk
    replace h_field_val := converts_skip hNot h_field_val
    replace h_name_val := converts_skip hNot h_name_val
    replace h_name_len := converts_skip hNot h_name_len
    replace h_ci := converts_skip hNot h_ci
    replace h_vi := converts_skip hNot h_vi
    replace h_value_val := converts_skip hNot h_value_val
    replace h_value_len := converts_skip hNot h_value_len
    replace h_field_len := converts_skip hNot h_field_len
    replace h_sb_val := converts_skip hNot h_sb_val
    refine convertsM_bind hNot ?_ (fun _ => trivial)
    simp only [true_implies]
    have h_perform := hNot.result
    clear hNot
    have hCheckValueQuotes := checkValueQuotes.convertsM h_field_val h_perform h_vi h_value_len
      h_maxKV_bn254
    replace h_field_val := converts_skip hCheckValueQuotes h_field_val
    replace h_vi := converts_skip hCheckValueQuotes h_vi
    replace h_value_len := converts_skip hCheckValueQuotes h_value_len
    replace h_name_len := converts_skip hCheckValueQuotes h_name_len
    replace h_ci := converts_skip hCheckValueQuotes h_ci
    replace h_field_len := converts_skip hCheckValueQuotes h_field_len
    replace h_sb_val := converts_skip hCheckValueQuotes h_sb_val
    replace h_perform := converts_skip hCheckValueQuotes h_perform
    apply convertsM_bind_and hCheckValueQuotes
    clear hCheckValueQuotes
    have hCheckWS := checkWhitespaceZonesQuoted.convertsM h_field_val h_perform h_name_len h_ci h_vi
      h_value_len h_field_len h_maxKV_bn254
    replace h_vi := converts_skip hCheckWS h_vi
    replace h_value_len := converts_skip hCheckWS h_value_len
    replace h_name_len := converts_skip hCheckWS h_name_len
    replace h_sb_val := converts_skip hCheckWS h_sb_val
    replace h_perform := converts_skip hCheckWS h_perform
    apply convertsM_bind_and hCheckWS
    clear hCheckWS
    exact checkStringBodies.convertsM h_perform h_name_len h_vi h_value_len h_sb_val h_maxKV_bn254
      hw_minBits
  case hiff =>
    have hskf_of_neg : ¬skipChecks_val → skipChecks_val = false := by
      intro hneg
      revert hneg
      cases skipChecks_val <;> simp
    have h2v : (2 : ZMod bn254).val = 2 := by decide
    have h1v : (1 : ZMod bn254).val = 1 := by decide
    have h_vlp1_assoc : value_index_val + (value_len + 1) = value_index_val + value_len + 1 := by
      ring
    have h20lt : (2:ℕ) ^ 20 < bn254 := by decide
    have h_nl1 : (name_len + 1).val = name_len.val + 1 := by
      have hlt : name_len.val + (1 : ZMod bn254).val < bn254 := by rw [h1v]; omega
      rw [ZMod.val_add_of_lt hlt, h1v]
    have h_name2 : (name_len + 2).val = name_len.val + 2 := by
      have hlt : name_len.val + (2 : ZMod bn254).val < bn254 := by rw [h2v]; omega
      rw [ZMod.val_add_of_lt hlt, h2v]
    constructor
    · rintro ⟨⟨hB1, hB2, hB3, hW1, hW2, hW3, hP1, hV1, hV2, hV3, hP2, hSLparses⟩,
        ⟨⟨hQ1a, hQ1b⟩, ⟨hQ2a, hQ2b⟩⟩,
        ⟨⟨hZA, hZB, hZC⟩, hZok, hZarith⟩,
        ⟨⟨hNS1, hNS2, hNS3⟩, ⟨hVS1, hVS2, hVS3⟩, -, hSBarith⟩⟩
      refine ⟨hB1, hB2, hB3, hQ1a, hQ2a, hZA.1, hZA.2.1, hZA.2.2, hZB.1, hZB.2.1, hZB.2.2,
        ?_, ?_, ?_, ?_, ?_, hVS2, hVS3, ?_⟩
      · rw [h_vlp1_assoc] at hZC; exact hZC.1
      · rw [h_vlp1_assoc] at hZC; exact hZC.2.1
      · rw [h_vlp1_assoc] at hZC; exact hZC.2.2
      · omega
      · rw [h1v] at hNS2; omega
      · intro hneg
        have hskf := hskf_of_neg hneg
        have hguard : (!skipChecks_val) = true := by simp [hskf]
        refine ⟨fun _ => hSLparses hneg, ?_, ?_, ?_, ?_⟩
        · have h34 := hQ1b hguard
          rw [h34]; decide
        · have h34 := hQ2b hguard
          rw [h34]; decide
        · intro i hranges
          have hzarith_i := hZarith hguard i
          have hzone_true :
              ((decide (0 < (name_len + 2).val ∧ (name_len + 2).val ≤ i.val) &&
                    decide (i.val < colon_index_val.val)) ||
                (decide (0 < (colon_index_val + 1).val ∧ (colon_index_val + 1).val ≤ i.val) &&
                    decide (i.val < (value_index_val - 1).val)) ||
                (decide (0 < (value_index_val + (value_len + 1)).val ∧
                      (value_index_val + (value_len + 1)).val ≤ i.val) &&
                    decide (i.val < (field_len - 1).val))) = true := by
            simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
            rcases hranges with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
            · exact Or.inl (Or.inl ⟨⟨hZA.1, h1⟩, h2⟩)
            · exact Or.inl (Or.inr ⟨⟨hZB.1, h1⟩, h2⟩)
            · exact Or.inr ⟨⟨hZC.1, by rw [h_vlp1_assoc]; exact h1⟩, h2⟩
          rw [hzone_true] at hzarith_i
          simp only [if_true, one_mul] at hzarith_i
          by_contra hws
          have hraw : ((lessThan.lessThanRaw 8 8 field_vals[i] && lessThan.lessThanRaw 8 field_vals[i] 14) ||
              field_vals[i] == 32) = false := by
            rw [lessThanRaw_isWs_eq (hB1 i)]
            simpa using hws
          rw [hraw] at hzarith_i
          simp at hzarith_i
        · intro i
          have hsb_i := hSBarith i
          constructor
          · intro hrange
            rcases hrange with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · refine hsb_i.1 hguard ?_
              simp only [Bool.or_eq_true]
              left
              rw [h1v, h_nl1]
              exact (xor_le_iff_interval (by omega)).mpr ⟨h1, h2⟩
            · refine hsb_i.1 hguard ?_
              simp only [Bool.or_eq_true]
              right
              exact (xor_le_iff_interval hV3).mpr ⟨h1, h2⟩
          · intro hsb
            have hor := hsb_i.2 hguard hsb
            simp only [Bool.or_eq_true] at hor
            rcases hor with h | h
            · left
              rw [h1v, h_nl1] at h
              exact (xor_le_iff_interval (by omega)).mp h
            · right
              exact (xor_le_iff_interval hV3).mp h
    · rintro ⟨hB1, hB2, hB3, hQ1a, hQ2a, hZA1, hZA2, hZA3, hZB1, hZB2, hZB3, hZC1, hZC2, hZC3,
        hNS2, hNS3, hVS1, hVS2, hparses⟩
      have hlt_minBits : maxKVPairLen < 2 ^ minBits' maxKVPairLen := by
        unfold minBits'
        split
        · rename_i h0
          simp [h0]
        · rename_i hx
          exact (Nat.log2_lt hx).mp (Nat.lt_succ_self _)
      have h0name : 0 < name_len.val := by rw [h_nl1] at hNS3; omega
      have h1name : name_len.val + 1 < maxKVPairLen := by rw [h_name2] at hZA2; omega
      have hNS1 : (name_len + 1).val < 2 ^ minBits' maxKVPairLen := by omega
      have hV1 : (value_index_val + value_len).val < 2 ^ minBits' maxKVPairLen := by omega
      have h0val : 0 < value_len.val := by
        by_contra hc
        push Not at hc
        have hv0 : value_len.val = 0 := Nat.le_zero.mp hc
        have hz : value_len = 0 := ZMod.val_injective bn254 (by simp [hv0])
        rw [hz, add_zero] at hVS2
        omega
      have hZC' : 0 < (value_index_val + (value_len + 1)).val ∧
          (value_index_val + (value_len + 1)).val ≤ maxKVPairLen ∧
          (field_len - 1).val < maxKVPairLen := by
        rw [h_vlp1_assoc]
        exact ⟨hZC1, by omega, hZC3⟩
      have h34 : (34 : ZMod bn254).val = 34 := by decide
      refine ⟨⟨hB1, hB2, hB3, h1name, hZA3, hZC3, h0name, hV1, hVS1, hVS2, h0val, ?_⟩,
        ⟨⟨hQ1a, ?_⟩, ⟨hQ2a, ?_⟩⟩,
        ⟨⟨⟨hZA1, hZA2, hZA3⟩, ⟨hZB1, hZB2, hZB3⟩, hZC'⟩,
          fun i => ⟨lessThan.lessThanOk_of
            (show (8 : ZMod bn254).val < 2 ^ 8 by decide) (hB1 i) (by decide),
            lessThan.lessThanOk_of (hB1 i) (show (14 : ZMod bn254).val < 2 ^ 8 by decide) (by decide)⟩, ?_⟩,
        ⟨hNS1, by rw [h1v]; omega, by rw [h1v]; omega⟩,
        ⟨hV1, hVS1, hVS2⟩, trivial, ?_⟩
      · intro hneg
        exact (hparses hneg).1 (by decide)
      · intro hguard
        have hneg : ¬skipChecks_val := by intro h; rw [h] at hguard; simp at hguard
        have h34eq := (hparses hneg).2.1
        exact ZMod.val_injective bn254 (by rw [h34, h34eq])
      · intro hguard
        have hneg : ¬skipChecks_val := by intro h; rw [h] at hguard; simp at hguard
        have h34eq := (hparses hneg).2.2.1
        exact ZMod.val_injective bn254 (by rw [h34, h34eq])
      · intro hguard i
        by_cases hzone :
            ((decide (0 < (name_len + 2).val ∧ (name_len + 2).val ≤ i.val) &&
                  decide (i.val < colon_index_val.val)) ||
              (decide (0 < (colon_index_val + 1).val ∧ (colon_index_val + 1).val ≤ i.val) &&
                  decide (i.val < (value_index_val - 1).val)) ||
              (decide (0 < (value_index_val + (value_len + 1)).val ∧
                    (value_index_val + (value_len + 1)).val ≤ i.val) &&
                  decide (i.val < (field_len - 1).val))) = true
        · have hneg : ¬skipChecks_val := by intro h; rw [h] at hguard; simp at hguard
          have hranges_i :
              ((name_len + 2).val ≤ i.val ∧ i.val < colon_index_val.val) ∨
              ((colon_index_val + 1).val ≤ i.val ∧ i.val < (value_index_val - 1).val) ∨
              ((value_index_val + (value_len + 1)).val ≤ i.val ∧ i.val < (field_len - 1).val) := by
            simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hzone
            rcases hzone with (⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩
            · exact Or.inl ⟨h1.2, h2⟩
            · exact Or.inr (Or.inl ⟨h1.2, h2⟩)
            · exact Or.inr (Or.inr ⟨h1.2, h2⟩)
          rw [h_vlp1_assoc] at hranges_i
          have hws_i := (hparses hneg).2.2.2.1 i (by
            rcases hranges_i with h | h | h
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr h))
          rw [hzone]
          rw [lessThanRaw_isWs_eq (hB1 i)]
          simpa using hws_i
        · simp only [Bool.not_eq_true] at hzone
          rw [hzone]
          simp
      · intro i
        constructor
        · intro hguard hxor
          have hneg : ¬skipChecks_val := by intro h; rw [h] at hguard; simp at hguard
          apply ((hparses hneg).2.2.2.2 i).mp
          simp only [Bool.or_eq_true] at hxor
          rcases hxor with h | h
          · left
            have h' := (xor_le_iff_interval (a := (1:ZMod bn254).val) (b := (name_len + 1).val)
              (by rw [h1v, h_nl1]; omega)).mp h
            rwa [h1v, h_nl1] at h'
          · right
            exact (xor_le_iff_interval hVS2).mp h
        · intro hguard hsb
          have hneg : ¬skipChecks_val := by intro h; rw [h] at hguard; simp at hguard
          have hor := ((hparses hneg).2.2.2.2 i).mpr hsb
          simp only [Bool.or_eq_true]
          rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · left
            have : (decide ((1:ZMod bn254).val ≤ i.val) ^^ decide ((name_len + 1).val ≤ i.val)) = true :=
              (xor_le_iff_interval (a := (1:ZMod bn254).val) (b := (name_len + 1).val)
                (by rw [h1v]; omega)).mpr (by rw [h1v]; omega)
            simpa using this
          · right
            exact (xor_le_iff_interval hVS2).mpr ⟨h1, h2⟩

theorem sound {nF nN nV} (field name value : String)
  (stringBodies : Vector Bool nF)
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
        stringBodies
        colonIndex
        valueIndex
        } ≤ (((nF - 1) + (max nN nV - 1) + 50 : ℕ) : ENNReal) / bn254
:= by
  have h_sub : {f : Query → ZMod bn254 |
      parses (skipChecks_val := false) (Query.toHashFn f) (encodeV nF field) field.length
        (encodeV nN name) name.length (encodeV nV value) value.length stringBodies colonIndex
        valueIndex} ⊆
      {f | parseJWTFieldSharedLogic.parses (Query.toHashFn f) (encodeV nF field) field.length
        (encodeV nN name) name.length (encodeV nV value) value.length colonIndex valueIndex
        false} := by
    intro f hf
    unfold parses at hf
    obtain ⟨h1, -, -, -, -⟩ := hf (by decide)
    exact h1
  exact (MeasureTheory.measure_mono h_sub).trans
    (parseJWTFieldSharedLogic.sound field name value colonIndex valueIndex h_fieldLen h_nameLen
      h_valueLen h_namePos h_valuePos h_nF_name h_valueIndex h_nm_name h_nm_value h_fieldBytes
      h_nameBytes h_valueBytes h_bad)

theorem complete {nF nN nV} (field name value : String)
  (colonIndex valueIndex : ZMod bn254)
  (stringBodies : Vector Bool nF)
  (h_fieldLen : field.length ≤ nF)
  (h_nameLen : name.length ≤ nN)
  (h_valueLen : value.length ≤ nV)
  (h_namePos : 0 < name.length)
  (h_valuePos : 0 < value.length)
  (h_nF_name : 1 < nF)
  (h_nm_name : nF + nN < bn254)
  (h_nm_value : nF + nV < bn254)
  (h_fieldBytes : ∀ c ∈ field.toList, c.toNat < 256)
  (h_nameBytes : ∀ c ∈ name.toList, 0 < c.toNat ∧ c.toNat < 256)
  (h_valueBytes : ∀ c ∈ value.toList, 0 < c.toNat ∧ c.toNat < 256)
  (h_fit_name : 1 + name.length ≤ field.length)
  (h_pre_name : name.toList <+: field.toList.drop 1)
  (h_fit_val : valueIndex.val + value.length ≤ field.length)
  (h_pre_val : value.toList <+: field.toList.drop valueIndex.val)
  (h_colon_order : name.length < colonIndex.val)
  (h_value_order : colonIndex.val < valueIndex.val)
  (h_open_quote : field.toList[0]? = some '\"')
  (h_close_quote : field.toList[name.length + 1]? = some '\"')
  (h_quoted₁ : field.toList[(valueIndex - 1).val]? = some '\"')
  (h_quoted₂ : field.toList[(valueIndex + value.length).val]? = some '\"')
  (h_colon : field.toList[colonIndex.val]? = some ':')
  (h_last_char : field.toList[field.length - 1]? = some ',' ∨
    field.toList[field.length - 1]? = some '}')
  (h_ws_zones : ∀ i,
    name.length + 2 ≤ i ∧ i < colonIndex.val ∨
    colonIndex.val + 1 ≤ i ∧ i < (valueIndex - 1).val ∨
    valueIndex.val + value.length + 1 ≤ i ∧ i < field.length - 1 →
    (field.toList[i]?.elim false (isWs ∘ Char.toNat) : Prop)
  )
  (h_stringBodies : ∀ i : ℕ,
    1 ≤ i ∧ i < name.length + 1 ∨
    valueIndex.val ≤ i ∧ i < valueIndex.val + value.length ↔
      stringBodies.toList[i]? = some true
  )
  :
  randomOracle.toOuterMeasure
    {f |
      ¬parses (skipChecks_val := false) (Query.toHashFn f)
        (encodeV nF field)
        field.length
        (encodeV nN name)
        name.length
        (encodeV nV value)
        value.length
        stringBodies
        colonIndex
        valueIndex
    }
      ≤ ((2 * (nF - 1) + 100 : ℕ) : ENNReal) / bn254
:= by
  have h1v : (1 : ZMod bn254).val = 1 := by decide
  have h2v : (2 : ZMod bn254).val = 2 := by decide
  have h256 : (256 : ℕ) < bn254 := by decide
  have hUInt8lt : ∀ c : Char, c.toUInt8.toNat < bn254 := fun c =>
    lt_trans (UInt8.toNat_lt_size c.toUInt8) h256
  have hvi_lt_fieldLen : valueIndex.val < field.length := by omega
  have h_vi_nF : valueIndex.val < nF := by omega
  have h_nl_lt : name.length < bn254 := by omega
  have h_nl_val : (name.length : ZMod bn254).val = name.length := ZMod.val_natCast_of_lt h_nl_lt
  have h_nl2_val : ((name.length : ZMod bn254) + 2).val = name.length + 2 := by
    rw [ZMod.val_add_of_lt (show (name.length : ZMod bn254).val + (2 : ZMod bn254).val < bn254 by
      rw [h_nl_val, h2v]; omega), h_nl_val, h2v]
  have h_vl_lt : value.length < bn254 := by omega
  have h_vl_val : (value.length : ZMod bn254).val = value.length := ZMod.val_natCast_of_lt h_vl_lt
  have h_vi_vl_val : (valueIndex + (value.length : ZMod bn254)).val
      = valueIndex.val + value.length := by
    rw [ZMod.val_add_of_lt (show valueIndex.val + (value.length : ZMod bn254).val < bn254 by
      rw [h_vl_val]; omega), h_vl_val]
  have h_fl_lt : field.length < bn254 := by omega
  have h_fl_val : (field.length : ZMod bn254).val = field.length := ZMod.val_natCast_of_lt h_fl_lt
  have h_fl1_val : ((field.length : ZMod bn254) - 1).val = field.length - 1 := by
    rw [ZMod.val_sub (by rw [h_fl_val, h1v]; omega), h_fl_val, h1v]
  have hvi_ge1 : 1 ≤ valueIndex.val := by omega
  have h_vim1_val : (valueIndex - 1).val = valueIndex.val - 1 := by
    rw [ZMod.val_sub (by rw [h1v]; omega), h1v]
  have h_ci1_val : (colonIndex + 1).val = colonIndex.val + 1 := by
    rw [ZMod.val_add_of_lt (show colonIndex.val + (1 : ZMod bn254).val < bn254 by
      rw [h1v]; omega), h1v]
  have h_vlp1_val : (valueIndex + (value.length : ZMod bn254) + 1).val
      = valueIndex.val + value.length + 1 := by
    rw [ZMod.val_add_of_lt
      (show (valueIndex + (value.length : ZMod bn254)).val + (1 : ZMod bn254).val < bn254 by
        rw [h_vi_vl_val, h1v]; omega), h_vi_vl_val, h1v]
  -- The two quote checks, proved unconditionally (independent of the random oracle).
  have hw_q1 : (valueIndex - 1).val < nF := by rw [h_vim1_val]; omega
  have hs_q1 : (valueIndex - 1).val < field.toList.length := by
    rw [String.length_toList, h_vim1_val]; omega
  have hQ1 : ((encodeV (p := bn254) nF field).getD (valueIndex - 1).val 0).val = 34 := by
    rw [encodeV_getD_of_lt hw_q1 hs_q1, List.getD_eq_getElem?_getD, h_quoted₁]
    decide
  -- The index at `h_quoted₂` is only ever a successful list lookup when it's in bounds — `h_fit_val`
  -- alone only gives `≤ field.length`, not the strict bound needed here.
  have hs_q2 : (valueIndex + (value.length : ZMod bn254)).val < field.toList.length := by
    by_contra hcon
    push Not at hcon
    rw [List.getElem?_eq_none hcon] at h_quoted₂
    exact absurd h_quoted₂ (by simp)
  have hw_q2 : (valueIndex + (value.length : ZMod bn254)).val < nF := by
    have := hs_q2
    rw [String.length_toList] at this
    omega
  have hQ2 : ((encodeV (p := bn254) nF field).getD
      (valueIndex + (value.length : ZMod bn254)).val 0).val = 34 := by
    rw [encodeV_getD_of_lt hw_q2 hs_q2, List.getD_eq_getElem?_getD, h_quoted₂]
    decide
  -- The whitespace-zones conjunct, proved unconditionally.
  have hWS : ∀ i : Fin nF,
      (((name.length : ZMod bn254) + 2).val ≤ i.val ∧ i.val < colonIndex.val) ∨
        ((colonIndex + 1).val ≤ i.val ∧ i.val < (valueIndex - 1).val) ∨
        ((valueIndex + (value.length : ZMod bn254) + 1).val ≤ i.val ∧
          i.val < ((field.length : ZMod bn254) - 1).val) →
      isWs ((encodeV (p := bn254) nF field)[i]).val := by
    intro i hranges
    rw [h_nl2_val, h_ci1_val, h_vlp1_val, h_fl1_val] at hranges
    have hi_lt_fieldLen : i.val < field.length := by
      rcases hranges with ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨_, h2⟩ <;> omega
    have hi_lt_toList : i.val < field.toList.length := by
      rw [String.length_toList]; exact hi_lt_fieldLen
    have hws := h_ws_zones i.val hranges
    have hgetElem : (encodeV (p := bn254) nF field)[i] =
        (((field.toList[i.val]'hi_lt_toList).toUInt8.toNat : ℕ) : ZMod bn254) :=
      encodeV_getElem_of_lt i.isLt hi_lt_toList
    rw [hgetElem, ZMod.val_natCast_of_lt (hUInt8lt _)]
    have hsome : field.toList[i.val]? = some (field.toList[i.val]'hi_lt_toList) :=
      List.getElem?_eq_getElem hi_lt_toList
    rw [hsome] at hws
    rw [toUInt8_toNat_of_lt (h_fieldBytes _ (List.getElem_mem hi_lt_toList))]
    simpa using hws
  -- The string-body agreement conjunct, proved unconditionally.
  have hSB : ∀ i : Fin nF,
      (1 ≤ i.val ∧ i.val < (name.length : ZMod bn254).val + 1 ∨
        valueIndex.val ≤ i.val ∧
          i.val < (valueIndex + (value.length : ZMod bn254)).val) ↔
        stringBodies[i] = true := by
    intro i
    have hbridge : stringBodies.toList[i.val]? = some true ↔ stringBodies[i] = true := by
      rw [Vector.getElem?_toList, Vector.getElem?_eq_getElem i.isLt, Fin.getElem_fin]
      exact Option.some_inj
    rw [h_nl_val, h_vi_vl_val, ← hbridge]
    exact h_stringBodies i.val
  -- `parses` reduces to exactly `parseJWTFieldSharedLogic.parses`, given the above: the four extra
  -- conjuncts hold for every `f`, so `¬parses` is no weaker than `¬parseJWTFieldSharedLogic.parses`.
  have h_sub : {f : Query → ZMod bn254 |
      ¬parses (skipChecks_val := false) (Query.toHashFn f) (encodeV nF field) field.length
        (encodeV nN name) name.length (encodeV nV value) value.length stringBodies colonIndex
        valueIndex} ⊆
      {f | ¬parseJWTFieldSharedLogic.parses (Query.toHashFn f) (encodeV nF field) field.length
        (encodeV nN name) name.length (encodeV nV value) value.length colonIndex valueIndex
        false} := by
    intro f hf hP1
    apply hf
    unfold parses
    exact fun _ => ⟨hP1, hQ1, hQ2, hWS, hSB⟩
  exact (MeasureTheory.measure_mono h_sub).trans
    (parseJWTFieldSharedLogic.complete field name value colonIndex valueIndex h_fieldLen h_nameLen
      h_valueLen h_namePos h_valuePos h_nF_name h_nm_name h_nm_value h_fieldBytes h_nameBytes
      h_valueBytes h_fit_name h_pre_name h_fit_val h_pre_val h_colon_order h_value_order
      h_open_quote h_close_quote h_colon h_last_char)

end parseJWTFieldWithQuotedValue
