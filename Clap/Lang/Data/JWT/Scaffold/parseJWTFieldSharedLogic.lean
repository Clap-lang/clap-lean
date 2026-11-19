import Clap.RandomOracle.HashFn
import Clap.Lang.Core.F.mkF
import Clap.Lang.Core.F.mkSub
import Clap.Lang.Core.F.lessThan
import Clap.Lang.Core.F.conditionalSwap
import Clap.Lang.Core.FB.eq
import Clap.Lang.Core.FB.not
import Clap.Lang.Gate.isZero
import Clap.Model.Convert.PaddedVector
import Clap.Lang.Core.FUnit.guardedEq0
import Clap.Util.Primes
import Clap.Lang.Data.HashToField.hashBytesToField
import Clap.Lang.Data.FString.isSubstring
import Clap.Lang.Data.FArray.selectArrayValue
import Clap.Lang.Core.FUnit.guardedAssertEq
import Mathlib.Data.List.GetD

-- Poseidon is opaque to these proofs, as in HashToField/hashElemsToField.lean and
-- FString/isSubstring.lean (every gadget here routes through `hashBytesToField`).
attribute [local irreducible] Clap.Lang.Poseidon.poseidonBN254

namespace Clap.Lang

namespace parseJWTFieldSharedLogic

open Poseidon RandomOracle Primes FiatShamir

open FString

/-! ## Proof infrastructure for `convertsM`

One private lemma per check (or check shape) in the body's chain of nine guarded assertions.
Per `docs/proving-circuits.md §When step does not apply`, every `guardedEq0`/`guardedAssertEq`
here has a real (non-`True`) slot 5, so adjacent real-constraint binds are composed with
`convertsM_bind_and`, never `step`/`convertsM_bind`. -/

lemma minBits'_le_of_le_1953 {x : ℕ} (h : x ≤ 1953) : minBits' x ≤ 11 := by
  unfold minBits'
  split
  · omega
  · rename_i hx
    have h2048 : (2:ℕ) ^ 11 = 2048 := by norm_num
    have hx11 : x < 2 ^ 11 := by omega
    have := (Nat.log2_lt hx).mpr hx11
    omega

/-- `(if !(decide (a.val < b.val)) then 1 else 0) = 0 ↔ a.val < b.val`, the cleanup each of
checks 0-2's `guardedEq0` leaves behind. -/
private lemma guardedEq0_lt_iff {a b : ZMod bn254} :
    (if !(decide (a.val < b.val) : Bool) then (1 : ZMod bn254) else 0) = 0 ↔ a.val < b.val := by
  by_cases hc : a.val < b.val <;> simp [hc]

-- `action >>= fun _ => step`, generic in `step`. Composing two already-built `ConvertsM` facts
-- this way — rather than via bare `convertsM_bind_and` with no `function :=`, or with
-- `function :=` re-spelling `step`'s own action as fresh text — never needs the elaborator to
-- re-derive or re-typecheck anything about `step`'s action: `step` (and the whole proposition
-- `Cstep`) is read off `h_step`'s own type, not re-elaborated. Re-spelling the same
-- sub-expression (e.g. an `isSubstring` call) as independent fresh text at several nesting
-- levels is what makes the kernel pay for a defeq check between two separately-elaborated
-- copies at every level — directly responsible for whnf timeouts observed composing checks
-- 6/7/8 here.
lemma seqUnit_convertsM
  {β : Type} {conversion2 : Conversion bn254 β}
  {action : ClapM bn254 Unit} {state : ClapMState bn254} {Cprev : Prop}
  (h_action : ConvertsM FUnit.conversion action state () Cprev)
  {step : ClapM bn254 β} {stepVal : conversion2.IdealT} {Cstep : Prop}
  (h_step : ConvertsM conversion2 step (action.getState state) stepVal Cstep)
:
  ConvertsM conversion2 (action >>= fun _ => step) state stepVal (Cprev ∧ Cstep)
:= convertsM_bind_and h_action h_step

/-- `guardedEq0 perform (← not (← lessThan w a b))`: when `perform`, asserts `a.val < b.val`.
Checks 0 (`name_len < colon_index`) and 1 (`colon_index < value_index`) are both instances. -/
lemma lessThanGuardedEq0_convertsM
  {state : ClapMState bn254} {w : ℕ} {a b perform : F bn254}
  {a_val b_val : ZMod bn254} {perform_val : Bool}
  (h_a : Converts F.conversion state a a_val)
  (h_b : Converts F.conversion state b b_val)
  (h_perform : Converts FB.conversion state perform perform_val)
  (ha : a_val.val < 2 ^ w) (hb : b_val.val < 2 ^ w) (hw : 2 ^ (w + 1) < bn254)
:
  ConvertsM FUnit.conversion
    (lessThan w a b >>= fun c0a => not c0a >>= fun c0b => guardedEq0 perform c0b)
    state () (perform_val = true → a_val.val < b_val.val)
:= by
  step lessThan.convertsM h_a h_b ha hb hw as c0a
  step not.convertsM h_c0a as c0b
  apply convertsM_of_convertsM (guardedEq0.convertsM h_perform (F.converts_of_FB_converts h_c0b))
  · rfl
  · simp only [true_implies]
    exact imp_congr_right fun _ => guardedEq0_lt_iff

/-- Check 2: `guardedEq0 perform (← not (← greaterThan w field_len s))`, asserting
`field_len.val > s.val`. -/
lemma check2_convertsM
  {state : ClapMState bn254} {field_len name_len' value_len' perform : F bn254}
  {field_len_val name_len_val value_len_val : ZMod bn254} {perform_val : Bool}
  (h_field_len : Converts F.conversion state field_len field_len_val)
  (h_name_len : Converts F.conversion state name_len' name_len_val)
  (h_value_len : Converts F.conversion state value_len' value_len_val)
  (h_perform : Converts FB.conversion state perform perform_val)
  (h_field_len_w : field_len_val.val < 2 ^ 20)
  (h_sum_len_w : (name_len_val + value_len_val).val < 2 ^ 20)
  (hw20 : (2:ℕ) ^ (20 + 1) < bn254)
:
  ConvertsM FUnit.conversion
    ((name_len' + value_len') >>= fun s =>
      greaterThan 20 field_len s >>= fun c2a => not c2a >>= fun c2b => guardedEq0 perform c2b)
    state () (perform_val = true → field_len_val.val > (name_len_val + value_len_val).val)
:= by
  step mkAdd.convertsM h_name_len h_value_len as s
  step greaterThan.convertsM h_field_len h_s h_field_len_w h_sum_len_w hw20 as c2a
  step not.convertsM h_c2a as c2b
  apply convertsM_of_convertsM (guardedEq0.convertsM h_perform (F.converts_of_FB_converts h_c2b))
  · rfl
  · simp only [true_implies]
    exact imp_congr_right fun _ => guardedEq0_lt_iff

/-- `mkF lit >>= fun c => guardedAssertEq perform x c`: when `perform`, asserts `x.val = lit`.
Checks 3, 5 and 6 are instances, at `lit = 34` (twice, `'"'`) and `lit = 58` (`':'`). -/
lemma assertEqLit_convertsM
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

/-- Check 5: `field[name_len + 1] = '"'`. -/
lemma check5_convertsM
  {maxKVPairLen : ℕ}
  {state : ClapMState bn254} {field_data : FVec bn254 maxKVPairLen} {name_len' perform : F bn254}
  {field_vals : Vector (ZMod bn254) maxKVPairLen} {name_len : ZMod bn254} {perform_val : Bool}
  (h_field_val : Converts FVec.conversion state field_data field_vals)
  (h_name_len : Converts F.conversion state name_len' name_len)
  (h_perform : Converts FB.conversion state perform perform_val)
  (h_maxKV : maxKVPairLen < bn254)
:
  ConvertsM FUnit.conversion
    (mkF 1 >>= fun one => (name_len' + one) >>= fun s5 =>
      selectArrayValue maxKVPairLen field_data s5 >>= fun nameClosingQuote =>
      mkF (34 : ZMod bn254) >>= fun c34 => guardedAssertEq perform nameClosingQuote c34)
    state ()
    ((name_len + 1).val < maxKVPairLen ∧
      (perform_val = true → field_vals.getD (name_len + 1).val 0 = 34))
:= by
  step mkF.convertsM as one
  step mkAdd.convertsM h_name_len h_one as s5
  have hSel := selectArrayValue.convertsM h_s5 h_field_val h_maxKV
  apply convertsM_of_convertsM
    (convertsM_bind_and (function := fun nameClosingQuote =>
        mkF (34 : ZMod bn254) >>= fun c34 => guardedAssertEq perform nameClosingQuote c34)
      hSel (assertEqLit_convertsM hSel.result (converts_skip hSel h_perform)))
  · rfl
  · simp

/-- The tail of check 8, after `lastChar` is known: asserts `lastChar ∈ {44, 125}`. -/
private lemma check8_tail_convertsM
  {state : ClapMState bn254} {lastChar perform : F bn254}
  {lastChar_val : ZMod bn254} {perform_val : Bool}
  (h_lastChar : Converts F.conversion state lastChar lastChar_val)
  (h_perform : Converts FB.conversion state perform perform_val)
:
  ConvertsM FUnit.conversion
    (mkF (44 : ZMod bn254) >>= fun c44 => (lastChar - c44) >>= fun d1 =>
      mkF (125 : ZMod bn254) >>= fun c125 => (lastChar - c125) >>= fun d2 =>
        (d1 * d2) >>= fun prod => guardedEq0 perform prod)
    state () (perform_val = true → (lastChar_val = 44 ∨ lastChar_val = 125))
:= by
  step mkF.convertsM as c44
  step mkSub.convertsM h_lastChar h_c44 as d1
  step mkF.convertsM as c125
  step mkSub.convertsM h_lastChar h_c125 as d2
  step mkMul.convertsM h_d1 h_d2 as prod
  apply convertsM_of_convertsM (guardedEq0.convertsM h_perform h_prod)
  · rfl
  · simp [mul_eq_zero, sub_eq_zero]

/-- Check 8: `field[field_len - 1] ∈ {',', '}'}`. -/
lemma check8_convertsM
  {maxKVPairLen : ℕ}
  {state : ClapMState bn254} {field_data : FVec bn254 maxKVPairLen} {field_len' perform : F bn254}
  {field_vals : Vector (ZMod bn254) maxKVPairLen} {field_len : ZMod bn254} {perform_val : Bool}
  (h_field_val : Converts FVec.conversion state field_data field_vals)
  (h_field_len : Converts F.conversion state field_len' field_len)
  (h_perform : Converts FB.conversion state perform perform_val)
  (h_maxKV : maxKVPairLen < bn254)
:
  ConvertsM FUnit.conversion
    (mkF 1 >>= fun one => (field_len' - one) >>= fun s8 =>
      selectArrayValue maxKVPairLen field_data s8 >>= fun lastChar =>
      mkF (44 : ZMod bn254) >>= fun c44 => (lastChar - c44) >>= fun d1 =>
        mkF (125 : ZMod bn254) >>= fun c125 => (lastChar - c125) >>= fun d2 =>
          (d1 * d2) >>= fun prod => guardedEq0 perform prod)
    state ()
    ((field_len - 1).val < maxKVPairLen ∧
      (perform_val = true → (field_vals.getD (field_len - 1).val 0 = 44 ∨
        field_vals.getD (field_len - 1).val 0 = 125)))
:= by
  step mkF.convertsM as one
  step mkSub.convertsM h_field_len h_one as s8
  have hSel := selectArrayValue.convertsM h_s8 h_field_val h_maxKV
  apply convertsM_of_convertsM
    (convertsM_bind_and (function := fun lastChar =>
        mkF (44 : ZMod bn254) >>= fun c44 => (lastChar - c44) >>= fun d1 =>
          mkF (125 : ZMod bn254) >>= fun c125 => (lastChar - c125) >>= fun d2 =>
            (d1 * d2) >>= fun prod => guardedEq0 perform prod)
      hSel (check8_tail_convertsM hSel.result (converts_skip hSel h_perform)))
  · rfl
  · simp

/-- The tail of check 4, after `nameOk` is known. -/
lemma check4_tail_convertsM
  {state : ClapMState bn254} {perform nameOk : FB bn254} {perform_val accepts_val : Bool}
  (h_nameOk : Converts FB.conversion state nameOk accepts_val)
  (h_perform : Converts FB.conversion state perform perform_val)
:
  ConvertsM FUnit.conversion
    (not nameOk >>= fun c4 => guardedEq0 perform c4)
    state () (perform_val = true → accepts_val = true)
:= by
  step not.convertsM h_nameOk as c4
  apply convertsM_of_convertsM (guardedEq0.convertsM h_perform (F.converts_of_FB_converts h_c4))
  · rfl
  · cases accepts_val <;> simp

/-- The tail of check 7, after `valueOk` is known. -/
private lemma check7_tail_convertsM
  {state : ClapMState bn254} {perform valueOk : FB bn254} {perform_val accepts_val : Bool}
  (h_valueOk : Converts FB.conversion state valueOk accepts_val)
  (h_perform : Converts FB.conversion state perform perform_val)
:
  ConvertsM FUnit.conversion
    (not valueOk >>= fun c7 => guardedEq0 perform c7)
    state () (perform_val = true → accepts_val = true)
:= by
  step not.convertsM h_valueOk as c7
  apply convertsM_of_convertsM (guardedEq0.convertsM h_perform (F.converts_of_FB_converts h_c7))
  · rfl
  · cases accepts_val <;> simp

/-! `isSubstring.sound` takes `strHash` as a value fixed independently of `H` — as its own
docstring (above `isSubstring`'s definition, in `FString/isSubstring.lean`) says, binding `str`
this way is the caller's job. `parseJWTFieldSharedLogic` instead hashes `field` itself once and
passes that hash as `strHash` to both its name- and value-checks, so it cannot cite
`isSubstring.sound` directly: the challenge then depends on `H` through *two* hashed vectors
(`field` and the substring), not one, so the collision term doubles, `50 = 2 · 25`, one `25` per
hashed vector via `HashToField.challenge_mem_transcript_le` (the same accounting
`assertIsConcatenation.prob_challenge_root_le` already does for its three hashed strings). The
three lemmas below are the `strHash`-is-itself-hashed analogues of `isSubstring.prob_challenge_root_le`,
`isSubstring.prob_accepts_le` and `isSubstring.sound`, specific to this gadget since it is
currently their only caller. -/

/-- `isSubstring.prob_challenge_root_le`, but with `strHash := HashToField.hashBytesToFieldSpec H
str_vals str_len` substituted — i.e. `str` is hashed by the same `H` the challenge is drawn from,
instead of `strHash` being free. Two hashed vectors now feed the challenge, so the collision bound
is `50 = 2 · 25` instead of `25`. -/
theorem prob_challenge_root_le_hashedStr {n m : ℕ} (str_vals : Vector (ZMod bn254) n)
    (str_len : ZMod bn254) (substr_vals : Vector (ZMod bn254) m) (len start : ZMod bn254)
    {P : Polynomial (ZMod bn254)} (hP : P ≠ 0) {d : ℕ} (hd : P.natDegree ≤ d) :
    randomOracle.toOuterMeasure
      {f | P.eval (isSubstring.challenge (Query.toHashFn f)
             (HashToField.hashBytesToFieldSpec (Query.toHashFn f) str_vals str_len)
             substr_vals len start) = 0} ≤ ((d + 50 : ℕ) : ENNReal) / bn254 := by
  classical
  set vS := HashToField.hashBytesToFieldElems str_vals str_len
  set vT := HashToField.hashBytesToFieldElems substr_vals len
  set c := fun f ↦ isSubstring.challengeQuery f
    (HashToField.hashBytesToFieldSpec (Query.toHashFn f) str_vals str_len) substr_vals len start
  set T := fun f ↦ HashToField.transcript f vS ∪ HashToField.transcript f vT
  have h_sub : {f | P.eval (isSubstring.challenge (Query.toHashFn f)
        (HashToField.hashBytesToFieldSpec (Query.toHashFn f) str_vals str_len)
        substr_vals len start) = 0} ⊆
      {f | c f ∈ T f} ∪ {f | c f ∉ (T f : Set Query) ∧ P.eval (f (c f)) = 0} := by
    intro f hf
    rw [Set.mem_setOf_eq, isSubstring.challenge_toHashFn] at hf
    by_cases h : c f ∈ T f
    · exact Or.inl h
    · exact Or.inr ⟨by simpa using h, hf⟩
  have h_collS : randomOracle.toOuterMeasure {f | c f ∈ HashToField.transcript f vS} ≤ 25 / bn254 :=
    HashToField.challenge_mem_transcript_le vS 0 c (fun f ↦ by
      simp only [c, isSubstring.challengeQuery]
      rw [RandomOracle.coord_hashQ _ (by decide)]
      rfl)
  have h_collT : randomOracle.toOuterMeasure {f | c f ∈ HashToField.transcript f vT} ≤ 25 / bn254 :=
    HashToField.challenge_mem_transcript_le vT 1 c (fun f ↦ by
      simp only [c, isSubstring.challengeQuery]
      rw [RandomOracle.coord_hashQ _ (by decide)]
      rfl)
  have h_coll : randomOracle.toOuterMeasure {f | c f ∈ T f} ≤ 50 / bn254 := by
    have h_eq : {f | c f ∈ T f} = {f | c f ∈ HashToField.transcript f vS} ∪
        {f | c f ∈ HashToField.transcript f vT} := by
      ext f; simp [T, Finset.mem_union]
    rw [h_eq]
    calc randomOracle.toOuterMeasure
            ({f | c f ∈ HashToField.transcript f vS} ∪ {f | c f ∈ HashToField.transcript f vT})
        ≤ randomOracle.toOuterMeasure {f | c f ∈ HashToField.transcript f vS} +
            randomOracle.toOuterMeasure {f | c f ∈ HashToField.transcript f vT} :=
          MeasureTheory.measure_union_le _ _
      _ ≤ 25 / bn254 + 25 / bn254 := add_le_add h_collS h_collT
      _ = 50 / bn254 := by rw [ENNReal.div_add_div_same]; norm_num
  have h_fresh := randomOracle_fresh_le c (fun f ↦ ↑(T f)) (fun _ y ↦ P.eval y = 0) d
    (fun f f' h ↦ by
      have h' : ∀ q ∈ T f, f q = f' q := by simpa using h
      have eS := HashToField.congr vS (fun q hq ↦ h' q (by simp [T, hq]))
      have eT := HashToField.congr vT (fun q hq ↦ h' q (by simp [T, hq]))
      have hS' : HashToField.hashBytesToFieldSpec (Query.toHashFn f) str_vals str_len =
          HashToField.hashBytesToFieldSpec (Query.toHashFn f') str_vals str_len := eS.1
      have hT' : HashToField.hashBytesToFieldSpec (Query.toHashFn f) substr_vals len =
          HashToField.hashBytesToFieldSpec (Query.toHashFn f') substr_vals len := eT.1
      refine ⟨?_, by simp [T, eS.2, eT.2], rfl⟩
      simp only [c, isSubstring.challengeQuery, hS', hT'])
    (fun _ ↦ card_roots_le hP hd)
  calc randomOracle.toOuterMeasure
          {f | P.eval (isSubstring.challenge (Query.toHashFn f)
            (HashToField.hashBytesToFieldSpec (Query.toHashFn f) str_vals str_len)
            substr_vals len start) = 0}
      ≤ randomOracle.toOuterMeasure {f | c f ∈ T f} +
          randomOracle.toOuterMeasure {f | c f ∉ (T f : Set Query) ∧ P.eval (f (c f)) = 0} :=
        (MeasureTheory.measure_mono h_sub).trans (MeasureTheory.measure_union_le _ _)
    _ ≤ 50 / bn254 + (d : ENNReal) / bn254 := add_le_add h_coll h_fresh
    _ = ((d + 50 : ℕ) : ENNReal) / bn254 := by
        rw [ENNReal.div_add_div_same]
        push_cast
        ring_nf

/-- `isSubstring.prob_accepts_le`, but for `strHash := HashToField.hashBytesToFieldSpec H str_vals
str_len` (`str` self-hashed, as in `prob_challenge_root_le_hashedStr`). -/
theorem prob_accepts_le_hashedStr {n m : ℕ} (str_vals : Vector (ZMod bn254) n)
    (str_len : ZMod bn254) (substr_vals : Vector (ZMod bn254) m) (len start : ZMod bn254)
    (h_sn : start.val < n) (h_se : start.val < (start + len).val)
    (h_bad : ¬ isSubstring.SubstrAt str_vals substr_vals start.val len.val) :
    randomOracle.toOuterMeasure
      {f | isSubstring.accepts (Query.toHashFn f) str_vals
             (HashToField.hashBytesToFieldSpec (Query.toHashFn f) str_vals str_len)
             substr_vals len start = true} ≤
      (((n - 1) + (m - 1) + 50 : ℕ) : ENNReal) / bn254 := by
  have h_D : isSubstring.substrDiff str_vals substr_vals start.val (start + len).val ≠ 0 := by
    rw [isSubstring.val_add_of_lt_val h_se, Ne, isSubstring.substrDiff_eq_zero_iff]
    exact h_bad
  refine le_trans (MeasureTheory.measure_mono fun f hf ↦ ?_)
    (prob_challenge_root_le_hashedStr str_vals str_len substr_vals len start h_D
      (isSubstring.natDegree_substrDiff_le _ _ h_sn))
  exact isSubstring.eval_substrDiff_of_accepts h_sn hf

/-- `isSubstring.sound`, but for `strHash := HashToField.hashBytesToFieldSpec H (encodeV n S)
str_len`: `S` (the "haystack") is self-hashed and that hash passed as `strHash`, instead of
`strHash` being a free fixed value. This is the shape `sound` below needs, since both its name-
and value-checks pass `field`'s own hash as `strHash`. The bound is `50`, not `25`, for the reason
given above `prob_challenge_root_le_hashedStr`. -/
theorem sound_hashedStr {n m s : ℕ} {S T : String} (str_len : ZMod bn254)
    (hS : S.length ≤ n) (hT : T.length ≤ m) (hT0 : 0 < T.length) (h_sn : s < n)
    (h_nm : n + m < bn254)
    (hSc : ∀ c ∈ S.toList, c.toNat < 256) (hTc : ∀ c ∈ T.toList, 0 < c.toNat ∧ c.toNat < 256)
    (h_bad : ¬ (s + T.length ≤ S.length ∧ T.toList <+: S.toList.drop s)) :
    randomOracle.toOuterMeasure
      {f | isSubstring.accepts (Query.toHashFn f) (encodeV n S)
             (HashToField.hashBytesToFieldSpec (Query.toHashFn f) (encodeV n S) str_len)
             (encodeV m T) T.length s = true} ≤
      (((n - 1) + (m - 1) + 50 : ℕ) : ENNReal) / bn254 := by
  have h_s : (s : ZMod bn254).val = s := ZMod.val_natCast_of_lt (by omega)
  have h_l : (T.length : ZMod bn254).val = T.length := ZMod.val_natCast_of_lt (by omega)
  have h_e : ((s : ZMod bn254) + (T.length : ZMod bn254)).val = s + T.length := by
    rw [← Nat.cast_add, ZMod.val_natCast_of_lt (by omega)]
  refine prob_accepts_le_hashedStr _ _ _ _ _ (by rwa [h_s]) (by rw [h_s, h_e]; omega) ?_
  rwa [h_s, h_l, isSubstring.substrAt_encodeV_iff (by decide) hS hT hT0 hSc hTc]

/-- `isSubstring.prob_rejects_le`, but with `strHash := HashToField.hashBytesToFieldSpec H str_vals
str_len` substituted, as in `prob_accepts_le_hashedStr`/`prob_challenge_root_le_hashedStr` above.
The bound carries no `(m - 1)` term, same as `isSubstring.prob_rejects_le`: only the window
polynomial (degree at most `n - 1`, independent of `m`) can make the check fail, and
`prob_challenge_root_le_hashedStr` is what supplies the `50` in place of the usual `25`. -/
theorem prob_rejects_le_hashedStr {n m : ℕ} (str_vals : Vector (ZMod bn254) n)
    (str_len : ZMod bn254) (substr_vals : Vector (ZMod bn254) m) (len start : ZMod bn254)
    (h_sn : start.val < n) (h_se : start.val < (start + len).val)
    (h_sub : isSubstring.SubstrAt str_vals substr_vals start.val len.val)
    (h_nz : vecPoly (isSubstring.window str_vals start.val (start + len).val) ≠ 0) :
    randomOracle.toOuterMeasure
      {f | isSubstring.accepts (Query.toHashFn f) str_vals
             (HashToField.hashBytesToFieldSpec (Query.toHashFn f) str_vals str_len)
             substr_vals len start = false} ≤
      (((n - 1) + 50 : ℕ) : ENNReal) / bn254 := by
  refine le_trans (MeasureTheory.measure_mono fun f hf ↦ ?_)
    (prob_challenge_root_le_hashedStr str_vals str_len substr_vals len start h_nz
      (natDegree_vecPoly_le _))
  rw [Set.mem_setOf_eq, eval_vecPoly]
  by_contra h0
  have := isSubstring.accepts_of_substrAt (H := Query.toHashFn f)
    (strHash := HashToField.hashBytesToFieldSpec (Query.toHashFn f) str_vals str_len)
    h_sn h_se h_sub h0
  exact Bool.false_ne_true (hf.symm.trans this)

/-- `isSubstring.complete`, but for `strHash := HashToField.hashBytesToFieldSpec H (encodeV n S)
str_len`: `S` (the "haystack") is self-hashed and that hash passed as `strHash`, instead of
`strHash` being a free fixed value. This is the shape `complete` below needs, since both its
name- and value-checks pass `field`'s own hash as `strHash`. The bound is `50`, not `25`, for the
reason given above `prob_challenge_root_le_hashedStr`. -/
theorem complete_hashedStr {n m s : ℕ} {S T : String} (str_len : ZMod bn254)
    (hS : S.length ≤ n) (hT : T.length ≤ m) (hT0 : 0 < T.length)
    (h_nm : n + m < bn254)
    (hSc : ∀ c ∈ S.toList, c.toNat < 256)
    (hTc : ∀ c ∈ T.toList, 0 < c.toNat ∧ c.toNat < 256)
    (h_fit : s + T.length ≤ S.length)
    (h_pre : T.toList <+: S.toList.drop s) :
    randomOracle.toOuterMeasure
      {f | isSubstring.accepts (Query.toHashFn f) (encodeV n S)
             (HashToField.hashBytesToFieldSpec (Query.toHashFn f) (encodeV n S) str_len)
             (encodeV m T) T.length s = false} ≤
      (((n - 1) + 50 : ℕ) : ENNReal) / bn254 := by
  have h256 : 256 < bn254 := by decide
  have h_s : (s : ZMod bn254).val = s := ZMod.val_natCast_of_lt (by omega)
  have h_l : (T.length : ZMod bn254).val = T.length := ZMod.val_natCast_of_lt (by omega)
  have h_e : ((s : ZMod bn254) + (T.length : ZMod bn254)).val = s + T.length := by
    rw [← Nat.cast_add, ZMod.val_natCast_of_lt (by omega)]
  have h_sub := (isSubstring.substrAt_encodeV_iff (p := bn254) (n := n) (m := m) (s := s) h256 hS
    hT hT0 hSc hTc).mpr ⟨h_fit, h_pre⟩
  refine prob_rejects_le_hashedStr _ str_len _ _ _ (by rw [h_s]; omega) (by rw [h_s, h_e]; omega)
    (by rwa [h_s, h_l]) ?_
  -- The window's coefficient at `s` is `T`'s first character.
  rw [h_s, h_e]
  intro h0
  have h_coeff := congrArg (fun P ↦ Polynomial.coeff P s) h0
  simp only [coeff_vecPoly, Polynomial.coeff_zero,
    isSubstring.ext_window _ (show s ≤ s + T.length by omega)] at h_coeff
  rw [if_pos (⟨le_refl s, by omega⟩ : s ≤ s ∧ s < s + T.length)] at h_coeff
  have h_at := h_sub s
  rw [if_pos (⟨le_refl s, by omega⟩ : s ≤ s ∧ s < s + T.length), if_pos (le_refl s),
    Nat.sub_self] at h_at
  have hT0' : 0 < T.toList.length := by rw [String.length_toList]; exact hT0
  obtain ⟨hc0, hc1⟩ := hTc _ (List.getElem_mem hT0')
  rw [h_at, ext_encodeV hT, dif_pos hT0', toUInt8_toNat_of_lt hc1] at h_coeff
  have := natCast_inj (p := bn254) (a := (T.toList[0]'hT0').toNat) (b := 0) (by omega)
    (by omega) (by rw [Nat.cast_zero]; exact h_coeff)
  omega

/-- Reads a character's byte out of `(encodeV w S).getD i 0`, when `i` is in bounds for both `w`
and `S` — the `getD` counterpart of `encodeV_getElem_of_lt`, needed because `complete` below
reasons about specific literal offsets in `field` via `Vector.getD`/`List.getD` (no index-bound
proof terms to carry through the string-append rewriting). -/
lemma encodeV_getD_of_lt {w i : ℕ} {S : String} (hw : i < w) (hs : i < S.toList.length) :
    (encodeV (p := bn254) w S).getD i 0 =
      (((S.toList.getD i default).toUInt8.toNat : ℕ) : ZMod bn254) := by
  rw [show (encodeV (p := bn254) w S).getD i 0 = (encodeV (p := bn254) w S)[i]'hw from by
    simp [Vector.getD, hw]]
  rw [encodeV_getElem_of_lt hw hs, show S.toList[i]'hs = S.toList.getD i default from by
    simp [List.getD_eq_getElem?_getD, hs]]

end parseJWTFieldSharedLogic
