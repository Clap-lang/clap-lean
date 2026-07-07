import Clap.Lang
import Clap.Wheels

namespace FArray

open Clap.Lang

variable {p : ℕ} [Fact (Nat.Prime p)]

/-- Computes a candidate one-hot mask: position `i` is `isZero(idx - i)`. -/
private def oneHotRaw (len : ℕ) (idx : F p) : Option (Vector (FB p) len) :=
  (Vector.range len).mapM (fun (i:ℕ) ↦ F.eq idx i)

/-- Returns a one-hot bit mask of length `len` with a 1 at index `idx` and 0s elsewhere. Only satisfiable when `0 ≤ idx < len`. -/
def singleOneArray (len : ℕ) (idx : F p) : Option (Vector (FB p) len) := do
  let out ← oneHotRaw len idx
  let s : F p := out.foldl (fun acc b ↦ acc + b) 0
  F.assert_eq s 1
  return out

/-- (SingleNegOneArray) Returns a one-hot bit mask of length `len` with a 1 at index `idx` and 0s elsewhere.
    Returns all zeros when `idx ≥ len`. -/
private def singleEndArray (len : ℕ) (idx : F p) : Option (Vector (FB p) len) := do
  let out ← oneHotRaw len idx
  let s : F p := out.foldl (fun acc b ↦ acc + b) 0
  F.assert_eq s (s * s) -- s² = s (at most one-hot)
  return out

/-- Outputs a bit array with 1s at `[startIdx, endIdx)` and 0s elsewhere.
    Satisfiable when `startIdx < endIdx` and `startIdx < len`. If `endIdx ≥ len`, the bit array has 1s at `[startIdx, len)`. -/
def arraySelector (len : ℕ) (startIdx endIdx : F p) : Option (Vector (FB p) len) := do
  let w := Clap.minBits len
  assert! w ≤ Clap.minBits p
  FB.assert (← F.lessThan w startIdx endIdx)
  let startMask ← singleOneArray len startIdx
  let endMask ← singleEndArray len endIdx
  -- Per CIRCOM ArraySelector: +1 at startIdx, -1 at endIdx (singleEndArray returns +1, so subtract).
  let combined := startMask.zipWith (· - ·) endMask
  -- Inclusive prefix sum of `combined` ⇒ 1s exactly on [startIdx, endIdx).
  -- `Vector.scanl` is exclusive (Σ_{j<i}), so add each element back to make it inclusive.
  return (combined.scanl (· + ·) 0).zipWith (· + ·) combined

/-- Returns the element of `arr` at index `idx`. Fails when `idx ≥ len`. -/
def selectArrayValue {len : ℕ} (arr : Vector (F p) len) (idx : F p) : Option (F p) := do
  let hot ← singleOneArray len idx
  return F.dotProduct hot arr

/-- Outputs a bit array with 1s at `[0, idx)` and 0s at `[idx, len)`. Only satisfiable when `0 ≤ idx < len`. Requires `len > 0`. -/
private def leftArraySelector (len : ℕ) (idx : F p) : Option (Vector (FB p) len) := do
  let bits ← singleOneArray len idx
  return bits.scanr (· + ·) 0

/-- Outputs a bit array with 0s at `[0, idx]` and 1s at `(idx, len)`. Only satisfiable when `0 ≤ idx < len`. -/
def rightArraySelector (len : ℕ) (idx : F p) : Option (Vector (FB p) len) := do
  let bits ← singleOneArray len idx
  return bits.scanl (· + ·) 0

/-- Like `arraySelector`, but returns all zeros when `endIdx ≤ startIdx`. Does not work when `startIdx = 0`. -/
def arraySelectorComplex (len : ℕ) (startIdx endIdx : F p) : Option (Vector (FB p) len) := do
  FB.assert (FB.not (←isZero startIdx))
  let right ← rightArraySelector len (startIdx - 1)
  let left ← leftArraySelector len endIdx
  return right.zipWith (· * ·) left


omit [Fact (Nat.Prime p)] in
/-- Induction lemma for the prefix fold that builds the `arraySelector` output:
    starting from `false`, OR-ing in a `1` only at position `0`, and AND-ing with
    `¬(position = e)`, the fold over positions `[0, j]` equals `j < e`. -/
lemma selector_fold_aux {len : ℕ} (e : ℕ) (he : 0 < e) :
    ∀ (j : ℕ), j < len →
      ((List.finRange len).take (j + 1)).foldl
        (fun (prev : FB p) (i : Fin len) =>
          FB.and (FB.or prev (FB.ofBool (i.val = 0))) (FB.not (FB.ofBool (e = i.val))))
        FB.false
      = FB.ofBool (j < e) := by
  intro j;
  induction j <;> simp_all +decide [ List.take_add_one ];
  · simp +decide [ FB.false, FB.ofBool, FB.and, FB.or ];
    simp +decide [ FB.true, FB.not ];
    aesop;
  · rename_i k hk;
    intro hk';
    convert congr_arg ( fun x : FB p => ( x.or ( FB.ofBool ( decide ( k + 1 = 0 ) ) ) ).and ( FB.ofBool !decide ( e = k + 1 ) ) ) ( hk ( Nat.lt_of_succ_lt hk' ) ) using 1;
    · sorry
    · simp +decide [ FB.ofBool, FB.or, FB.and ];
      split_ifs <;> simp_all +decide [ FB.true, FB.false ];
      · linarith;
      · omega

/-
`oneHotRaw len idx` is the vector whose `i`-th entry is `1` iff `idx = i` in the field.
-/
lemma oneHotRaw_eq {len : ℕ} (idx : F p) :
    oneHotRaw len idx =
      some (Vector.ofFn fun i : Fin len => FB.ofBool (idx = (i.val : F p))) := by
  unfold oneHotRaw; simp +decide [ F.eq ] ;
  convert Vector.mapM_pure _ using 2;
  rotate_right;
  use fun i => FB.ofBool (idx = i);
  · ext i; simp +decide [ isZero, FB.ofBool ] ;
    split_ifs <;> simp_all +decide [ sub_eq_zero ]; all_goals exact Eq.congr_right rfl;
  · ext i; simp +decide [ Vector.getElem_ofFn ] ;
  · infer_instance

/-
`singleOneArray len 0` is the one-hot vector with a single `1` at position `0`,
    provided `0 < len ≤ p`.
-/
lemma singleOneArray_zero_eq {len : ℕ} (hlen : 0 < len) (hp : len ≤ p) :
    singleOneArray len (0 : F p) =
      some (Vector.ofFn fun i : Fin len => FB.ofBool (i.val = 0)) := by
  convert Option.bind_congr ?_;
  rotate_left;
  exact fun a => if Vector.foldl ( fun acc b => acc + b ) 0 a = 1 then some a else none;
  · simp +decide [ F.assert_eq, eq0 ];
    grind;
  · rw [ oneHotRaw_eq ];
    simp +decide [ Vector.foldl, Vector.ofFn ];
    induction hlen <;> simp_all +decide [ Array.ofFn_succ ];
    · rfl;
    · rename_i k hk ih; specialize ih ( by linarith ) ; simp_all +decide [ eq_comm ] ;
      simp_all +decide [ Fin.ext_iff, ZMod.natCast_eq_zero_iff ];
      simp_all +decide [ Nat.dvd_iff_mod_eq_zero, Nat.mod_eq_of_lt hp ];
      cases k <;> aesop

/-
`singleEndArray len endIdx`, when `endIdx.val < len ≤ p`, is the one-hot vector
    with a single `1` at position `endIdx.val`.
-/
lemma singleEndArray_lt_eq {len : ℕ} (endIdx : F p)
    (hlt : endIdx.val < len) (hp : len ≤ p) :
    singleEndArray len endIdx =
      some (Vector.ofFn fun i : Fin len => FB.ofBool (endIdx.val = i.val)) := by
  -- By definition of `singleEndArray`, we know that it is equal to the vector of ones at the position `endIdx.val`.
  have h_singleEndArray_eq : singleEndArray len endIdx = some (Vector.ofFn fun i : Fin len => FB.ofBool (endIdx = (i.val : F p))) := by
    rw [singleEndArray, oneHotRaw_eq];
    -- Since `endIdx.val < len`, there is exactly one index `i` such that `endIdx.val = i.val`.
    have h_unique : ∃! i : Fin len, endIdx.val = i.val := by
      exact ⟨ ⟨ endIdx.val, hlt ⟩, rfl, fun i hi => Fin.ext hi.symm ⟩;
    obtain ⟨ i, hi, hiu ⟩ := h_unique;
    have h_sum : (Vector.foldl (fun acc b => acc + b) 0 (Vector.ofFn fun i : Fin len => FB.ofBool (decide (endIdx = (i.val : F p)))) : F p) = 1 := by
      have h_sum : (Vector.foldl (fun acc b => acc + b) 0 (Vector.ofFn (fun i : Fin len => FB.ofBool (endIdx = (i.val : F p)))) : F p) = ∑ j : Fin len, FB.ofBool (endIdx = (j.val : F p)) := by
        simp +decide [ Vector.foldl, Finset.sum ];
        rw [ List.sum_eq_foldl ];
        rw [ Array.foldl_toList ];
        grind;
      rw [ h_sum, Finset.sum_eq_single i ] <;> simp_all +decide [ ZMod.natCast_zmod_val ];
      · rw [ ← hi, ZMod.natCast_zmod_val ] ; aesop;
      · intro j hj; contrapose! hj; simp_all +decide [ ZMod.natCast_zmod_val ] ;
        by_cases h : endIdx = j.val <;> simp_all +decide [ FB.ofBool ];
        · exact hiu j ( by rw [ ← hi, Nat.mod_eq_of_lt ( show ( j : ℕ ) < p from lt_of_lt_of_le j.2 hp ) ] );
        · exact False.elim <| hj <| by rfl;
    simp +decide [ h_sum, F.assert_eq ];
    unfold eq0; aesop;
  convert h_singleEndArray_eq;
  constructor <;> intro h <;> rw [ ← ZMod.natCast_zmod_val endIdx ] at * <;> simp_all +decide [ ZMod.natCast_eq_natCast_iff' ];
  exact Nat.mod_eq_of_lt ( lt_of_lt_of_le ( Fin.is_lt _ ) hp )
/-
Characterization of `arraySelector` with `startIdx = 0`: the result selects
    exactly the positions `[0, endIdx.val)`.
-/
lemma arraySelector_zero_eq {len : ℕ} (endIdx : F p)
    (h0 : 0 < endIdx.val) (hlt : endIdx.val < len)
    (hfits : Clap.minBits len ≤ Clap.minBits p)
    (hw : 2 ^ (Clap.minBits len + 1) < p) :
    arraySelector len 0 endIdx =
      some (Vector.ofFn fun i : Fin len => FB.ofBool (i.val < endIdx.val)) := by
  convert Option.some_inj.mpr ( Vector.ext fun i => ?_ ) using 1;
  rotate_left;
  exact Vector.ofFn fun i : Fin len => ( List.finRange len |> List.take ( i.val + 1 ) |> List.foldl ( fun prev i => FB.and ( FB.or prev ( FB.ofBool ( i.val = 0 ) ) ) ( FB.not ( FB.ofBool ( endIdx.val = i.val ) ) ) ) FB.false );
  · convert selector_fold_aux ( endIdx.val ) h0 i using 1;
    rw [ Vector.getElem_ofFn, Vector.getElem_ofFn ];
  · rw [arraySelector];
    rw [ Spec.F.lessThan_equiv ];
    · rw [ singleOneArray_zero_eq, singleEndArray_lt_eq ];
      · simp +decide [ FB.assert ];
        rw [ if_pos hfits, eq0 ];
        rw [ if_pos ];
        · sorry
        · sorry
      · exact hlt;
      · exact le_trans ( Nat.le_of_lt ( Clap.minBits_lt_two_pow len ) ) ( Nat.le_of_lt ( lt_of_le_of_lt ( Nat.pow_le_pow_right ( by decide ) ( Nat.le_succ _ ) ) hw ) );
      · grind;
      · exact le_trans ( Nat.le_of_lt ( Clap.minBits_lt_two_pow len ) ) ( Nat.le_of_lt ( lt_of_le_of_lt ( Nat.pow_le_pow_right ( by decide ) ( Nat.le_succ _ ) ) hw ) );
    · exact ZMod.val_zero.trans_lt ( pow_pos ( by decide ) _ );
    · exact hlt.trans_le ( Nat.le_of_lt ( Clap.minBits_lt_two_pow len ) );
    · exact hw

end FArray

-- We have all ingredients to specify  arraySelector. We have the specs for F.lessThan, singleOneArray and singleEndArray.
namespace Spec.FArray

open Clap.Lang

variable {p : ℕ}

/-- `true` exactly at position `i`, `false` everywhere else -/
def singleOneArray_spec (len i : ℕ) : Vector Bool len :=
  Vector.ofFn (fun j => decide ((j : ℕ) = i))

private lemma oneHotRaw_eq [Fact (Nat.Prime p)] (len : ℕ) (idx : F p) :
    FArray.oneHotRaw len idx
      = some (Vector.ofFn (fun j : Fin len => if idx = ((j : ℕ) : F p) then (1 : FB p) else 0)) := by
  have hf : (fun (i : ℕ) => F.eq idx (i : F p))
      = (fun i : ℕ => (pure (if idx = (i : F p) then (1 : FB p) else 0) : Option (FB p))) := by
    funext i
    rw [F.eq, F.isZero_def]
    simp only [sub_eq_zero]
    rfl
  unfold FArray.oneHotRaw
  rw [hf, Vector.mapM_pure]
  show some _ = some _
  congr 1
  apply Vector.ext
  intro i hi
  simp [Vector.getElem_map, Vector.getElem_range, Vector.getElem_ofFn]

private lemma spec_map_eq [Fact (Nat.Prime p)] (len : ℕ) (idx : F p) (hlen : len ≤ p) :
    (singleOneArray_spec len idx.val).map (FB.ofBool (p := p))
      = Vector.ofFn (fun j : Fin len => if idx = ((j : ℕ) : F p) then (1 : FB p) else 0) := by
  haveI : NeZero p := ⟨(Fact.out : Nat.Prime p).pos.ne'⟩
  apply Vector.ext
  intro i hi
  simp only [singleOneArray_spec, Vector.getElem_map, Vector.getElem_ofFn]
  by_cases h : (i : ℕ) = idx.val
  · have hQ : idx = (i : F p) := by rw [h, ZMod.natCast_zmod_val]
    rw [if_pos hQ]
    simp [FB.ofBool, FB.true, h]
  · have hQ : idx ≠ (i : F p) := by
      intro hc
      apply h
      have hiv : (((i : ℕ)) : F p).val = i := ZMod.val_natCast_of_lt (lt_of_lt_of_le hi hlen)
      rw [← hiv, ← hc]
    rw [if_neg hQ]
    simp [FB.ofBool, FB.false, h]

/-- **Refinement.** When `idx` is a valid in-range index (`idx.val < len`, with
    `len ≤ p` so distinct positions `j < len` have distinct field encodings `↑j`),
    `singleOneArray` returns the one-hot mask at `idx`.

    Proof outline (pending): `oneHotRaw` always succeeds with
    `out[j] = if idx = ↑j then 1 else 0`; in range exactly one `j` (namely
    `idx.val`) matches, so `Σ out = 1` and the final `F.assert_eq s 1` succeeds
    (`Spec.F.assert_eq_spec`); a `Vector.ext` + `ZMod.val_natCast_of_lt` identifies
    `out` with the encoded spec. -/
lemma singleOneArray_equiv [Fact (Nat.Prime p)] (len : ℕ) (idx : F p)
    (hidx : idx.val < len) (hlen : len ≤ p) :
    FArray.singleOneArray len idx
      = some ((singleOneArray_spec len idx.val).map (FB.ofBool (p := p))) := by
  haveI : NeZero p := ⟨(Fact.out : Nat.Prime p).pos.ne'⟩
  have hs : (Vector.ofFn (fun j : Fin len => if idx = ((j : ℕ) : F p) then (1 : FB p) else 0)).foldl
      (· + ·) 0 = (1 : F p) := by
    rw [Spec.F.ofFn_foldl_add]
    refine (Finset.sum_eq_single (⟨idx.val, hidx⟩ : Fin len) ?_ ?_).trans ?_
    · intro b _ hb
      apply if_neg
      intro hc
      apply hb
      apply Fin.ext
      show (b : ℕ) = idx.val
      have hbv : (((b : ℕ)) : F p).val = (b : ℕ) :=
        ZMod.val_natCast_of_lt (lt_of_lt_of_le b.isLt hlen)
      rw [← hbv, ← hc]
    · intro hcon
      exact absurd (Finset.mem_univ _) hcon
    · exact if_pos (ZMod.natCast_zmod_val idx).symm
  have ha : F.assert_eq (1 : F p) 1 = some () := by
    rw [Spec.F.assert_eq_eq_ite, if_pos rfl]
  unfold FArray.singleOneArray
  rw [oneHotRaw_eq]
  simp only [bind, Option.bind, hs, ha, pure]
  rw [spec_map_eq len idx hlen]

/-- **Out of range.** When `idx` is not a valid index (`len ≤ idx.val`, with
    `len ≤ p`), `singleOneArray` is unsatisfiable: no position matches, so
    `Σ out = 0 ≠ 1` and the `F.assert_eq` fails. Captures the "only satisfiable
    when `0 ≤ idx < LEN`" half of the CIRCOM contract. -/
lemma singleOneArray_none [Fact (Nat.Prime p)] (len : ℕ) (idx : F p)
    (hlen : len ≤ p) (hidx : len ≤ idx.val) :
    FArray.singleOneArray len idx = none := by
  haveI : NeZero p := ⟨(Fact.out : Nat.Prime p).pos.ne'⟩
  have hs : (Vector.ofFn (fun j : Fin len => if idx = ((j : ℕ) : F p) then (1 : FB p) else 0)).foldl
      (· + ·) 0 = (0 : F p) := by
    rw [Spec.F.ofFn_foldl_add]
    apply Finset.sum_eq_zero
    intro b _
    apply if_neg
    intro hc
    have hbv : (((b : ℕ)) : F p).val = (b : ℕ) :=
      ZMod.val_natCast_of_lt (lt_of_lt_of_le b.isLt hlen)
    have hval : idx.val = (b : ℕ) := by rw [hc]; exact hbv
    have hbl : (b : ℕ) < len := b.isLt
    omega
  have ha : F.assert_eq (0 : F p) 1 = none := by
    rw [Spec.F.assert_eq_eq_ite]
    simp
  unfold FArray.singleOneArray
  rw [oneHotRaw_eq]
  simp only [bind, Option.bind, hs, ha, pure]

/-- `singleEndArray` computes the same mask as `singleOneArray`: one-hot in range, all-zeros out of range. The circuits differ only in
    satisfiability: `singleOneArray` requires exactly one hot bit (`Σ = 1`), while
    `singleEndArray` requires only at most one (`Σ = Σ²`), so it also accepts the out-of-range (all-zeros) case. -/
def singleEndArray_spec (len i : ℕ) : Vector Bool len := singleOneArray_spec len i

/-- The number of positions `j ∈ [0, len)` whose field encoding `↑j` equals `idx`.
    The field sum `singleEndArray` folds is exactly this count, cast into `F p`. -/
def matchCount (len : ℕ) (idx : F p) : ℕ :=
  (Finset.univ.filter (fun j : Fin len => idx = ((j : ℕ) : F p))).card

/-- The raw `+1` indicator mask `oneHotRaw` builds: `1` at *every* matching position.
    Coincides with the one-hot `singleOneArray_spec` exactly when `len ≤ p` (at most
    one match); for `len > p` it can have several `1`s, one per modular collision. -/
def endMask (len : ℕ) (idx : F p) : Vector (FB p) len :=
  Vector.ofFn (fun j => if idx = ((j : ℕ) : F p) then (1 : FB p) else 0)

/-- `singleEndArray` returns the indicator
    `endMask` exactly when the match count, cast into `F p`, is `0` or `1` (the
    `Σ = Σ²` check); otherwise it is unsatisfiable. Holds for every `len`, `idx`. -/
theorem singleEndArray_total [Fact (Nat.Prime p)] (len : ℕ) (idx : F p) :
    FArray.singleEndArray len idx
      = if (matchCount len idx : F p) = 0 ∨ (matchCount len idx : F p) = 1
        then some (endMask len idx) else none := by
  -- The folded sum is exactly the (cast) match count.
  have hsum : (Vector.ofFn (fun j : Fin len => if idx = ((j : ℕ) : F p) then (1 : FB p) else 0)).foldl
      (· + ·) 0 = (matchCount len idx : F p) := by
    rw [Spec.F.ofFn_foldl_add, Finset.sum_boole]; rfl
  unfold endMask
  unfold FArray.singleEndArray
  rw [oneHotRaw_eq]
  by_cases hc : (matchCount len idx : F p) = 0 ∨ (matchCount len idx : F p) = 1
  · rw [if_pos hc]
    have hss : (Vector.ofFn (fun j : Fin len => if idx = ((j : ℕ) : F p) then (1 : FB p) else 0)).foldl (· + ·) 0
        = (Vector.ofFn (fun j : Fin len => if idx = ((j : ℕ) : F p) then (1 : FB p) else 0)).foldl (· + ·) 0 *
          (Vector.ofFn (fun j : Fin len => if idx = ((j : ℕ) : F p) then (1 : FB p) else 0)).foldl (· + ·) 0 := by
      rw [hsum]; rcases hc with h0 | h1
      · rw [h0]; ring
      · rw [h1]; ring
    have ha : F.assert_eq
        ((Vector.ofFn (fun j : Fin len => if idx = ((j : ℕ) : F p) then (1 : FB p) else 0)).foldl (· + ·) 0)
        ((Vector.ofFn (fun j : Fin len => if idx = ((j : ℕ) : F p) then (1 : FB p) else 0)).foldl (· + ·) 0 *
         (Vector.ofFn (fun j : Fin len => if idx = ((j : ℕ) : F p) then (1 : FB p) else 0)).foldl (· + ·) 0)
        = some () := by rw [Spec.F.assert_eq_eq_ite, if_pos hss]
    simp only [bind, Option.bind, ha, pure]
  · rw [if_neg hc]
    have hss : ¬ ((Vector.ofFn (fun j : Fin len => if idx = ((j : ℕ) : F p) then (1 : FB p) else 0)).foldl (· + ·) 0
        = (Vector.ofFn (fun j : Fin len => if idx = ((j : ℕ) : F p) then (1 : FB p) else 0)).foldl (· + ·) 0 *
          (Vector.ofFn (fun j : Fin len => if idx = ((j : ℕ) : F p) then (1 : FB p) else 0)).foldl (· + ·) 0) := by
      rw [hsum]
      intro h
      apply hc
      have hz : (matchCount len idx : F p) * ((matchCount len idx : F p) - 1) = 0 := by
        rw [mul_sub, mul_one, ← h, sub_self]
      rcases mul_eq_zero.mp hz with h0 | h1
      · exact Or.inl h0
      · exact Or.inr (sub_eq_zero.mp h1)
    have ha : F.assert_eq
        ((Vector.ofFn (fun j : Fin len => if idx = ((j : ℕ) : F p) then (1 : FB p) else 0)).foldl (· + ·) 0)
        ((Vector.ofFn (fun j : Fin len => if idx = ((j : ℕ) : F p) then (1 : FB p) else 0)).foldl (· + ·) 0 *
         (Vector.ofFn (fun j : Fin len => if idx = ((j : ℕ) : F p) then (1 : FB p) else 0)).foldl (· + ·) 0)
        = none := by rw [Spec.F.assert_eq_eq_ite, if_neg hss]
    simp only [bind, Option.bind, ha]

/-- For `len ≤ p` the raw `endMask` is exactly the one-hot Bool spec encoded. -/
lemma endMask_eq [Fact (Nat.Prime p)] (len : ℕ) (idx : F p) (hlen : len ≤ p) :
    endMask len idx = (singleOneArray_spec len idx.val).map (FB.ofBool (p := p)) := by
  unfold endMask
  exact (spec_map_eq len idx hlen).symm

/-- For `len ≤ p` distinct positions have distinct encodings, so at most one matches. -/
lemma matchCount_le_one [Fact (Nat.Prime p)] (len : ℕ) (idx : F p) (hlen : len ≤ p) :
    matchCount len idx ≤ 1 := by
  haveI : NeZero p := ⟨(Fact.out : Nat.Prime p).pos.ne'⟩
  rw [matchCount, Finset.card_le_one]
  intro a ha b hb
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  apply Fin.ext
  have hav : (((a : ℕ)) : F p).val = (a : ℕ) := ZMod.val_natCast_of_lt (lt_of_lt_of_le a.isLt hlen)
  have hbv : (((b : ℕ)) : F p).val = (b : ℕ) := ZMod.val_natCast_of_lt (lt_of_lt_of_le b.isLt hlen)
  have heq : ((a : ℕ) : F p) = ((b : ℕ) : F p) := by rw [← ha, ← hb]
  have hv := congrArg ZMod.val heq
  rwa [hav, hbv] at hv

/-- **(`len ≤ p`).** Corollary of `singleEndArray_total`: in the real
    parameter regime the match count is `0` or `1`, so the circuit always succeeds,
    returning the one-hot Bool spec. (No `idx.val < len` hypothesis needed.) -/
lemma singleEndArray_equiv [Fact (Nat.Prime p)] (len : ℕ) (idx : F p) (hlen : len ≤ p) :
    FArray.singleEndArray len idx
      = some ((singleEndArray_spec len idx.val).map (FB.ofBool (p := p))) := by
  have hcond : (matchCount len idx : F p) = 0 ∨ (matchCount len idx : F p) = 1 := by
    obtain h0 | h1 : matchCount len idx = 0 ∨ matchCount len idx = 1 :=
      by have := matchCount_le_one len idx hlen; omega
    · exact Or.inl (by rw [h0, Nat.cast_zero])
    · exact Or.inr (by rw [h1, Nat.cast_one])
  rw [singleEndArray_total, if_pos hcond, endMask_eq len idx hlen, singleEndArray_spec]

/-- **(`len > p`).** Corollary of `singleEndArray_total`: whenever the
    match count lands strictly between `1` and `p` (`2 ≤ m < p`) — e.g. the `len > p`
    modular-collision regime, `singleEndArray (p := 11) 12 0 = none` — the count is
    neither `0` nor `1` in `F p`, so the `Σ = Σ²` check fails. The remaining work for
    a concrete instance is computing `matchCount` (often `native_decide`-able). -/
lemma singleEndArray_none_of_matchCount [Fact (Nat.Prime p)] (len : ℕ) (idx : F p)
    (h2 : 2 ≤ matchCount len idx) (hlt : matchCount len idx < p) :
    FArray.singleEndArray len idx = none := by
  haveI : NeZero p := ⟨(Fact.out : Nat.Prime p).pos.ne'⟩
  rw [singleEndArray_total, if_neg]
  rintro (h0 | h1)
  · have hdvd : p ∣ matchCount len idx := (ZMod.natCast_eq_zero_iff _ _).mp h0
    have : matchCount len idx = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hlt
    omega
  · have hm1 : ((matchCount len idx : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
      rw [Nat.cast_one]; exact h1
    have hmod : matchCount len idx ≡ 1 [MOD p] := (ZMod.natCast_eq_natCast_iff _ _ _).mp hm1
    rw [Nat.ModEq, Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by omega : 1 < p)] at hmod
    omega

/-- **Level 1 spec.** `arraySelector` outputs the indicator of the half-open
    interval `[startIdx, endIdx)`: bit `i` is `true` iff `startIdx ≤ i < endIdx`.
    (`endIdx ≥ len` is clamped automatically since every `i < len`.) -/
def arraySelector_spec (len startIdx endIdx : ℕ) : Vector Bool len :=
  Vector.ofFn (fun i => decide (startIdx ≤ (i : ℕ) ∧ (i : ℕ) < endIdx))

/-- Bridge: the sum of the first `i` entries of a list is the `Finset.range` sum of
    its indexed entries. -/
private lemma list_sum_take_eq_sum_range {β : Type} [AddCommMonoid β] [Inhabited β]
    (L : List β) : ∀ (i : ℕ), i ≤ L.length → (L.take i).sum = ∑ j ∈ Finset.range i, L[j]! := by
  intro i
  induction i with
  | zero => intro _; simp
  | succ i ih =>
    intro hi
    have hii : i < L.length := hi
    rw [List.take_add_one, List.sum_append, ih (Nat.le_of_lt hii), Finset.sum_range_succ,
        getElem!_pos L i hii]
    simp [List.getElem?_eq_getElem hii]

/-- **Refinement.** When `startIdx` is in range (`startIdx.val < len`), both indices
    fit in `minBits len` bits (`hstart`/`hend`), `startIdx.val < endIdx.val`, and the
    field is large enough, `arraySelector` returns the encoded interval indicator. -/
lemma arraySelector_equiv [Fact (Nat.Prime p)] (len : ℕ) (startIdx endIdx : F p)
    (hlen : len ≤ p) (hstart : startIdx.val < len)
    (hlt : startIdx.val < endIdx.val)
    (hend : endIdx.val < 2 ^ Clap.minBits len)
    (hw : 2 ^ (Clap.minBits len + 1) < p) :
    FArray.arraySelector len startIdx endIdx
      = some ((arraySelector_spec len startIdx.val endIdx.val).map (FB.ofBool (p := p))) := by
  haveI : NeZero p := ⟨(Fact.out : Nat.Prime p).pos.ne'⟩
  have hsw : startIdx.val < 2 ^ Clap.minBits len :=
    lt_of_lt_of_le hstart (le_of_lt (Clap.lt_two_pow_minBits len))
  have hwp : Clap.minBits len ≤ Clap.minBits p := Clap.minBits_mono hlen
  have hlteq : F.lessThan (Clap.minBits len) startIdx endIdx
      = some (FB.ofBool (startIdx.val < endIdx.val)) :=
    Spec.F.lessThan_equiv startIdx endIdx hsw hend hw
  have hassert : FB.assert (FB.ofBool (p := p) (startIdx.val < endIdx.val)) = some () := by
    rw [Spec.FB.assert_equiv _ (Spec.FB.valid_ofBool _), Spec.FB.left_inv]
    simp [Spec.FB.assert, hlt]
  have hsm := singleOneArray_equiv len startIdx hstart hlen
  have hem := singleEndArray_equiv len endIdx hlen
  set encS := (singleOneArray_spec len startIdx.val).map (FB.ofBool (p := p)) with hencS
  set encE := (singleEndArray_spec len endIdx.val).map (FB.ofBool (p := p)) with hencE
  -- reduce the do-block
  unfold FArray.arraySelector
  simp only [hwp, if_true, hlteq, bind, Option.bind, hassert, hsm, hem, pure]
  set combined := encS.zipWith (· - ·) encE with hcomb
  congr 1
  apply Vector.ext
  intro i hi
  -- `combined` at any in-range position: +1 at startIdx, -1 at endIdx
  have hval : ∀ j : ℕ, j < len → combined.toList[j]!
      = (if j = startIdx.val then (1 : FB p) else 0)
        - (if j = endIdx.val then (1 : FB p) else 0) := by
    intro j hj
    rw [getElem!_pos combined.toList j (by rw [Vector.length_toList]; exact hj),
        Vector.getElem_toList]
    simp only [hcomb, hencS, hencE, Vector.getElem_zipWith, Vector.getElem_map,
      singleOneArray_spec, singleEndArray_spec, Vector.getElem_ofFn, FB.ofBool,
      FB.true, FB.false, decide_eq_true_eq]
  -- output at `i` is the inclusive prefix sum of `combined` up to `i`
  rw [Vector.getElem_zipWith, Vector.getElem_scanl_add combined i hi]
  have hci : combined[i] = combined.toList[i]! := by
    rw [getElem!_pos combined.toList i (by rw [Vector.length_toList]; exact hi),
        Vector.getElem_toList]
  rw [list_sum_take_eq_sum_range combined.toList i (by rw [Vector.length_toList]; omega),
      hci, ← Finset.sum_range_succ,
      Finset.sum_congr rfl (fun j hj => hval j (by have := Finset.mem_range.mp hj; omega))]
  simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_range,
    arraySelector_spec, Vector.getElem_map, Vector.getElem_ofFn, FB.ofBool, FB.true,
    FB.false, decide_eq_true_eq]
  by_cases h1 : startIdx.val ≤ i
  · by_cases h2 : i < endIdx.val
    · rw [if_pos (show startIdx.val < i + 1 by omega),
          if_neg (show ¬ endIdx.val < i + 1 by omega), if_pos ⟨h1, h2⟩]; ring
    · rw [if_pos (show startIdx.val < i + 1 by omega),
          if_pos (show endIdx.val < i + 1 by omega), if_neg (fun h => h2 h.2)]; ring
  · by_cases h2 : i < endIdx.val
    · rw [if_neg (show ¬ startIdx.val < i + 1 by omega),
          if_neg (show ¬ endIdx.val < i + 1 by omega), if_neg (fun h => h1 h.1)]; ring
    · exfalso; omega

/-- **Level 2 spec.** Same indicator, phrased as membership in the half-open
    interval `Finset.Ico startIdx endIdx`. -/
def arraySelector_high (len startIdx endIdx : ℕ) : Vector Bool len :=
  Vector.ofFn (fun i => decide ((i : ℕ) ∈ Finset.Ico startIdx endIdx))

/-- The two spec levels agree (`Finset.mem_Ico`). -/
lemma arraySelector_eq_arraySelector_high :
    arraySelector_spec = arraySelector_high := by
  funext len startIdx endIdx
  apply Vector.ext
  intro i hi
  simp only [arraySelector_spec, arraySelector_high, Vector.getElem_ofFn, Finset.mem_Ico]

def selectArrayValue_spec {len : ℕ} (arr : Vector (F p) len) (idx : ℕ) : Option (F p) :=
  arr[idx]?

lemma selectArrayValue_equiv [Fact (Nat.Prime p)] {len : ℕ}
    (arr : Vector (F p) len) (idx : F p) (hlen : len ≤ p) :
    FArray.selectArrayValue arr idx = selectArrayValue_spec arr idx.val := by
  unfold FArray.selectArrayValue selectArrayValue_spec
  by_cases hidx : idx.val < len
  · rw [singleOneArray_equiv len idx hidx hlen, Vector.getElem?_eq_getElem hidx]
    simp only [bind, Option.bind, pure]
    rw [Spec.F.dotProduct_equiv]
    congr 1
    unfold Spec.F.dotProduct_spec
    refine (Finset.sum_eq_single (⟨idx.val, hidx⟩ : Fin len) ?_ ?_).trans ?_
    · intro b _ hb
      have hbne : (b : ℕ) ≠ idx.val := fun hc => hb (Fin.ext hc)
      simp [singleOneArray_spec, Vector.getElem_ofFn, FB.ofBool, FB.false, hbne]
    · intro hcon
      exact absurd (Finset.mem_univ _) hcon
    · simp [singleOneArray_spec, Vector.getElem_ofFn, FB.ofBool, FB.true]
  · rw [singleOneArray_none len idx hlen (not_lt.mp hidx),
        Vector.getElem?_eq_none (not_lt.mp hidx)]
    simp only [bind, Option.bind]

end Spec.FArray

namespace TestArray

open Clap.Lang Clap.Spec
open Array

abbrev p := Primes.goldilocks

abbrev p' := 11
local instance : Fact (Nat.Prime p') := by decide

-- singleOneArray tests
-- from https://github.com/aptos-labs/keyless-zk-proofs/blob/main/circuit/templates/helpers/arrays/SingleOneArray.circom
-- Only satisfiable when 0 <= idx < LEN.
example : FArray.singleOneArray (p := p) 4 0 = some #v[1,0,0,0] := by native_decide
example : FArray.singleOneArray (p := p) 4 1 = some #v[0,1,0,0] := by native_decide
example : FArray.singleOneArray (p := p) 4 2 = some #v[0,0,1,0] := by native_decide
example : FArray.singleOneArray (p := p) 4 3 = some #v[0,0,0,1] := by native_decide
example : FArray.singleOneArray (p := p) 6 3 = some #v[0,0,0,1,0,0] := by native_decide
example : FArray.singleOneArray (p := p) 1 0 = some #v[1] := by native_decide
example : FArray.singleOneArray (p := p) 4 4 = none := by native_decide
example : FArray.singleOneArray (p := p) 4 5 = none := by native_decide
example : FArray.singleOneArray (p := p) 1 1 = none := by native_decide

-- singleEndArray (SingleNegOneArray) tests
-- from https://github.com/aptos-labs/keyless-zk-proofs/blob/main/circuit/templates/helpers/arrays/SingleNegOneArray.circom
-- Returns a vector of all zeros when idx >= LEN.
-- @warning behaves differently than SingleOneArray: i.e., remains satisfiable even when idx > LEN
example : FArray.singleEndArray (p := p) 4 0 = some #v[1,0,0,0] := by native_decide
example : FArray.singleEndArray (p := p) 4 2 = some #v[0,0,1,0] := by native_decide
example : FArray.singleEndArray (p := p) 4 3 = some #v[0,0,0,1] := by native_decide
example : FArray.singleEndArray (p := p) 4 4 = some #v[0,0,0,0] := by native_decide
example : FArray.singleEndArray (p := p) 4 5 = some #v[0,0,0,0] := by native_decide
example : FArray.singleEndArray (p := p) 4 1 = some #v[0,1,0,0] := by native_decide
example : FArray.singleEndArray (p := p) 1 0 = some #v[1] := by native_decide
example : FArray.singleEndArray (p := p) 6 3 = some #v[0,0,0,1,0,0] := by native_decide
-- With p' = 11, len > p causes index collisions mod p, producing s ≥ 2 which fails s² = s.
example : FArray.singleEndArray (p := p') 12 0 = none := by native_decide
example : FArray.singleEndArray (p := p') 13 1 = none := by native_decide

-- arraySelector tests
example : FArray.arraySelector (p := p) 4 0 1 = some #v[1,0,0,0] := by native_decide
example : FArray.arraySelector (p := p) 4 1 3 = some #v[0,1,1,0] := by native_decide
example : FArray.arraySelector (p := p) 4 3 4 = some #v[0,0,0,1] := by native_decide
example : FArray.arraySelector (p := p) 4 0 4 = some #v[1,1,1,1] := by native_decide
example : FArray.arraySelector (p := p) 4 2 4 = some #v[0,0,1,1] := by native_decide
example : FArray.arraySelector (p := p) 4 1 2 = some #v[0,1,0,0] := by native_decide
example : FArray.arraySelector (p := p) 4 3 3 = none := by native_decide
example : FArray.arraySelector (p := p) 4 0 0 = none := by native_decide

-- selectArrayValue tests
example : FArray.selectArrayValue (p := p) #v[10,20,30,40] 0 = some 10 := by native_decide
example : FArray.selectArrayValue (p := p) #v[10,20,30,40] 1 = some 20 := by native_decide
example : FArray.selectArrayValue (p := p) #v[10,20,30,40] 2 = some 30 := by native_decide
example : FArray.selectArrayValue (p := p) #v[10,20,30,40] 3 = some 40 := by native_decide
example : FArray.selectArrayValue (p := p) #v[10,20,30,40] 4 = none := by native_decide
example : FArray.selectArrayValue (p := p) #v[42] 0 = some 42 := by native_decide
example : FArray.selectArrayValue (p := p) #v[42] 1 = none := by native_decide
example : FArray.selectArrayValue (p := p) #v[100,200,300,400,500,600] 5 = some 600 := by native_decide

-- leftArraySelector tests
-- LeftArraySelector(4)(0) -> 0000
example : FArray.leftArraySelector (p := p) 4 0 = some #v[0,0,0,0] := by native_decide
-- LeftArraySelector(4)(1) -> 1000
example : FArray.leftArraySelector (p := p) 4 1 = some #v[1,0,0,0] := by native_decide
-- LeftArraySelector(4)(2) -> 1100
example : FArray.leftArraySelector (p := p) 4 2 = some #v[1,1,0,0] := by native_decide
-- LeftArraySelector(4)(3) -> 1110
example : FArray.leftArraySelector (p := p) 4 3 = some #v[1,1,1,0] := by native_decide
-- idx >= len fails (singleOneArray not satisfiable)
example : FArray.leftArraySelector (p := p) 4 4 = none := by native_decide

-- rightArraySelector tests
-- RightArraySelector(4)(0) -> 0111
example : FArray.rightArraySelector (p := p) 4 0 = some #v[0,1,1,1] := by native_decide
-- RightArraySelector(4)(1) -> 0011
example : FArray.rightArraySelector (p := p) 4 1 = some #v[0,0,1,1] := by native_decide
-- RightArraySelector(4)(2) -> 0001
example : FArray.rightArraySelector (p := p) 4 2 = some #v[0,0,0,1] := by native_decide
-- RightArraySelector(4)(3) -> 0000
example : FArray.rightArraySelector (p := p) 4 3 = some #v[0,0,0,0] := by native_decide
-- idx >= len fails
example : FArray.rightArraySelector (p := p) 4 4 = none := by native_decide

-- arraySelectorComplex tests
-- right(0)=[0,1,1,1] * left(2)=[1,1,0,0] = [0,1,0,0]
example : FArray.arraySelectorComplex (p := p) 4 1 2 = some #v[0,1,0,0] := by native_decide
-- right(1)=[0,0,1,1] * left(3)=[1,1,1,0] = [0,0,1,0]
example : FArray.arraySelectorComplex (p := p) 4 2 3 = some #v[0,0,1,0] := by native_decide
-- right(0)=[0,1,1,1] * left(3)=[1,1,1,0] = [0,1,1,0]
example : FArray.arraySelectorComplex (p := p) 4 1 3 = some #v[0,1,1,0] := by native_decide
-- endIdx <= startIdx → all zeros: right(1)=[0,0,1,1] * left(1)=[1,0,0,0] = [0,0,0,0]
example : FArray.arraySelectorComplex (p := p) 4 2 1 = some #v[0,0,0,0] := by native_decide
-- startIdx = 0 fails
example : FArray.arraySelectorComplex (p := p) 4 0 2 = none := by native_decide

end TestArray
