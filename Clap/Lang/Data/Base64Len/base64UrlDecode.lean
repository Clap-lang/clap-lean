import Clap.Lang.Gate.num2bits
import Clap.Model.Convert.PaddedVector
import Clap.Model.Convert.Vector
import Clap.Lang.Core.Combinators.mapM
import Clap.Util.Wheels
-- import Clap.Lang.Core.FB.ofBool
-- import Clap.Lang.Core.F.mkAdd
-- import Clap.Lang.Core.F.mkSub
-- import Clap.Lang.Core.F.lessThan
-- import Clap.Lang.Core.FB.and
-- import Clap.Lang.Core.FB.eq
import Clap.Lang.Data.FArray.bits2num
import Clap.Lang.Data.Base64Len.base64UrlLookup
import Clap.Lang.Data.Base64Len.base64UrlDecodedLength

namespace Clap.Lang.Base64

variable {p : ℕ}

def base64UrlDecode₀ {w} (h:3 ∣ w) (input : FVec p (w*4/3)) : ClapM p (FVec p w)
:= do
  let tmp : Vector (FBitVec p 6) _ ← input.mapM (num2bits 6)
  let tmp : Vector (FBitVec p 6) _ := tmp.map Vector.reverse
  let tmp : FBitVec p (w*4/3 * 6) := tmp.flatten
  let tmp : Vector (FBitVec p 8) w :=
    have h : w*4/3 * 6 = w * 8 := by
      have h1 : w * 4 / 3 * 6 = w * 8 / 6 * 6 := by grind
      have h2 : w * 8 / 6 * 6 = w * 8 := by grind
      aesop (add safe [h1,h2,Nat.div_mul_cancel])
    toChunks 8 (h ▸ tmp)
  tmp.mapM (fun b ↦ FArray.bits2num b.reverse)

def base64UrlDecode {w} [p.AtLeastTwo] (h:3 ∣ w) (input : FString p (w*4/3)) :
  ClapM p (FString p w)
:= do
  let lookedup ← input.data.mapM base64UrlLookup
  let payload ← base64UrlDecode₀ h lookedup
  let len ← base64UrlDecodedLength w input.len
  return ⟨payload, len⟩

namespace base64UrlDecode

/-- Get the base64URL index of a char -/
private def charIndex (c : Char) : ℕ :=
  if c.isUpper then (c.toNat - 'A'.toNat)
  else if c.isLower then (c.toNat - 'a'.toNat + 26)
  else if c.isDigit then (c.toNat - '0'.toNat + 52)
  else if c == '-' then 62
  else if c == '_' then 63
  else 0

/-- Get the base64URL index of a char, in binary form. -/
private def charIndexBin (c : Char) : List Bool :=
  let bs := (charIndex c : BitVec 6)
  Vector.ofFn (fun i => bs.getMsb i) |>.toList

/-- Base64URL decode. Not expected to work with '=' padding -/
def decode (encoded : String) : String :=
  let bits₀ := encoded.toList.map charIndexBin
  let bits₁ := bits₀.flatten
  let bits₂ := bits₁.toChunks 8
  let toNatMSB (bs : List Bool) := bs.foldl (fun acc b => 2 * acc + b.toNat) 0
  let e₄ := bits₂.map toNatMSB
  String.ofList (e₄.map Char.ofNat)

#guard decode "TWFu" == "Man"

private lemma four_mul_lt_eight_pow (k : ℕ) : 4 * k < 8 ^ k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    have h8 : 1 ≤ 8 ^ k := Nat.one_le_pow _ _ (by norm_num)
    have hpow : (8:ℕ) ^ (k + 1) = 8 ^ k * 8 := pow_succ 8 k
    omega

/-- The decoded-length gadget's `num2bits w` range check always passes on the encoded length
`w * 4 / 3`, for any `w` a multiple of 3. -/
private lemma w43_lt_two_pow {w : ℕ} (h : 3 ∣ w) : w * 4 / 3 < 2 ^ w := by
  obtain ⟨k, rfl⟩ := h
  have hdiv : 3 * k * 4 / 3 = 4 * k := by
    rw [show 3 * k * 4 = 4 * k * 3 by ring, Nat.mul_div_cancel _ (by norm_num)]
  rw [hdiv, show (2:ℕ) ^ (3 * k) = 8 ^ k by rw [show (8:ℕ) = 2 ^ 3 by norm_num, ← pow_mul]]
  exact four_mul_lt_eight_pow k

end base64UrlDecode

/-! Pure-math reformulation of the `base64UrlDecode₀` circuit's computation (reading indices
`0 .. 63` as field elements directly, with no `ClapM`/`Converts` machinery), used to state and
prove `circuitBytes_eq_decode` below. -/
namespace base64UrlDecode₀

variable {α β : Type}

/-! Batteries' `List.toChunks` has no indexing lemmas anywhere in Mathlib/Batteries (confirmed by
exhaustive grep). The next few private lemmas establish the one we need (`toChunks_getElem`), by
unfolding the `Array`-accumulator recursion `List.toChunks.go` directly. -/

private theorem toChunks_go_eq (n : ℕ) (hn : 0 < n) :
    ∀ (xs : List α) (acc1 : Array α) (acc2 : Array (List α)),
      acc1.size ≤ n →
      List.toChunks.go n xs acc1 acc2 =
        acc2.toList ++ (acc1.toList ++ xs).take n :: ((acc1.toList ++ xs).drop n).toChunks n := by
  intro xs
  induction xs with
  | nil =>
    intro acc1 acc2 h2
    simp only [List.toChunks.go, List.append_nil]
    rw [List.take_of_length_le (by omega), List.drop_eq_nil_of_le (by omega), List.toChunks]
    simp
  | cons y ys ih =>
    intro acc1 acc2 h2
    have hstep : List.toChunks.go n (y :: ys) acc1 acc2 =
        if acc1.size = n then
          List.toChunks.go n ys (#[y]) (acc2.push acc1.toList)
        else
          List.toChunks.go n ys (acc1.push y) acc2 := by
      simp [List.toChunks.go, beq_iff_eq]
    rw [hstep]
    have hy1 : (#[y] : Array α).size = 1 := rfl
    split
    case isTrue heq =>
      have key := ih (#[y]) (acc2.push acc1.toList) (by rw [hy1]; omega)
      have hself := ih (#[y]) (#[]) (by rw [hy1]; omega)
      simp only [Array.toList_push, List.nil_append, List.singleton_append] at key hself
      have hcons : List.toChunks n (y :: ys) =
          (y :: ys).take n :: ((y :: ys).drop n).toChunks n := by
        rw [show List.toChunks n (y :: ys) = List.toChunks.go n ys #[y] #[] by
          obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hn; simp [List.toChunks]]
        exact hself
      rw [key, ← hcons]
      have htake : (acc1.toList ++ y :: ys).take n = acc1.toList :=
        List.take_left' (by rw [← heq, Array.length_toList])
      have hdrop : (acc1.toList ++ y :: ys).drop n = y :: ys :=
        List.drop_left' (by rw [← heq, Array.length_toList])
      rw [htake, hdrop]
      simp
    case isFalse heq =>
      have key := ih (acc1.push y) acc2 (by rw [Array.size_push]; omega)
      rw [key, Array.toList_push]
      simp [List.append_assoc]

private theorem toChunks_entry (n : ℕ) (hn : 0 < n) (x : α) (xs : List α) :
    List.toChunks n (x :: xs) = List.toChunks.go n xs #[x] #[] := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hn
  simp [List.toChunks]

/-- The ragged `List.toChunks` recursion equation, for a chunk size that actually chunks (`n > 0`):
peel off the first chunk of size `n` and recurse on the rest. -/
private theorem toChunks_cons (n : ℕ) (hn : 0 < n) (x : α) (xs : List α) :
    List.toChunks n (x :: xs) = (x :: xs).take n :: ((x :: xs).drop n).toChunks n := by
  rw [toChunks_entry n hn x xs, toChunks_go_eq n hn xs #[x] #[] (by simp; omega)]
  simp

private theorem toChunks_length (n : ℕ) (hn : 0 < n) :
    ∀ (k : ℕ) (l : List α), l.length = k * n → (l.toChunks n).length = k := by
  intro k
  induction k with
  | zero =>
    intro l hl
    simp only [Nat.zero_mul, List.length_eq_zero_iff] at hl
    simp [hl, List.toChunks]
  | succ k ih =>
    intro l hl
    rcases l with _ | ⟨x, xs⟩
    · simp only [List.length_nil] at hl
      exact absurd hl (by have : 0 < (k + 1) * n := Nat.mul_pos (by omega) hn; omega)
    · rw [toChunks_cons n hn]
      simp only [List.length_cons]
      have hdroplen : ((x :: xs).drop n).length = k * n := by
        rw [List.length_drop, hl, Nat.succ_mul]
        omega
      rw [ih _ hdroplen]

set_option linter.unusedVariables false in
/-- Chunk `i` of `l.toChunks n` (when `n` divides `l`'s length exactly) is the slice
`l.drop (i*n) |>.take n`. -/
private theorem toChunks_getElem (n : ℕ) (hn : 0 < n) :
    ∀ (k i : ℕ) (l : List α) (hl : l.length = k * n) (hi : i < k)
      (hi' : i < (l.toChunks n).length),
      (l.toChunks n)[i]'hi' = (l.drop (i * n)).take n := by
  intro k
  induction k with
  | zero => intro i l _ hi; omega
  | succ k ih =>
    intro i l hl hi hi'
    rcases l with _ | ⟨x, xs⟩
    · simp only [List.length_nil] at hl
      exact absurd hl (by have : 0 < (k + 1) * n := Nat.mul_pos (by omega) hn; omega)
    · have hdroplen : ((x :: xs).drop n).length = k * n := by
        rw [List.length_drop, hl, Nat.succ_mul]
        omega
      rcases i with _ | i
      · simp only [toChunks_cons n hn]
        simp
      · have hbound : i < k := by omega
        simp only [toChunks_cons n hn] at hi' ⊢
        have hi'' : i < (((x :: xs).drop n).toChunks n).length := by simpa using hi'
        have step := ih i ((x :: xs).drop n) hdroplen hbound hi''
        simp only [List.getElem_cons_succ]
        rw [step, List.drop_drop]
        have : n + i * n = (i + 1) * n := by rw [Nat.succ_mul]; omega
        rw [this]

/-- Element `i` of `(l.map f).flatten`, when `f` always returns length-`6` lists: it is element
`i % 6` of `f` applied to element `i / 6` of `l`. (Specialised to `6` since that is the only
length this file ever chunks by; the general-`m` statement needs nonlinear `div`/`mod` identities
that `omega` cannot close, while the literal `6` lets `omega` handle them directly.) -/
private theorem flatten_map6_getElem (f : α → List β) (hf : ∀ a, (f a).length = 6) :
    ∀ (l : List α) (i : ℕ) (hi1 : i / 6 < l.length) (hi2 : i % 6 < 6)
      (hi : i < ((l.map f).flatten).length),
      ((l.map f).flatten)[i]'hi = (f (l[i / 6]'hi1))[i % 6]'(by rw [hf]; exact hi2) := by
  intro l
  induction l with
  | nil => intro i hi1 _ _; simp at hi1
  | cons a tl ih =>
    intro i hi1 hi2 hi
    simp only [List.length_cons] at hi1
    simp only [List.map_cons, List.flatten_cons]
    by_cases hlt : i < 6
    · have e1 : i / 6 = 0 := by omega
      have e2 : i % 6 = i := by omega
      simp [hf a, hlt, e1, e2]
    · have hlt' : 6 ≤ i := by omega
      have hi1' : (i - 6) / 6 < tl.length := by
        have : i / 6 = (i - 6) / 6 + 1 := by omega
        omega
      have hi2' : (i - 6) % 6 < 6 := by omega
      have step := ih (i - 6) hi1' hi2' (by
        have hlen : (List.map f (a :: tl)).flatten.length = 6 + (List.map f tl).flatten.length := by
          simp [List.flatten_cons, hf a]
        omega)
      have e1 : i / 6 = (i - 6) / 6 + 1 := by omega
      have e2 : i % 6 = (i - 6) % 6 := by omega
      simp only [List.getElem_append, hf a, hlt]
      simp only [e1, e2]
      rw! (castMode := .all) [show (a :: tl)[(i - 6) / 6 + 1]'(by simp [List.length_cons]; omega) =
        tl[(i - 6) / 6]'hi1' from rfl]
      simp [step]

/-! Bridge between the `ℕ` MSB-first fold `decode` uses (`toNatMSB`, inlined in `decode`'s `let`)
and the `ZMod p` MSB-first fold `FArray.toNum` uses: on the same bits, with the same shape of
recursion, they agree once the resulting value fits in the field. -/

private theorem cast_toNatMSB_fold [NeZero p] :
    ∀ (l : List Bool) (acc0 : ℕ) (acc0' : ZMod p), (acc0 : ZMod p) = acc0' →
      ((l.foldl (fun acc b => 2 * acc + b.toNat) acc0 : ℕ) : ZMod p) =
        l.foldl (fun acc b => (if b then (1 : ZMod p) else 0) + 2 * acc) acc0' := by
  intro l
  induction l with
  | nil => intro acc0 acc0' h; simpa using h
  | cons b bs ih =>
    intro acc0 acc0' h
    simp only [List.foldl_cons]
    apply ih
    rcases b with _ | _
    · simp [← h]
    · simp [← h]; ring

private theorem toNum_reverse_val [p.AtLeastTwo] {m : ℕ} (v : Vector Bool m)
    (hv : v.toList.foldl (fun acc b => 2 * acc + b.toNat) 0 < p) :
    (Clap.Lang.FArray.toNum (p := p) v.reverse).val =
      v.toList.foldl (fun acc b => 2 * acc + b.toNat) 0 := by
  haveI : NeZero p := ⟨by have := Nat.AtLeastTwo.one_lt (n := p); omega⟩
  unfold Clap.Lang.FArray.toNum
  rw [Vector.reverse_reverse, ← Vector.foldl_toList, ← cast_toNatMSB_fold v.toList 0 0 (by simp),
    ZMod.val_natCast_of_lt hv]

/-! `charIndex`/`charIndexBin` facts, relating `decode`'s per-character bits to
`base64UrlLookup.index`. -/

private theorem isUpper_iff' {c : Char} : c.isUpper ↔ 65 ≤ c.toNat ∧ c.toNat ≤ 90 := by
  simp [Char.isUpper, UInt32.le_iff_toNat_le, ← Char.toNat_val]

private theorem isLower_iff' {c : Char} : c.isLower ↔ 97 ≤ c.toNat ∧ c.toNat ≤ 122 := by
  simp [Char.isLower, UInt32.le_iff_toNat_le, ← Char.toNat_val]

private theorem charIndex_lt_64 (c : Char) : base64UrlDecode.charIndex c < 64 := by
  have hA : ('A' : Char).toNat = 65 := rfl
  have hZ : ('Z' : Char).toNat = 90 := rfl
  have ha : ('a' : Char).toNat = 97 := rfl
  have hz : ('z' : Char).toNat = 122 := rfl
  have h0 : ('0' : Char).toNat = 48 := rfl
  have h9 : ('9' : Char).toNat = 57 := rfl
  unfold base64UrlDecode.charIndex
  split_ifs with h1 h2 h3 h4 h5
  · have := isUpper_iff'.mp h1; omega
  · have := isLower_iff'.mp h2; omega
  · have := Char.isDigit_iff_toNat.mp h3; omega
  · omega
  · omega
  · omega

/-- `charIndex` (`decode`'s spec-side character lookup) and `base64UrlLookup.index` (the
circuit-side lookup `h_idx` is stated against) agree on every character. -/
private theorem charIndex_eq_index (c : Char) :
    base64UrlDecode.charIndex c = base64UrlLookup.index c.toNat := by
  have hU := @isUpper_iff' c
  have hL := @isLower_iff' c
  have hD := Char.isDigit_iff_toNat (c := c)
  have hA : ('A' : Char).toNat = 65 := rfl
  have hZ : ('Z' : Char).toNat = 90 := rfl
  have ha : ('a' : Char).toNat = 97 := rfl
  have hz : ('z' : Char).toNat = 122 := rfl
  have h0 : ('0' : Char).toNat = 48 := rfl
  have h9 : ('9' : Char).toNat = 57 := rfl
  have hm : c.toNat = 45 ↔ c = '-' := Char.toNat_inj (d := '-')
  have hu : c.toNat = 95 ↔ c = '_' := Char.toNat_inj (d := '_')
  unfold base64UrlDecode.charIndex base64UrlLookup.index
  simp only [beq_iff_eq, ← hm, ← hu, hU, hL, hD]
  split_ifs <;> omega

private theorem charIndexBin_length (c : Char) : (base64UrlDecode.charIndexBin c).length = 6 := by
  unfold base64UrlDecode.charIndexBin
  simp

/-- `charIndexBin c`, read MSB-first, is bit `5 - r` of `charIndex c`. -/
private theorem charIndexBin_getElem (c : Char) (r : ℕ) (hr : r < 6) :
    (base64UrlDecode.charIndexBin c)[r]'(by rw [charIndexBin_length]; exact hr) =
      Nat.testBit (base64UrlDecode.charIndex c) (5 - r) := by
  unfold base64UrlDecode.charIndexBin
  simp only [Vector.getElem_toList, Vector.getElem_ofFn, BitVec.getMsb_eq_getLsb, BitVec.getLsb]
  rw [BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by have := charIndex_lt_64 c; omega)]

private theorem beq_one_iff_eq_one_of_lt_two [p.AtLeastTwo] {m : ℕ} (hm : m < 2) :
    (((m : ℕ) : ZMod p) == 1) = decide (m = 1) := by
  interval_cases m <;> simp

/-- `3 ∣ w` makes the encoded length's bit count regroup exactly into `w` bytes. -/
private theorem w43_mul6_eq_w8 {w : ℕ} (h : 3 ∣ w) : w * 4 / 3 * 6 = w * 8 := by
  have h1 : w * 4 / 3 * 6 = w * 8 / 6 * 6 := by grind
  have h2 : w * 8 / 6 * 6 = w * 8 := by grind
  aesop (add safe [h1, h2, Nat.div_mul_cancel])

/-- Pure-math value the `base64UrlDecode₀` circuit computes: convert every 6-bit index to its
MSB-first bit representation (via `num2bitsLsbPureV`, matching `num2bits`'s ideal value),
concatenate them (via `Vector.flatten`, matching the circuit's `Vector.flatten`), re-chunk the
result into 8-bit bytes (via `Wheels.toChunks`, matching the circuit's `toChunks`), and read each
byte off (via `FArray.toNum`, matching `FArray.bits2num`'s ideal value). -/
noncomputable def circuitBytes {p w : ℕ} (idxVals : Vector (ZMod p) (w * 4 / 3)) (h : 3 ∣ w) :
    Vector (ZMod p) w :=
  let bits6 : Vector (Vector Bool 6) (w * 4 / 3) :=
    idxVals.map (fun v => ((num2bitsLsbPureV 6 v).map (· == 1)).reverse)
  let flat : Vector Bool (w * 4 / 3 * 6) := bits6.flatten
  (toChunks 8 (flat.cast (w43_mul6_eq_w8 h))).map
    (fun c => Clap.Lang.FArray.toNum (p := p) c.reverse)

/-- The total bit count `decode` chunks its characters' bits into. -/
private theorem bits1_length (l : List Char) :
    ((l.map base64UrlDecode.charIndexBin).flatten).length = l.length * 6 := by
  induction l with
  | nil => simp
  | cons c cs ih => simp [List.flatten_cons, charIndexBin_length, ih, Nat.succ_mul]; omega

/-- The circuit's per-character 6-bit MSB-first representation (`circuitBytes`'s `bits6`) and the
spec's `charIndexBin`, read off the same flat bit index, agree -- given `h_idx` identifies the two
lookups on every character. -/
private theorem flat_getElem_eq {w : ℕ} (h : 3 ∣ w) {p : ℕ} [p.AtLeastTwo]
    (s : String) (hs : s.length = w * 4 / 3) (idxVals : Vector (ZMod p) (w * 4 / 3))
    (h_idx : ∀ i : Fin (w * 4 / 3),
      idxVals[i].val =
        base64UrlLookup.index (s.toList[i.1]'(by rw [String.length_toList, hs]; omega)).toNat)
    (t : ℕ) (ht : t < w * 4 / 3 * 6)
    (ht' : t < ((s.toList.map base64UrlDecode.charIndexBin).flatten).length) :
    (idxVals.map (fun v => ((num2bitsLsbPureV 6 v).map (· == 1)).reverse)).flatten[t]'ht =
      ((s.toList.map base64UrlDecode.charIndexBin).flatten)[t]'ht' := by
  have hidx1 : t / 6 < w * 4 / 3 := by omega
  have hidx2 : t % 6 < 6 := by omega
  have hs' : t / 6 < s.toList.length := by rw [String.length_toList, hs]; exact hidx1
  rw [Vector.getElem_flatten, Vector.getElem_map _ hidx1, Vector.getElem_reverse hidx2,
    Vector.getElem_map _ (show 6 - 1 - t % 6 < 6 by omega), num2bitsLsbPureV_getElem,
    flatten_map6_getElem base64UrlDecode.charIndexBin charIndexBin_length s.toList t hs' hidx2]
  rw [show (6 - 1 - t % 6) = 5 - t % 6 by omega, charIndexBin_getElem _ _ hidx2,
    beq_one_iff_eq_one_of_lt_two (Nat.mod_lt _ (by norm_num)), Nat.testBit_eq_decide_div_mod_eq]
  congr 2
  have hh := h_idx ⟨t / 6, hidx1⟩
  simp only [Fin.getElem_fin] at hh
  rw [hh, charIndex_eq_index]

/-- An MSB-first fold starting from an accumulator `< 2^k` stays `< 2^(length + k)`: generalises
the bound `toNatMSB l < 2 ^ l.length` to carry through the induction. -/
private theorem foldlMSB_lt_two_pow_add :
    ∀ (l : List Bool) (k acc : ℕ), acc < 2 ^ k →
      l.foldl (fun acc b => 2 * acc + b.toNat) acc < 2 ^ (l.length + k) := by
  intro l
  induction l with
  | nil => intro k acc hacc; simpa using hacc
  | cons b bs ih =>
    intro k acc hacc
    simp only [List.foldl_cons, List.length_cons]
    have hp : (2 : ℕ) ^ (k + 1) = 2 ^ k * 2 := pow_succ 2 k
    have hacc' : 2 * acc + b.toNat < 2 ^ (k + 1) := by cases b <;> simp_all [Bool.toNat] <;> omega
    have hstep := ih (k + 1) (2 * acc + b.toNat) hacc'
    have e : bs.length + (k + 1) = bs.length + 1 + k := by omega
    rwa [e] at hstep

private theorem toNatMSB_lt_256 (l : List Bool) (hl : l.length = 8) :
    l.foldl (fun acc b => 2 * acc + b.toNat) 0 < 256 := by
  have := foldlMSB_lt_two_pow_add l 0 0 (by norm_num)
  rw [hl] at this
  simpa using this

/-- `circuitBytes`'s byte `j`, as a value: the `FArray.toNum`-via-`.reverse` wrapper peels back to
the plain MSB-first fold over the matching flat-bit slice, given that slice's value fits the
field. -/
private theorem circuitBytes_getElem_val {w : ℕ} (h : 3 ∣ w) {p : ℕ} [p.AtLeastTwo]
    (h_p : 2 ^ (8 + 1) < p) (idxVals : Vector (ZMod p) (w * 4 / 3)) (j : ℕ) (hj : j < w) :
    ((circuitBytes idxVals h)[j]'hj).val =
      (((idxVals.map (fun v => ((num2bitsLsbPureV 6 v).map (· == 1)).reverse)).flatten
        |>.cast (w43_mul6_eq_w8 h)).toList.drop (j * 8) |>.take 8).foldl
        (fun acc b => 2 * acc + b.toNat) 0 := by
  unfold circuitBytes
  rw [Vector.getElem_map _ hj]
  generalize hflat :
    (idxVals.map (fun v => ((num2bitsLsbPureV 6 v).map (· == 1)).reverse)).flatten.cast
      (w43_mul6_eq_w8 h) = flat
  have hflatlen : flat.toList.length = w * 8 := by simp
  have hlen8 : ((toChunks 8 flat)[j]'hj).toList.length = 8 := by simp
  have hlenslice : ((flat.toList.drop (j * 8)).take 8).length = 8 := by
    rw [List.length_take, List.length_drop, hflatlen]; omega
  have hlist : ((toChunks 8 flat)[j]'hj).toList = (flat.toList.drop (j * 8)).take 8 := by
    apply List.ext_getElem (hlen8.trans hlenslice.symm)
    intro k hk1 hk2
    simp only [Vector.getElem_toList]
    rw [List.getElem_take, List.getElem_drop, getElem_toChunks flat j hj k (by simpa using hk1)]
    simp
  have hval : ((toChunks 8 flat)[j]'hj).toList.foldl (fun acc b => 2 * acc + b.toNat) 0 < p :=
    lt_trans (toNatMSB_lt_256 _ hlen8) (by omega)
  rw [toNum_reverse_val _ hval, hlist]

private theorem decode_toList_length {w : ℕ} (h : 3 ∣ w) (s : String) (hs : s.length = w * 4 / 3) :
    (base64UrlDecode.decode s).toList.length = w := by
  unfold base64UrlDecode.decode
  rw [String.toList_ofList, List.length_map, List.length_map,
    toChunks_length 8 (by norm_num) w _
      (by rw [bits1_length, String.length_toList, hs]; exact w43_mul6_eq_w8 h)]

private theorem decode_toList_getElem {w : ℕ} (h : 3 ∣ w) (s : String) (hs : s.length = w * 4 / 3)
    (j : ℕ) (hj : j < w) :
    (base64UrlDecode.decode s).toList[j]'(decode_toList_length h s hs ▸ hj) =
      Char.ofNat ((((s.toList.map base64UrlDecode.charIndexBin).flatten).drop (j * 8)).take 8
        |>.foldl (fun acc b => 2 * acc + b.toNat) 0) := by
  have hbits : ((s.toList.map base64UrlDecode.charIndexBin).flatten).length = w * 8 := by
    rw [bits1_length, String.length_toList, hs]; exact w43_mul6_eq_w8 h
  simp only [base64UrlDecode.decode, String.toList_ofList, List.getElem_map]
  congr 1
  rw [toChunks_getElem 8 (by norm_num) w j _ hbits hj]

/-- The circuit's pure-math value (`circuitBytes`, built from `num2bitsLsbPureV`,
`Vector.flatten`, `Wheels.toChunks`, `FArray.toNum` -- the same combinators the real `ConvertsM`
proof produces) agrees with the reference `decode`, given that `idxVals` carries each character's
`base64UrlLookup.index` (as `h_idx` states) and the field is big enough to hold a byte
(`h_p`, matching the bound already used elsewhere in this file for `base64UrlLookup`). -/
theorem circuitBytes_eq_decode {w : ℕ} (h : 3 ∣ w) {p : ℕ} [p.AtLeastTwo]
    (h_p : 2 ^ (8 + 1) < p) (s : String) (hs : s.length = w * 4 / 3)
    (idxVals : Vector (ZMod p) (w * 4 / 3))
    (h_idx : ∀ i : Fin (w * 4 / 3),
      idxVals[i].val =
        base64UrlLookup.index (s.toList[i.1]'(by rw [String.length_toList, hs]; omega)).toNat) :
    (circuitBytes idxVals h).toList.map (fun v => Char.ofNat v.val) =
      (base64UrlDecode.decode s).toList := by
  have hlenL : ((circuitBytes idxVals h).toList.map (fun v => Char.ofNat v.val)).length = w := by
    simp
  have hlenR : (base64UrlDecode.decode s).toList.length = w := decode_toList_length h s hs
  apply List.ext_getElem (by rw [hlenL, hlenR])
  intro j hj1 hj2
  have hjw : j < w := by simpa using hj1
  have hbits : ((s.toList.map base64UrlDecode.charIndexBin).flatten).length = w * 8 := by
    rw [bits1_length, String.length_toList, hs]; exact w43_mul6_eq_w8 h
  simp only [List.getElem_map, Vector.getElem_toList]
  rw [decode_toList_getElem h s hs j hjw, circuitBytes_getElem_val h h_p idxVals j hjw]
  congr 1
  congr 1
  apply List.ext_getElem (by
    rw [List.length_take, List.length_take, List.length_drop, List.length_drop, hbits]
    simp)
  intro k hk1 hk2
  have hk8 : k < 8 := lt_of_lt_of_le hk1 (List.length_take_le _ _)
  rw [List.getElem_take, List.getElem_take, List.getElem_drop, List.getElem_drop,
    Vector.getElem_toList, Vector.getElem_cast]
  exact flat_getElem_eq h s hs idxVals h_idx (j * 8 + k) (by omega) (by rw [hbits]; omega)

/-! `ConvertsM`-level bridge between the real `base64UrlDecode₀` circuit and its pure-math
reformulation `circuitBytes`, proved above. -/

/-- `h ▸ v` (the dependent-cast notation `base64UrlDecode₀` builds its own equality proof for)
and `Vector.cast h v` denote the same vector. They need not be definitionally equal for an
abstract `h` (`Eq.rec` stays stuck unless the proof is literally `rfl`, which it is not here
since the two lengths are only propositionally, not definitionally, equal), so this is proved
once by generalising (`subst`ing) the equality rather than relying on defeq. -/
private theorem cast_eq_vector_cast {α : Type} {n m : ℕ} (heq : n = m) (v : Vector α n) :
    heq ▸ v = v.cast heq := by subst heq; rfl

/-- `base64UrlDecode₀`'s body, rewritten so its two genuine monadic binds (`num2bits` then
`bits2num`) are exposed directly around the pure reshaping in between (now spelled with `.cast`,
matching `circuitBytes`'s own cast, via `cast_eq_vector_cast`). Everything between the two
`mapM`s in the source (`.map Vector.reverse`, `.flatten`, the dependent cast, `toChunks 8`) is a
plain `let`, i.e. direct substitution -- this lemma just makes that substitution (and the cast's
spelling) syntactically visible, so `convertsM_bind` can be applied to the result by hand. -/
private theorem base64UrlDecode₀_eq {w : ℕ} (h : 3 ∣ w) (input : FVec p (w * 4 / 3)) :
    base64UrlDecode₀ h input =
      input.mapM (num2bits 6) >>= fun tmp0 =>
        (toChunks 8 ((tmp0.map Vector.reverse).flatten.cast (w43_mul6_eq_w8 h))).mapM
          (fun b ↦ FArray.bits2num b.reverse)
:= by
  unfold base64UrlDecode₀
  simp only [cast_eq_vector_cast]

/-- Reversing every 6-bit block of a vector that converts (at the `Conversion.vector` level) and
then flattening it converts to the flattening of the per-element reversals -- fused with the
flatten the circuit performs right after reversing each block, so this never has to state a
block-reversal fact at the `Conversion.vector` level on its own (there is no element-projection
lemma for that level to rebuild one from; see `Clap/Model/Convert/Vector.lean`). Specialised to
the fixed block width `6` that `num2bits 6` produces here: at a literal width `omega` can invert
the `/6`, `%6` arithmetic a generic block width needs (the same device as `flatten_map6_getElem`
above, on the pure-math side). -/
private theorem converts_flatten_reverse6
  {k : ℕ} {p : ℕ} {state : ClapMState p}
  {exprs : Vector (FArray p 6) k} {vals : Vector (Vector Bool 6) k}
  (h : Converts (Conversion.vector FArray.conversion k) state exprs vals) :
  Converts FArray.conversion state
    (exprs.map Vector.reverse).flatten (vals.map Vector.reverse).flatten
:= by
  have h_flat := FArray.converts_flatten h
  rw [FArray.converts_iff_FB_converts] at h_flat ⊢
  rintro ⟨t, h_t⟩
  have ht2 : t / 6 * 6 + (6 - 1 - t % 6) < k * 6 := by omega
  have key := h_flat ⟨t / 6 * 6 + (6 - 1 - t % 6), ht2⟩
  simp only [Fin.getElem_fin, Vector.getElem_flatten, Vector.getElem_map,
    Vector.getElem_reverse] at key ⊢
  have e1 : (t / 6 * 6 + (6 - 1 - t % 6)) / 6 = t / 6 := by omega
  have e2 : (t / 6 * 6 + (6 - 1 - t % 6)) % 6 = 6 - 1 - t % 6 := by omega
  simp only [e1, e2] at key
  exact key

/-- The `ConvertsM`-level lemma connecting the real `base64UrlDecode₀` circuit to its pure-math
reformulation `circuitBytes`. By `base64UrlDecode₀_eq` the circuit is a single two-stage bind:
`num2bits 6` on every index (asserting each is `< 2 ^ 6`, via `convertsM_mapM_constraints`), then
a purely-`True` pipeline of reshaping and a final `bits2num` `mapM` (via `convertsM_mapM`). Only
one side of the bind ever asserts, so this is a single-assertion chain, and the overall
constraint is exactly the first stage's. -/
theorem convertsM
  {w : ℕ} (h : 3 ∣ w) {p : ℕ} [p.AtLeastTwo]
  {state : ClapMState p} {lookedup : FVec p (w*4/3)} {idxVals : Vector (ZMod p) (w*4/3)}
  (h_lookedup : Converts FVec.conversion state lookedup idxVals)
:
  ConvertsM FVec.conversion (base64UrlDecode₀ h lookedup) state
    (circuitBytes idxVals h)
    (∀ i : Fin (w*4/3), idxVals[i].val < 2 ^ 6)
:= by
  rw [base64UrlDecode₀_eq]
  have h_v : ∀ i : Fin (w * 4 / 3), Converts F.conversion state lookedup[i] idxVals[i] :=
    fun i => FVec.converts_getElem h_lookedup i.isLt
  have h_mapM1 := convertsM_mapM_constraints
    (C_elem := F.conversion) (C_out := FArray.conversion)
    (f := num2bits 6)
    (f_spec := fun v => (num2bitsLsbPureV 6 v).map (· == 1))
    (step_constraints := fun v => v.val < 2 ^ 6)
    h_v
    (fun h_elem => num2bits.convertsM h_elem)
  set bits6raw := idxVals.map (fun v => (num2bitsLsbPureV 6 v).map (· == 1)) with hbits6raw_def
  have h_rev := converts_flatten_reverse6 h_mapM1.result
  have h_cast := FArray.converts_vector_cast h_rev (w43_mul6_eq_w8 h)
  have h_chunks := FArray.converts_toChunks h_cast
  have h_mapM2 := convertsM_mapM
    (C_elem := FArray.conversion)
    (f := fun b : FArray p 8 ↦ FArray.bits2num b.reverse)
    (f_spec := fun bval ↦ Clap.Lang.FArray.toNum bval.reverse)
    h_chunks
    (fun hx => FArray.bits2num.convertsM (FArray.converts_reverse hx))
  have h_mapM2' := convertsM_of_convertsM h_mapM2 rfl
    (show True ↔ ((∀ i : Fin (w * 4 / 3), idxVals[i].val < 2 ^ 6) →
      (∀ i : Fin (w * 4 / 3), idxVals[i].val < 2 ^ 6)) from ⟨fun _ => id, fun _ => trivial⟩)
  apply convertsM_of_convertsM (convertsM_bind h_mapM1 h_mapM2' id) ?_ Iff.rfl
  have hbits6_eq : bits6raw.map Vector.reverse =
      idxVals.map (fun v => ((num2bitsLsbPureV 6 v).map (· == 1)).reverse) := by
    simp [hbits6raw_def, Vector.map_map, Function.comp_def]
  show (toChunks 8 ((bits6raw.map Vector.reverse).flatten.cast (w43_mul6_eq_w8 h))).map
      (fun bval ↦ Clap.Lang.FArray.toNum bval.reverse) = circuitBytes idxVals h
  rw [hbits6_eq]
  rfl

end base64UrlDecode₀

namespace base64UrlDecode

/-- A byte round-trips through `Char.ofNat`. -/
private lemma ofNat_toNat_of_lt256 {n : ℕ} (h : n < 256) : (Char.ofNat n).toNat = n := by
  have hv : n.isValidChar := by unfold Nat.isValidChar; omega
  rw [Char.ofNat, dif_pos hv]
  simp [Char.ofNatAux, Char.toNat]

set_option maxHeartbeats 1000000 in
lemma convertsM
  [p.AtLeastTwo]
  {w : ℕ}
  {state : ClapMState p}
  {a : FString p (w * 4 / 3)}
  {a_val : String}
  (h_a : Converts FString.conversion state a a_val)
  (h_len : 3 ∣ w)
  (h_a_len : a_val.length = w * 4 / 3)
  (h_p : 2 ^ (8 + 1) < p)
  (h_field : 2 ^ (w + 2) ≤ p)
  (h_bytes : ∀ c ∈ a_val.toList, c.toNat < 256)
:
  ConvertsM FString.conversion (base64UrlDecode h_len a) state
    (decode a_val)
    (a_val.toList.all
      fun c ↦ c ∈ [Char.ofNat 0, '-', '_', '='] ∨ c.isUpper ∨ c.isLower ∨ c.isDigit
    )
:= by
  haveI : NeZero p := ⟨by have := Nat.AtLeastTwo.one_lt (n := p); omega⟩
  unfold base64UrlDecode
  rw [← bind_assoc]
  have hlen_toList : a_val.toList.length = w * 4 / 3 := by rw [String.length_toList, h_a_len]
  have hp' : (512 : ℕ) < p := by norm_num at h_p; exact h_p
  -- Every character's field encoding is just its byte, given `h_bytes` (no truncation).
  have h_enc_eq : ∀ i (hi : i < w * 4 / 3),
      (FString.encodeV (p := p) (w * 4 / 3) a_val)[i]'hi =
        ((a_val.toList[i]'(hlen_toList ▸ hi)).toNat : ZMod p) := by
    intro i hi
    rw [FString.encodeV_getElem_of_lt hi (hlen_toList ▸ hi),
      FString.toUInt8_toNat_of_lt (h_bytes _ (List.getElem_mem _))]
  have h_enc_lt256 : ∀ i (hi : i < w * 4 / 3),
      ((FString.encodeV (p := p) (w * 4 / 3) a_val)[i]'hi).val < 256 := by
    intro i hi
    have hb : (a_val.toList[i]'(hlen_toList ▸ hi)).toNat < 256 := h_bytes _ (List.getElem_mem _)
    rw [h_enc_eq i hi, ZMod.val_natCast_of_lt (by omega)]
    omega
  -- Stage 1: look up every character's base64url index.
  have h_v : ∀ i : Fin (w * 4 / 3),
      Converts F.conversion state a.data[i] (FString.encodeV (p := p) (w * 4 / 3) a_val)[i] :=
    fun i => FVec.converts_getElem (FString.converts_data h_a) i.isLt
  have h_stage1 := convertsM_mapM_constraints
    (C_elem := F.conversion) (C_out := F.conversion)
    (f := base64UrlLookup) (f_spec := base64UrlLookup.value)
    (step_constraints := fun v => base64UrlLookup.accepts v.val)
    h_v
    (fun hx => base64UrlLookup.convertsM hx h_p)
  set idxVals := (FString.encodeV (p := p) (w * 4 / 3) a_val).map base64UrlLookup.value
    with hidxVals_def
  -- Stage 2: decode the indices into bytes. Stage 1's `< 2^6` precondition is exactly
  -- `base64UrlLookup.accepts` for every character, established by the lookup's own slot 5.
  have h_stage1_fvec : Converts FVec.conversion
      ((a.data.mapM base64UrlLookup).getState state)
      ((a.data.mapM base64UrlLookup).getResult state.numAlloc state.σ) idxVals :=
    converts_cast h_stage1.result
      (by simp only [← List.flatMap_def, List.flatMap_singleton'])
      (by simp only [← List.flatMap_def, List.flatMap_singleton'])
  have h_stage2 := base64UrlDecode₀.convertsM h_len h_stage1_fvec
  have h_guard : (∀ i : Fin (w * 4 / 3), base64UrlLookup.accepts
      ((FString.encodeV (p := p) (w * 4 / 3) a_val)[i]).val) →
      ((∀ i : Fin (w * 4 / 3), idxVals[i].val < 2 ^ 6) ↔ True) := by
    intro h_acc
    refine ⟨fun _ => trivial, fun _ i => ?_⟩
    have h_idx_lt : base64UrlLookup.index
        ((FString.encodeV (p := p) (w * 4 / 3) a_val)[i.1]'i.isLt).val < 64 := by
      unfold base64UrlLookup.index base64UrlLookup.accepts at *
      have := h_acc i
      split_ifs <;> omega
    simp only [hidxVals_def, Vector.getElem_map, Fin.getElem_fin] at h_acc ⊢
    rw [base64UrlLookup.value_of_accepts h_p (h_acc i)]
    rw [ZMod.val_natCast_of_lt (by omega)]
    omega
  have h_combined := convertsM_bind_guard h_stage1 h_stage2 h_guard
  have h_stage12 : ConvertsM FVec.conversion
      (a.data.mapM base64UrlLookup >>= base64UrlDecode₀ h_len) state
      (base64UrlDecode₀.circuitBytes idxVals h_len)
      (∀ i : Fin (w * 4 / 3), base64UrlLookup.accepts
        ((FString.encodeV (p := p) (w * 4 / 3) a_val)[i]).val) :=
    convertsM_of_convertsM h_combined rfl (by simp)
  -- Carry the length conversion fact across both steps, so `step` reframes it for us.
  have h_len_conv := FString.converts_len h_a
  clear h_stage1 h_stage1_fvec h_stage2 h_guard h_combined h_v
  step h_stage12 as combined12
  case h =>
    -- the leftover `constraints → constraints1` side of `convertsM_bind`, the converse direction
    intro h_target i
    rw [List.all_eq_true] at h_target
    have hi : i.1 < a_val.toList.length := by rw [hlen_toList]; exact i.isLt
    have h_mem := h_target a_val.toList[i.1] (List.getElem_mem hi)
    simp only [decide_eq_true_eq] at h_mem
    have hb : (a_val.toList[i.1]'hi).toNat < 256 := h_bytes _ (List.getElem_mem _)
    simp only [Fin.getElem_fin]
    rw [base64UrlLookup.accepts_iff_char (h_enc_lt256 i i.isLt), h_enc_eq i i.isLt,
      ZMod.val_natCast_of_lt (by omega), Char.ofNat_toNat]
    exact h_mem
  -- Stage 3: the decoded length. Its own range check always holds given `h_a_len`.
  have h_len_val_eq : (a_val.length : ZMod p).val = w * 4 / 3 := by
    rw [h_a_len, ZMod.val_natCast_of_lt]
    calc w * 4 / 3 < 2 ^ w := w43_lt_two_pow h_len
      _ ≤ 2 ^ (w + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ p := h_field
  have h_range : (a_val.length : ZMod p).val < 2 ^ w := by rw [h_len_val_eq]; exact w43_lt_two_pow h_len
  have h_length := base64UrlDecodedLength.convertsM h_len_conv h_range h_field
  have h_decoded_len_eq : 3 * (w * 4 / 3) / 4 = w := by
    obtain ⟨k, rfl⟩ := h_len
    have h1 : 3 * k * 4 / 3 = 4 * k := by
      rw [show 3 * k * 4 = 4 * k * 3 by ring, Nat.mul_div_cancel _ (by norm_num)]
    rw [h1]; omega
  have h_length_true : ConvertsM F.conversion (base64UrlDecodedLength w a.len) combined12_state
      (w : ZMod p) True :=
    convertsM_of_convertsM h_length
      (by rw [h_len_val_eq, h_decoded_len_eq]; exact Semiring.toGrindSemiring_ofNat (ZMod p) w)
      (by
        refine iff_of_true ⟨h_range, ?_⟩ trivial
        have h_pow : (2 : ℕ) ^ (w + 2) = 2 ^ w * 4 := by rw [pow_add]; norm_num
        rw [h_len_val_eq]; omega)
  step h_length_true as lenStep
  -- The value every character's index carries, read through `base64UrlLookup.index` of its byte.
  have h_idx : ∀ i : Fin (w * 4 / 3),
      idxVals[i].val = base64UrlLookup.index
        (a_val.toList[i.1]'(by rw [hlen_toList]; exact i.isLt)).toNat := by
    intro i
    have hb : (a_val.toList[i.1]'(by rw [hlen_toList]; exact i.isLt)).toNat < 256 :=
      h_bytes _ (List.getElem_mem _)
    have h_cast_eq : ((a_val.toList[i.1]'(by rw [hlen_toList]; exact i.isLt)).toNat : ZMod p).val
        = (a_val.toList[i.1]'(by rw [hlen_toList]; exact i.isLt)).toNat :=
      ZMod.val_natCast_of_lt (by omega)
    have h_idx_lt64 : base64UrlLookup.index
        (a_val.toList[i.1]'(by rw [hlen_toList]; exact i.isLt)).toNat < 64 := by
      unfold base64UrlLookup.index; split_ifs <;> omega
    simp only [hidxVals_def, Vector.getElem_map, Fin.getElem_fin]
    rw [base64UrlLookup.value_of_lt h_p (h_enc_lt256 i i.isLt), h_enc_eq i i.isLt, h_cast_eq,
      ZMod.val_natCast_of_lt (by omega)]
  have h_circuit_eq := base64UrlDecode₀.circuitBytes_eq_decode h_len h_p a_val h_a_len idxVals h_idx
  have hw : (base64UrlDecode.decode a_val).toList.length = w :=
    base64UrlDecode₀.decode_toList_length h_len a_val h_a_len
  have h_byte_lt : ∀ j (hj : j < w),
      ((base64UrlDecode₀.circuitBytes idxVals h_len)[j]'hj).val < 256 := by
    intro j hj
    rw [base64UrlDecode₀.circuitBytes_getElem_val h_len h_p idxVals j hj]
    apply base64UrlDecode₀.toNatMSB_lt_256
    rw [List.length_take, List.length_drop]
    simp only [Vector.toList_cast, Vector.length_toList]
    omega
  have h_value_eq : base64UrlDecode₀.circuitBytes idxVals h_len =
      FString.encodeV (p := p) w (base64UrlDecode.decode a_val) := by
    apply Vector.ext
    intro j hj
    have hj' : j < (base64UrlDecode.decode a_val).toList.length := hw ▸ hj
    rw [FString.encodeV_getElem_of_lt hj hj']
    have hmap : (base64UrlDecode.decode a_val).toList[j]'hj' =
        Char.ofNat ((base64UrlDecode₀.circuitBytes idxVals h_len)[j]'hj).val := by
      simp only [← h_circuit_eq, List.getElem_map, Vector.getElem_toList]
    have h_char_lt : (Char.ofNat
        ((base64UrlDecode₀.circuitBytes idxVals h_len)[j]'hj).val).toNat < 256 := by
      rw [ofNat_toNat_of_lt256 (h_byte_lt j hj)]; exact h_byte_lt j hj
    rw [hmap, FString.toUInt8_toNat_of_lt h_char_lt, ofNat_toNat_of_lt256 (h_byte_lt j hj),
      ZMod.natCast_zmod_val]
  have h_len_eq : (w : ZMod p) = ((base64UrlDecode.decode a_val).length : ZMod p) := by
    rw [← String.length_toList, hw]
  generalize combined12_result = payload at *
  generalize lenStep_result = len at *
  rw [h_value_eq] at h_combined12
  rw [h_len_eq] at h_lenStep
  apply convertsM_pure
  · exact FString.converts_intro h_combined12 h_lenStep
  · intro _ h_acc
    rw [List.all_eq_true, List.forall_mem_iff_forall_getElem]
    simp only [decide_eq_true_eq]
    intro i hi
    have hi' : i < w * 4 / 3 := hlen_toList ▸ hi
    have h_acc_i := h_acc ⟨i, hi'⟩
    simp only [Fin.getElem_fin] at h_acc_i
    rw [base64UrlLookup.accepts_iff_char (h_enc_lt256 i hi')] at h_acc_i
    have hb : (a_val.toList[i]'hi).toNat < 256 := h_bytes _ (List.getElem_mem _)
    rwa [h_enc_eq i hi', ZMod.val_natCast_of_lt (by omega), Char.ofNat_toNat] at h_acc_i

end base64UrlDecode
