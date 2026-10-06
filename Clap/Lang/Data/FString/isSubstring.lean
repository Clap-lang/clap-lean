import Clap.Lang.Core.Combinators.mapM
import Clap.Lang.Core.F.dotProduct
import Clap.Lang.Core.FB.and
import Clap.Lang.Core.FB.assert
import Clap.Lang.Core.FB.eq
import Clap.Lang.Core.FB.not
import Clap.Lang.Data.FArray.arraySelector
import Clap.Lang.Data.FArray.selectArrayValue
import Clap.Lang.Data.FVec.powers
import Clap.FiatShamir.Polynomial
import Clap.Lang.Data.HashToField.transcript

namespace Clap.Lang.FString

open Poseidon RandomOracle Primes FiatShamir

variable {p : ℕ}

/-! Circom's `IsSubstring` reads each byte array as the coefficients of a polynomial, evaluates them
at one challenge `α`, and checks `ŝ(α) = α^s · t(α)`, with `ŝ` the window `[s, e)` of `str` and
`t` the substring. Vectors are compared through `ext v i`, their zero extension, so no index
bounds appear. -/

section identity

open Polynomial hiding ext

namespace isSubstring

variable {n m : ℕ}

/-- The window `[s, e)` of `str`, as the circuit selects it: `ArraySelector`'s bit at `i` is
`(s ≤ i) xor (e ≤ i)`, which is the interval once `s ≤ e`, and the selected string is that bit
times `str[i]`. -/
def window (str : Vector (ZMod p) n) (s e : ℕ) : Vector (ZMod p) n :=
  Vector.ofFn fun i ↦ if (decide (s ≤ i.val) ^^ decide (e ≤ i.val)) then str[i] else 0

lemma ext_window (str : Vector (ZMod p) n) {s e : ℕ} (h : s ≤ e) (i : ℕ) :
    ext (window str s e) i = if s ≤ i ∧ i < e then ext str i else 0 := by
  by_cases hi : i < n
  · rw [ext_of_lt _ hi, ext_of_lt _ hi]
    simp only [window, Vector.getElem_ofFn]
    by_cases h1 : s ≤ i <;> by_cases h2 : e ≤ i <;> simp [h1, h2]; omega
  · rw [ext_of_le _ (by omega), ext_of_le _ (by omega)]
    simp

/-- `substr` occurs in `str` at `s`, for length `ℓ`. The window
`[s, s + ℓ)` of `str` (zero past its end), shifted to `0`, is `substr` zero-extended.

Unfolded, this says `substr[j] = str[s + j]` for `j < ℓ` with `s + j` inside `str`, that
`substr` is `0` after `ℓ`, and wherever the window runs past the end of `str`, and that `str` is
`0` wherever the window runs past the end of `substr`. -/
def SubstrAt (str : Vector (ZMod p) n) (substr : Vector (ZMod p) m) (s ℓ : ℕ) : Prop :=
  ∀ i : ℕ, (if s ≤ i ∧ i < s + ℓ then ext str i else 0) =
    (if s ≤ i then ext substr (i - s) else 0)

/-- The polynomial the substring check tests at `α`: window minus shifted substring. -/
noncomputable def substrDiff (str : Vector (ZMod p) n) (substr : Vector (ZMod p) m) (s e : ℕ) :
    (ZMod p)[X] :=
  vecPoly (window str s e) - X ^ s * vecPoly substr

lemma substrDiff_eq_zero_iff (str : Vector (ZMod p) n) (substr : Vector (ZMod p) m)
    {s ℓ : ℕ} :
    substrDiff str substr s (s + ℓ) = 0 ↔ SubstrAt str substr s ℓ := by
  rw [substrDiff, sub_eq_zero, Polynomial.ext_iff]
  simp only [coeff_vecPoly, coeff_X_pow_mul_vecPoly, ext_window str (show s ≤ s + ℓ by omega)]
  rfl

lemma eval_substrDiff (str : Vector (ZMod p) n) (substr : Vector (ZMod p) m) (s e : ℕ)
    (α : ZMod p) :
    (substrDiff str substr s e).eval α =
      evalAt (window str s e) α - α ^ s * evalAt substr α := by
  simp [substrDiff, eval_vecPoly]

lemma natDegree_substrDiff_le (str : Vector (ZMod p) n) (substr : Vector (ZMod p) m)
    {s e : ℕ} (hs : s < n) :
    (substrDiff str substr s e).natDegree ≤ (n - 1) + (m - 1) := by
  unfold substrDiff
  apply (natDegree_sub_le _ _).trans
  apply max_le
  · exact (natDegree_vecPoly_le _).trans (by omega)
  · exact (natDegree_X_pow_mul_vecPoly_le _ _).trans (by omega)

/-- (Completeness of the identity) when `substr` occurs at `s`, the check's two sides agree at
every `α`. -/
lemma evalAt_window_of_substrAt {str : Vector (ZMod p) n} {substr : Vector (ZMod p) m}
    {s ℓ : ℕ} (h : SubstrAt str substr s ℓ) (α : ZMod p) :
    evalAt (window str s (s + ℓ)) α = α ^ s * evalAt substr α := by
  have h0 := (substrDiff_eq_zero_iff str substr).mpr h
  have := congrArg (Polynomial.eval α) h0
  rw [eval_substrDiff] at this
  simpa [sub_eq_zero] using this

end isSubstring

end identity

/-! ## On strings

`SubstrAt`, and `assertIsConcatenation.IsConcat`, are about zero-extended vectors. For strings
encoded by `FString.encodeV`, one byte per character, they are the string statements, provided
no character is NUL: otherwise zero padding could stand in for one. -/

section strings

lemma natCast_inj {a b : ℕ} (ha : a < p) (hb : b < p) (h : (a : ZMod p) = (b : ZMod p)) :
    a = b := by
  haveI : NeZero p := ⟨by omega⟩
  have := congrArg ZMod.val h
  rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this

lemma ext_encodeV {w : ℕ} {S : String} (hS : S.length ≤ w) (i : ℕ) :
    ext (encodeV (p := p) w S) i =
      if h : i < S.toList.length then (((S.toList[i]'h).toUInt8.toNat : ℕ) : ZMod p) else 0 := by
  by_cases hi : i < w
  · rw [ext_of_lt _ hi]
    simp [encodeV]
  · rw [ext_of_le _ (by omega)]
    have : ¬ i < S.toList.length := by rw [String.length_toList]; omega
    simp [this]

namespace isSubstring

/-- A window of `L` read as a list: `M` sits in `L` at `s`, position by position. -/
private lemma list_window_iff {α : Type} (L M : List α) (s : ℕ) (hM : 0 < M.length) :
    (∀ j (hj : j < M.length), ∃ h : s + j < L.length, L[s + j] = M[j]) ↔
      s + M.length ≤ L.length ∧ M = (L.drop s).take M.length := by
  constructor
  · intro h
    have h_len : s + M.length ≤ L.length := by
      obtain ⟨hlt, -⟩ := h (M.length - 1) (by omega)
      omega
    refine ⟨h_len, ?_⟩
    apply List.ext_getElem
    · simp only [List.length_take, List.length_drop]; omega
    · intro j h1 h2
      obtain ⟨hlt, heq⟩ := h j h1
      rw [List.getElem_take, List.getElem_drop, heq]
  · rintro ⟨h_len, h_eq⟩ j hj
    refine ⟨by omega, ?_⟩
    have h1 : j < ((L.drop s).take M.length).length := by
      simp only [List.length_take, List.length_drop]; omega
    have := List.getElem_of_eq h_eq hj
    rw [this, List.getElem_take, List.getElem_drop]

/-- For strings encoded by `FString.encodeV`, `SubstrAt` is the statement: `T` fits in
`S` at `s` and is a prefix of what follows. `T` has no NUL character, so that `S`'s zero padding
cannot stand in for it. -/
theorem substrAt_encodeV_iff {n m s : ℕ} {S T : String} (hp : 256 < p)
    (hS : S.length ≤ n) (hT : T.length ≤ m) (hT0 : 0 < T.length)
    (hSc : ∀ c ∈ S.toList, c.toNat < 256) (hTc : ∀ c ∈ T.toList, 0 < c.toNat ∧ c.toNat < 256) :
    SubstrAt (encodeV (p := p) n S) (encodeV (p := p) m T) s T.length ↔
      s + T.length ≤ S.length ∧ T.toList <+: S.toList.drop s := by
  -- 1. the identity is pointwise on the window
  have step1 : SubstrAt (encodeV (p := p) n S) (encodeV (p := p) m T) s T.length ↔
      ∀ j < T.length, ext (encodeV (p := p) n S) (s + j) =
        ext (encodeV (p := p) m T) j := by
    constructor
    · intro h j hj
      have := h (s + j)
      simp only [show s ≤ s + j by omega, show s + j < s + T.length by omega, and_self, if_true,
        Nat.add_sub_cancel_left] at this
      exact this
    · intro h i
      by_cases hsi : s ≤ i
      · obtain ⟨j, rfl⟩ : ∃ j, i = s + j := ⟨i - s, by omega⟩
        simp only [hsi, true_and, if_true, Nat.add_sub_cancel_left]
        by_cases hj : j < T.length
        · rw [if_pos (by omega), h j hj]
        · rw [if_neg (by omega), ext_encodeV hT, dif_neg (by rw [String.length_toList]; omega)]
      · simp [hsi]
  -- 2. each position: the substring's byte is nonzero, so `S` must have the same character there
  have step2 : ∀ j (hj : j < T.length), (ext (encodeV (p := p) n S) (s + j) =
      ext (encodeV (p := p) m T) j ↔
      ∃ h : s + j < S.toList.length,
        S.toList[s + j] = T.toList[j]'(by rw [String.length_toList]; exact hj)) := by
    intro j hj
    have hjT : j < T.toList.length := by rw [String.length_toList]; exact hj
    have hTj := hTc _ (List.getElem_mem hjT)
    rw [ext_encodeV hS, ext_encodeV hT, dif_pos hjT, toUInt8_toNat_of_lt hTj.2]
    by_cases hsj : s + j < S.toList.length
    · have hSj := hSc _ (List.getElem_mem hsj)
      rw [dif_pos hsj, toUInt8_toNat_of_lt hSj]
      constructor
      · intro heq
        refine ⟨hsj, Char.ext (UInt32.toNat.inj ?_)⟩
        exact natCast_inj (a := (S.toList[s + j]).toNat) (b := (T.toList[j]).toNat)
          (by omega) (by omega) heq
      · rintro ⟨_, heq⟩
        rw [heq]
    · rw [dif_neg hsj]
      simp only [hsj, IsEmpty.exists_iff, iff_false]
      intro h0
      have := natCast_inj (p := p) (a := 0) (b := (T.toList[j]).toNat) (by omega) (by omega)
        (by rw [Nat.cast_zero]; exact h0)
      omega
  -- 3. the pointwise statement is the prefix statement
  rw [step1]
  have step12 := (show (∀ j < T.length, ext (encodeV (p := p) n S) (s + j) =
        ext (encodeV (p := p) m T) j) ↔ _ from
      ⟨fun h j hj ↦ (step2 j hj).mp (h j hj), fun h j hj ↦ (step2 j hj).mpr (h j hj)⟩)
  rw [step12, List.prefix_iff_eq_take]
  exact list_window_iff S.toList T.toList s hT0

end isSubstring

end strings

section check

/-- The body of Circom's `IsSubstring` once the challenge powers and the selector are known.
select the window of `str`, evaluate it and `substr` at the challenge, and compare
`ŝ(α) ≠ 0 ∧ ŝ(α) = α^start · t(α)`. `selectArrayValue` gives `α^start`, and is the only
assertion is `start < n`. -/
def isSubstring.check [p.AtLeastTwo] {n m : ℕ} (h : m ≤ n) (str : FVec p n)
    (substrData : FVec p m) (startIndex : F p) (pows : FVec p n) (sel : FArray p n) :
    ClapM p (FB p) := do
  let selected ← (sel.zip str).mapM (fun bs ↦ bs.1 * bs.2)
  let strEval ← dotProduct selected pows
  let substrEval ← dotProduct substrData ((pows.extract 0 m).cast (by omega))
  let dv ← selectArrayValue n pows startIndex
  let isZ ← isZero strEval
  let nz ← not isZ
  let rhs ← dv * substrEval
  let same ← eq strEval rhs
  FB.and nz same

namespace isSubstring

/-- `str` masked by the selector bits. -/
def selectVec {n : ℕ} (sel : Vector Bool n) (str : Vector (ZMod p) n) : Vector (ZMod p) n :=
  Vector.ofFn fun i ↦ if sel[i] then str[i] else 0

/-- What `check` computes, at challenge `α`: `ŝ(α) ≠ 0 ∧ ŝ(α) = dv · t(α)`, where `dv` is
`α^start` when `start < n` (and `0` otherwise, where `check` is unsatisfiable anyway). -/
def checkPure {n m : ℕ} (α : ZMod p) (sel : Vector Bool n) (str : Vector (ZMod p) n)
    (substr : Vector (ZMod p) m) (start : ℕ) : Bool :=
  let s := evalAt (selectVec sel str) α
  let dv := if start < n then α ^ start else 0
  (!(s == 0)) && (s == dv * evalAt substr α)

private lemma dot_eq_evalAt {n : ℕ} (a : Vector (ZMod p) n) (α : ZMod p) :
    (a.zip (Vector.ofFn fun i : Fin n ↦ α ^ i.val)).foldl (fun acc xy ↦ acc + xy.1 * xy.2) 0 =
      evalAt a α := by
  rw [dotProduct.foldl_eq_sum, zero_add, evalAt]
  simp

lemma check_convertsM
  [p.AtLeastTwo]
  {n m : ℕ}
  (h : m ≤ n)
  {state : ClapMState p}
  {str : FVec p n} {substrData : FVec p m} {startIndex : F p} {pows : FVec p n}
  {sel : FArray p n}
  {str_vals : Vector (ZMod p) n} {substr_vals : Vector (ZMod p) m} {start_val α : ZMod p}
  {sel_vals : Vector Bool n}
  (h_str : Converts FVec.conversion state str str_vals)
  (h_substr : Converts FVec.conversion state substrData substr_vals)
  (h_start : Converts F.conversion state startIndex start_val)
  (h_pows : Converts FVec.conversion state pows (Vector.ofFn fun i : Fin n ↦ α ^ i.val))
  (h_sel : Converts FArray.conversion state sel sel_vals)
  (h_n : n < p)
:
  ConvertsM FB.conversion (check h str substrData startIndex pows sel) state
    (checkPure α sel_vals str_vals substr_vals start_val.val) (start_val.val < n)
:= by
  unfold check
  have h_sel_f := FVec.converts_of_FArray_converts h_sel
  step (convertsM_mapM (C_elem := FPair.conversion) (f_spec := fun bs ↦ bs.1 * bs.2)
    (fun i ↦ FVec.converts_zip h_sel_f h_str i.isLt)
    (fun h_bs ↦ mkMul.convertsM (FPair.converts_fst h_bs) (FPair.converts_snd h_bs)))
    as selected
  step dotProduct.convertsM h_selected h_pows as strEval
  have h_pows_m := FVec.converts_vector_cast (FVec.converts_extract 0 m h_pows)
    (show min m n - 0 = m by omega)
  step dotProduct.convertsM h_substr h_pows_m as substrEval
  step selectArrayValue.convertsM h_start h_pows h_n as dv
  step isZero.convertsM h_strEval as isZ
  step not.convertsM h_isZ as nz
  step mkMul.convertsM h_dv h_substrEval as rhs
  step eq.convertsM h_strEval h_rhs as same
  apply convertsM_of_convertsM (FB.and.convertsM h_nz h_same)
  · have h_s : ((Vector.map (fun bs : ZMod p × ZMod p ↦ bs.1 * bs.2)
        ((Vector.map (fun b ↦ if b = true then (1 : ZMod p) else 0) sel_vals).zip str_vals)).zip
          (Vector.ofFn fun i : Fin n ↦ α ^ i.val)).foldl (fun acc xy ↦ acc + xy.1 * xy.2) 0 =
        evalAt (selectVec sel_vals str_vals) α := by
      rw [dot_eq_evalAt]
      unfold evalAt selectVec
      apply Finset.sum_congr rfl
      intro i _
      simp only [Fin.getElem_fin, Vector.getElem_map, Vector.getElem_zip, Vector.getElem_ofFn]
      split <;> simp
    have h_t : (substr_vals.zip (Vector.cast (show min m n - 0 = m by omega)
          ((Vector.ofFn fun i : Fin n ↦ α ^ i.val).extract 0 m))).foldl
          (fun acc xy ↦ acc + xy.1 * xy.2) 0 = evalAt substr_vals α := by
      rw [dotProduct.foldl_eq_sum, zero_add, evalAt]
      apply Finset.sum_congr rfl
      intro i _
      simp only [Fin.getElem_fin, Vector.getElem_cast]
      rw [Vector.getElem_extract]
      simp
    have h_dv : (Vector.ofFn fun i : Fin n ↦ α ^ i.val).getD start_val.val 0 =
        if start_val.val < n then α ^ start_val.val else 0 := by
      split <;> simp_all [Vector.getD]
    simp only [checkPure, h_s, h_t, h_dv]
  · simp
  -- `step`'s side goal for `selectArrayValue`, the one assertion
  · exact fun h ↦ h trivial trivial trivial

lemma bind_check_convertsM
  [p.AtLeastTwo]
  {n m : ℕ}
  (h : m ≤ n)
  {state : ClapMState p}
  {action : ClapM p (FArray p n)}
  {str : FVec p n} {substrData : FVec p m} {startIndex : F p} {pows : FVec p n}
  {str_vals : Vector (ZMod p) n} {substr_vals : Vector (ZMod p) m} {start_val α : ZMod p}
  {sel_vals : Vector Bool n} {C_sel : Prop}
  (h_action : ConvertsM FArray.conversion action state sel_vals C_sel)
  (h_str : Converts FVec.conversion state str str_vals)
  (h_substr : Converts FVec.conversion state substrData substr_vals)
  (h_start : Converts F.conversion state startIndex start_val)
  (h_pows : Converts FVec.conversion state pows (Vector.ofFn fun i : Fin n ↦ α ^ i.val))
  (h_n : n < p)
:
  ConvertsM FB.conversion (action >>= fun sel ↦ check h str substrData startIndex pows sel) state
    (checkPure α sel_vals str_vals substr_vals start_val.val) (C_sel ∧ start_val.val < n)
:= convertsM_bind_and h_action
    (check_convertsM h (converts_skip h_action h_str) (converts_skip h_action h_substr)
      (converts_skip h_action h_start) (converts_skip h_action h_pows) h_action.result h_n)

end isSubstring

end check

section isSubstring

-- Poseidon is opaque to these proofs; see `Data/HashToField/hashElemsToField.lean`.
attribute [local irreducible] Clap.Lang.Poseidon.poseidonBN254

/-- Everything after hashing `substr`: the challenge, its powers, the selector, and `check`. -/
def isSubstring.afterHash {n m : ℕ} (h : m ≤ n) (str : FVec bn254 n) (strHash : F bn254)
    (substr : FString bn254 m) (startIndex : F bn254) (substrHash : F bn254) :
    ClapM bn254 (FB bn254) := do
  let α ← poseidonBN254 #v[strHash, substrHash, substr.len, startIndex]
  let pows ← powers α n
  let endIdx ← mkAdd startIndex substr.len
  let sel ← arraySelector n startIndex endIdx
  isSubstring.check h str substr.data startIndex pows sel

/-- Whether `substr` occurs in `str` at `startIndex`, by one polynomial identity at a Fiat–Shamir
challenge. Circom's `IsSubstring`.

- The challenge is `H(strHash, H(substr, len), len, start)`.
- With `ŝ` the window `[start, start + len)` of `str` and `t` the substring, the output is
  `ŝ(α) ≠ 0 ∧ ŝ(α) = α^start · t(α)`. `isSubstring.convertsM` states it as `accepts`.
- It never fails on a false instance, it outputs `0`. What it does assert is the index range:
  `start` and `start + len` fit in `minBits' n` bits, and `start < n`, `start < start + len`.
  These stay hard even when the output bit is only used softly, as in Keyless's extra-field
  check.

**`strHash` is not checked.** Circom assumes it is `HashBytesToFieldWithLen(str, str_len)` and
does not hash `str`. So `str` is neither hashed nor byte-checked here, and a prover who could
choose `str` after seeing the challenge could solve for it. The soundness bound
`isSubstring.sound` is for a fixed instance, and holds for every fixed `strHash`; binding `str`
is the caller's job (Keyless passes `jwt_payload_hash`, and for `string_bodies` relies on it being
a function of `jwt_payload`).

An all-zero window always outputs `0`, and a real occurrence can output `0` when `ŝ(α) = 0`,
which is Circom's `NOT(IsZero(ŝ(α)))`. See `isSubstring.complete`. -/
def isSubstring {n m : ℕ} (h : m ≤ n) (str : FVec bn254 n) (strHash : F bn254)
    (substr : FString bn254 m) (startIndex : F bn254) : ClapM bn254 (FB bn254) := do
  let substrHash ← HashToField.hashBytesToField substr
  isSubstring.afterHash h str strHash substr startIndex substrHash

/-- `isSubstring`, asserted. Circom's `AssertIsSubstring`. -/
def assertisSubstring {n m : ℕ} (h : m ≤ n) (str : FVec bn254 n) (strHash : F bn254)
    (substr : FString bn254 m) (startIndex : F bn254) : ClapM bn254 Unit := do
  let success ← isSubstring h str strHash substr startIndex
  assert success

namespace isSubstring

/-- The Fiat–Shamir challenge `H(strHash, H(substr, len), len, start)`. -/
def challenge (H : HashFn) {m : ℕ} (strHash : ZMod bn254) (substr_vals : Vector (ZMod bn254) m)
    (len start : ZMod bn254) : ZMod bn254 :=
  H #v[strHash, HashToField.hashBytesToFieldSpec H substr_vals len, len, start]

/-- What `isSubstring` computes, for every input: `checkPure` at the challenge, on the selector
`arraySelector` produces. -/
def accepts (H : HashFn) {n m : ℕ} (str_vals : Vector (ZMod bn254) n) (strHash : ZMod bn254)
    (substr_vals : Vector (ZMod bn254) m) (len start : ZMod bn254) : Bool :=
  checkPure (challenge H strHash substr_vals len start)
    (Vector.ofFn fun i : Fin n ↦ decide (start.val ≤ i.val) ^^ decide ((start + len).val ≤ i.val))
    str_vals substr_vals start.val

lemma afterHash_convertsM
  {H : HashFn}
  (h_H : Computes H)
  {n m : ℕ}
  (h : m ≤ n)
  {state : ClapMState bn254}
  {str : FVec bn254 n} {strHash : F bn254} {substr : FString bn254 m} {startIndex : F bn254}
  {substrHash : F bn254}
  {str_vals : Vector (ZMod bn254) n} {strHash_val : ZMod bn254}
  {substr_vals : Vector (ZMod bn254) m} {len_val start_val substrHash_val : ZMod bn254}
  (h_str : Converts FVec.conversion state str str_vals)
  (h_strHash : Converts F.conversion state strHash strHash_val)
  (h_data : Converts FVec.conversion state substr.data substr_vals)
  (h_len : Converts F.conversion state substr.len len_val)
  (h_start : Converts F.conversion state startIndex start_val)
  (h_substrHash : Converts F.conversion state substrHash substrHash_val)
  (h_n : n < bn254) (hw : 2 ^ (minBits' n + 1) < bn254)
:
  ConvertsM FB.conversion (afterHash h str strHash substr startIndex substrHash) state
    (checkPure (H #v[strHash_val, substrHash_val, len_val, start_val])
      (Vector.ofFn fun i : Fin n ↦
        decide (start_val.val ≤ i.val) ^^ decide ((start_val + len_val).val ≤ i.val))
      str_vals substr_vals start_val.val)
    ((start_val.val < 2 ^ minBits' n ∧ (start_val + len_val).val < 2 ^ minBits' n ∧
      start_val.val < n ∧ start_val.val < (start_val + len_val).val) ∧ start_val.val < n)
:= by
  unfold afterHash
  have h_inputs := FVec.converts_push (FVec.converts_push (FVec.converts_push
    (FVec.converts_push FVec.converts_empty h_strHash) h_substrHash) h_len) h_start
  step (h_H (by decide) (by decide) h_inputs) as α
  step powers.convertsM h_α as pows
  step mkAdd.convertsM h_start h_len as endIdx
  apply convertsM_of_convertsM (bind_check_convertsM h
    (arraySelector.convertsM h_start h_endIdx h_n hw) h_str h_data h_start h_pows h_n)
  · rfl
  · simp

lemma convertsM
  {H : HashFn}
  (h_H : Computes H)
  {n m : ℕ}
  (h : m ≤ n)
  {state : ClapMState bn254}
  {str : FVec bn254 n} {strHash : F bn254} {substr : FString bn254 m} {startIndex : F bn254}
  {str_vals : Vector (ZMod bn254) n} {strHash_val : ZMod bn254}
  {substr_vals : Vector (ZMod bn254) m} {len_val start_val : ZMod bn254}
  (h_str : Converts FVec.conversion state str str_vals)
  (h_strHash : Converts F.conversion state strHash strHash_val)
  (h_data : Converts FVec.conversion state substr.data substr_vals)
  (h_len : Converts F.conversion state substr.len len_val)
  (h_start : Converts F.conversion state startIndex start_val)
  (h_m : m ≤ 1953) (h_n : n < bn254) (hw : 2 ^ (minBits' n + 1) < bn254)
:
  ConvertsM FB.conversion (isSubstring h str strHash substr startIndex) state
    (accepts H str_vals strHash_val substr_vals len_val start_val)
    ((∀ i : Fin m, substr_vals[i].val < 2 ^ 8) ∧
      start_val.val < 2 ^ minBits' n ∧ (start_val + len_val).val < 2 ^ minBits' n ∧
      start_val.val < n ∧ start_val.val < (start_val + len_val).val)
:= by
  unfold isSubstring
  have hHash := HashToField.hashBytesToField.convertsM h_H h_data h_len h_m
  apply convertsM_of_convertsM (convertsM_bind_and
    (function := fun sh ↦ afterHash h str strHash substr startIndex sh) hHash
    (afterHash_convertsM h_H h (converts_skip hHash h_str) (converts_skip hHash h_strHash)
      (converts_skip hHash h_data) (converts_skip hHash h_len) (converts_skip hHash h_start)
      hHash.result h_n hw))
  · rfl
  · constructor
    · rintro ⟨h_bytes, ⟨h_s, h_e, h_sn, h_se⟩, -⟩
      exact ⟨h_bytes, h_s, h_e, h_sn, h_se⟩
    · rintro ⟨h_bytes, h_s, h_e, h_sn, h_se⟩
      exact ⟨h_bytes, ⟨h_s, h_e, h_sn, h_se⟩, h_sn⟩

/-! ### What `accepts` means

`accepts` is a polynomial identity at a hashed challenge. So it is not equivalent to `SubstrAt`:
a real occurrence can fail (when `ŝ(α) = 0`), and a false one can pass (when `α` is a root of the
difference polynomial). Both are bounded under the random oracle below, for a fixed instance. -/

/-- Slot 5's `start < start + len` rules out wrapping, so the window length is `len`. -/
lemma val_add_of_lt_val {a b : ZMod bn254} (h : a.val < (a + b).val) :
    (a + b).val = a.val + b.val := by
  apply ZMod.val_add_of_lt
  by_contra h'
  rw [ZMod.val_add_of_le (by omega)] at h
  have := ZMod.val_lt b
  omega

lemma selectVec_arraySelector {n : ℕ} (str_vals : Vector (ZMod bn254) n) (s e : ℕ) :
    selectVec (Vector.ofFn fun i : Fin n ↦ decide (s ≤ i.val) ^^ decide (e ≤ i.val)) str_vals =
      window str_vals s e := by
  ext i hi
  simp [selectVec, window]

/-- The challenge is the random function's answer at `challengeQuery`. -/
def challengeQuery (f : Query → ZMod bn254) {m : ℕ} (strHash : ZMod bn254)
    (substr_vals : Vector (ZMod bn254) m) (len start : ZMod bn254) : Query :=
  RandomOracle.hashQ #v[strHash,
    HashToField.hashBytesToFieldSpec (Query.toHashFn f) substr_vals len, len, start]

lemma challenge_toHashFn (f : Query → ZMod bn254) {m : ℕ} (strHash : ZMod bn254)
    (substr_vals : Vector (ZMod bn254) m) (len start : ZMod bn254) :
    challenge (Query.toHashFn f) strHash substr_vals len start =
      f (challengeQuery f strHash substr_vals len start) :=
  RandomOracle.toHashFn_apply f _ (by decide)

/-- An accepted instance makes the challenge a root of the difference polynomial. -/
lemma eval_substrDiff_of_accepts {H : HashFn} {n m : ℕ} {str_vals : Vector (ZMod bn254) n}
    {strHash : ZMod bn254} {substr_vals : Vector (ZMod bn254) m} {len start : ZMod bn254}
    (h_sn : start.val < n) (h : accepts H str_vals strHash substr_vals len start = true) :
    (substrDiff str_vals substr_vals start.val (start + len).val).eval
      (challenge H strHash substr_vals len start) = 0 := by
  simp only [accepts, checkPure, selectVec_arraySelector, h_sn, if_true, Bool.and_eq_true,
    Bool.not_eq_true', beq_eq_false_iff_ne, beq_iff_eq] at h
  rw [eval_substrDiff, h.2, sub_self]

/-- (Completeness at a challenge) If `substr` occurs at `start`, the circuit accepts at every
challenge where the window does not evaluate to `0`, whatever `H` is. -/
lemma accepts_of_substrAt {H : HashFn} {n m : ℕ} {str_vals : Vector (ZMod bn254) n}
    {strHash : ZMod bn254} {substr_vals : Vector (ZMod bn254) m} {len start : ZMod bn254}
    (h_sn : start.val < n) (h_se : start.val < (start + len).val)
    (h_sub : SubstrAt str_vals substr_vals start.val len.val)
    (h_nz : evalAt (window str_vals start.val (start + len).val)
      (challenge H strHash substr_vals len start) ≠ 0) :
    accepts H str_vals strHash substr_vals len start = true := by
  have h_id := evalAt_window_of_substrAt h_sub (challenge H strHash substr_vals len start)
  rw [← val_add_of_lt_val h_se] at h_id
  simp only [accepts, checkPure, selectVec_arraySelector, h_sn, if_true, Bool.and_eq_true,
    Bool.not_eq_true', beq_eq_false_iff_ne, beq_iff_eq]
  exact ⟨h_nz, h_id⟩

/-- (Soundness under the random oracle) For a fixed instance in which `substr` does not occur
at `start`, the circuit accepts with probability at most `((n - 1) + (m - 1) + 25) / p` over
`H ← randomOracle`.

The first term is Schwartz–Zippel for the difference polynomial, valid while the challenge query
is fresh. The `25 / p` is the chance that it is not, i.e. that it coincides with one of the at
most five queries hashing `substr` makes (`HashToField.challenge_mem_transcript_le`). See `prob_checks_le` in assertIsConcatenation
The instance, `strHash` included, is fixed before `H` is drawn; see `isSubstring` on why an
adaptive prover also needs `strHash` to bind `str`. -/
theorem prob_accepts_le {n m : ℕ} (str_vals : Vector (ZMod bn254) n) (strHash : ZMod bn254)
    (substr_vals : Vector (ZMod bn254) m) (len start : ZMod bn254)
    (h_sn : start.val < n) (h_se : start.val < (start + len).val)
    (h_bad : ¬ SubstrAt str_vals substr_vals start.val len.val) :
    randomOracle.toOuterMeasure
        {f | accepts (Query.toHashFn f) str_vals strHash substr_vals len start = true}
      ≤ (((n - 1) + (m - 1) + 25 : ℕ) : ENNReal) / bn254 := by
  classical
  set D := substrDiff str_vals substr_vals start.val (start + len).val with hD
  have h_D : D ≠ 0 := by
    rw [hD, val_add_of_lt_val h_se, Ne, substrDiff_eq_zero_iff]
    exact h_bad
  set v := HashToField.hashBytesToFieldElems substr_vals len
  set c := fun f ↦ challengeQuery f strHash substr_vals len start
  set T := fun f ↦ HashToField.transcript f v
  have h_sub : {f | accepts (Query.toHashFn f) str_vals strHash substr_vals len start = true} ⊆
      {f | c f ∈ T f} ∪ {f | c f ∉ (T f : Set Query) ∧ D.eval (f (c f)) = 0} := by
    intro f hf
    have h_root := eval_substrDiff_of_accepts h_sn hf
    rw [challenge_toHashFn] at h_root
    by_cases h : c f ∈ T f
    · exact Or.inl h
    · exact Or.inr ⟨by simpa using h, h_root⟩
  have h_coll : randomOracle.toOuterMeasure {f | c f ∈ T f} ≤ 25 / bn254 :=
    HashToField.challenge_mem_transcript_le v 1 c (fun f ↦ by
      simp only [c, challengeQuery]
      rw [RandomOracle.coord_hashQ _ (by decide)]
      rfl)
  have h_fresh := randomOracle_fresh_le c (fun f ↦ ↑(T f)) (fun _ y ↦ D.eval y = 0)
    ((n - 1) + (m - 1))
    (fun f f' h ↦ by
      have h' := HashToField.congr v (by simpa using h)
      have h_hash : HashToField.hashBytesToFieldSpec (Query.toHashFn f) substr_vals len =
          HashToField.hashBytesToFieldSpec (Query.toHashFn f') substr_vals len := h'.1
      refine ⟨?_, by simp [T, h'.2], rfl⟩
      simp only [c, challengeQuery, h_hash])
    (fun _ ↦ card_roots_le h_D (natDegree_substrDiff_le _ _ h_sn))
  calc randomOracle.toOuterMeasure
          {f | accepts (Query.toHashFn f) str_vals strHash substr_vals len start = true}
      ≤ randomOracle.toOuterMeasure {f | c f ∈ T f} +
          randomOracle.toOuterMeasure {f | c f ∉ (T f : Set Query) ∧ D.eval (f (c f)) = 0} :=
        (MeasureTheory.measure_mono h_sub).trans (MeasureTheory.measure_union_le _ _)
    _ ≤ 25 / bn254 + (((n - 1) + (m - 1) : ℕ) : ENNReal) / bn254 := add_le_add h_coll h_fresh
    _ = (((n - 1) + (m - 1) + 25 : ℕ) : ENNReal) / bn254 := by
        rw [ENNReal.div_add_div_same]
        push_cast
        ring_nf

/-- (Completeness under the random oracle) For a fixed instance in which `substr` occurs at
`start` and the window is not all zero, the circuit rejects with probability at most
`((n - 1) + 25) / p`: only when the window evaluates to `0` at the challenge (Circom's
`NOT(IsZero(ŝ(α)))`):  When substr really occurs at start, it holds at every α. The first conjunct, NOT(IsZero(ŝ(α))), can still fail on a true instance, namely when α is a root of the window polynomial W.. -/
theorem prob_rejects_le {n m : ℕ} (str_vals : Vector (ZMod bn254) n) (strHash : ZMod bn254)
    (substr_vals : Vector (ZMod bn254) m) (len start : ZMod bn254)
    (h_sn : start.val < n) (h_se : start.val < (start + len).val)
    (h_sub : SubstrAt str_vals substr_vals start.val len.val)
    (h_nz : vecPoly (window str_vals start.val (start + len).val) ≠ 0) :
    randomOracle.toOuterMeasure
        {f | accepts (Query.toHashFn f) str_vals strHash substr_vals len start = false}
      ≤ (((n - 1) + 25 : ℕ) : ENNReal) / bn254 := by
  classical
  set W := vecPoly (window str_vals start.val (start + len).val)
  set v := HashToField.hashBytesToFieldElems substr_vals len
  set c := fun f ↦ challengeQuery f strHash substr_vals len start
  set T := fun f ↦ HashToField.transcript f v
  have h_sub' : {f | accepts (Query.toHashFn f) str_vals strHash substr_vals len start = false} ⊆
      {f | c f ∈ T f} ∪ {f | c f ∉ (T f : Set Query) ∧ W.eval (f (c f)) = 0} := by
    intro f hf
    have h_zero : W.eval (f (c f)) = 0 := by
      by_contra h0
      have := accepts_of_substrAt (H := Query.toHashFn f) (strHash := strHash) h_sn h_se h_sub
        (by rw [challenge_toHashFn, ← eval_vecPoly]; exact h0)
      simp_all
    by_cases h : c f ∈ T f
    · exact Or.inl h
    · exact Or.inr ⟨by simpa using h, h_zero⟩
  have h_coll : randomOracle.toOuterMeasure {f | c f ∈ T f} ≤ 25 / bn254 :=
    HashToField.challenge_mem_transcript_le v 1 c (fun f ↦ by
      simp only [c, challengeQuery]
      rw [RandomOracle.coord_hashQ _ (by decide)]
      rfl)
  have h_fresh := randomOracle_fresh_le c (fun f ↦ ↑(T f)) (fun _ y ↦ W.eval y = 0) (n - 1)
    (fun f f' h ↦ by
      have h' := HashToField.congr v (by simpa using h)
      have h_hash : HashToField.hashBytesToFieldSpec (Query.toHashFn f) substr_vals len =
          HashToField.hashBytesToFieldSpec (Query.toHashFn f') substr_vals len := h'.1
      refine ⟨?_, by simp [T, h'.2], rfl⟩
      simp only [c, challengeQuery, h_hash])
    (fun _ ↦ card_roots_le h_nz (natDegree_vecPoly_le _))
  calc randomOracle.toOuterMeasure
          {f | accepts (Query.toHashFn f) str_vals strHash substr_vals len start = false}
      ≤ randomOracle.toOuterMeasure {f | c f ∈ T f} +
          randomOracle.toOuterMeasure {f | c f ∉ (T f : Set Query) ∧ W.eval (f (c f)) = 0} :=
        (MeasureTheory.measure_mono h_sub').trans (MeasureTheory.measure_union_le _ _)
    _ ≤ 25 / bn254 + ((n - 1 : ℕ) : ENNReal) / bn254 := add_le_add h_coll h_fresh
    _ = (((n - 1) + 25 : ℕ) : ENNReal) / bn254 := by
        rw [ENNReal.div_add_div_same]
        push_cast
        ring_nf

end isSubstring

namespace assertisSubstring

lemma convertsM
  {H : HashFn}
  (h_H : Computes H)
  {n m : ℕ}
  (h : m ≤ n)
  {state : ClapMState bn254}
  {str : FVec bn254 n} {strHash : F bn254} {substr : FString bn254 m} {startIndex : F bn254}
  {str_vals : Vector (ZMod bn254) n} {strHash_val : ZMod bn254}
  {substr_vals : Vector (ZMod bn254) m} {len_val start_val : ZMod bn254}
  (h_str : Converts FVec.conversion state str str_vals)
  (h_strHash : Converts F.conversion state strHash strHash_val)
  (h_data : Converts FVec.conversion state substr.data substr_vals)
  (h_len : Converts F.conversion state substr.len len_val)
  (h_start : Converts F.conversion state startIndex start_val)
  (h_m : m ≤ 1953) (h_n : n < bn254) (hw : 2 ^ (minBits' n + 1) < bn254)
:
  ConvertsM FUnit.conversion (assertisSubstring h str strHash substr startIndex) state ()
    (((∀ i : Fin m, substr_vals[i].val < 2 ^ 8) ∧
      start_val.val < 2 ^ minBits' n ∧ (start_val + len_val).val < 2 ^ minBits' n ∧
      start_val.val < n ∧ start_val.val < (start_val + len_val).val) ∧
      isSubstring.accepts H str_vals strHash_val substr_vals len_val start_val = true)
:= by
  unfold assertisSubstring
  have hS := isSubstring.convertsM h_H h h_str h_strHash h_data h_len h_start h_m h_n hw
  exact convertsM_bind_and (function := assert) hS (assert.convertsM hS.result)

end assertisSubstring

end isSubstring


section examples

/-! The old model's vectors (`old/Clap/FString.lean`), by evaluation, since nothing containing
Poseidon lowers yet. `strHash` is computed in the circuit, as Keyless does. The output is the bit
`isSubstring` computes; a `1` on a false instance would need the challenge to be a root of the
difference polynomial. ASCII: `'h' = 104`, `'e' = 101`, `'l' = 108`, `'o' = 111`, `'a' = 97`,
`'b' = 98`, `'c' = 99`, `'x' = 120`, `'y' = 121`, `'z' = 122`. -/

private def fsBit {n m : ℕ} (h : m ≤ n) (str : Vector (ZMod bn254) n) (strLen : ZMod bn254)
    (sub : Vector (ZMod bn254) m) (subLen start : ZMod bn254) : Option (ZMod bn254) :=
  let cmd : ClapM bn254 (HashConsSt bn254 × ExprRef) := do
    let s ← str.mapM (fun x ↦ liftM (HashConsM.mkConstant (p := bn254) x))
    let sl ← liftM (HashConsM.mkConstant (p := bn254) strLen)
    let t ← sub.mapM (fun x ↦ liftM (HashConsM.mkConstant (p := bn254) x))
    let tl ← liftM (HashConsM.mkConstant (p := bn254) subLen)
    let st ← liftM (HashConsM.mkConstant (p := bn254) start)
    let sh ← HashToField.hashBytesToField ⟨s, sl⟩
    let r ← isSubstring h s sh ⟨t, tl⟩ st
    let σ ← getThe (HashConsSt bn254)
    return (σ, r)
  let Γ := cmd.getVarStore {} 0 {}
  let r := (cmd.run 0 {}).1.1.1
  [Γ, r.1|r.2]

-- "hel" in "hello" at 0
example : fsBit (by decide) #v[104, 101, 108, 108, 111] 5 #v[104, 101, 108] 3 0 = some 1 := by
  native_decide
-- "ell" in "hello" at 1
example : fsBit (by decide) #v[104, 101, 108, 108, 111] 5 #v[101, 108, 108] 3 1 = some 1 := by
  native_decide
-- "xyz" is not in "hello" at 0
example : fsBit (by decide) #v[104, 101, 108, 108, 111] 5 #v[120, 121, 122] 3 0 = some 0 := by
  native_decide
-- "lo" in "hello" at 3
example : fsBit (by decide) #v[104, 101, 108, 108, 111] 5 #v[108, 111] 2 3 = some 1 := by
  native_decide
-- "lo" runs past the end of "hello" at 4
example : fsBit (by decide) #v[104, 101, 108, 108, 111] 5 #v[108, 111, 0] 2 4 = some 0 := by
  native_decide
-- "b" in "abc" at 1
example : fsBit (by decide) #v[97, 98, 99] 3 #v[98] 1 1 = some 1 := by
  native_decide
-- `substr`'s padding is part of the identity: a nonzero byte past `len` fails
example : fsBit (by decide) #v[104, 101, 108, 108, 111] 5 #v[104, 101, 108] 2 0 = some 0 := by
  native_decide

end examples

end Clap.Lang.FString
