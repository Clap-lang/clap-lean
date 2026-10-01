import Clap.Lang.Core.FUnit.assert_eq
import Clap.Lang.Data.FArray.OneHotRaw
import Clap.Lang.Data.FArray.sum
import Clap.Lang.Data.FString.assertIsAsciiDigits
import Clap.Lang.Gate.share

namespace Clap.Lang.FString

variable {p : ℕ}

section asciiDigitsToScalar

/-- The first `len` entries of `vals`, read as ASCII decimal digits, most significant first:
`Σ (vals[j] - 48) · 10^(len-1-j)`, in `ZMod p`, so it wraps once the number reaches `p`. -/
def digitsValue {n : ℕ} (vals : Vector (ZMod p) n) (len : ℕ) : ZMod p :=
  (vals.toList.take len).foldl (fun a d ↦ 10 * a + (d - 48)) 0

/-- loop, on `(s, acc)` and `(digit, index_eq)`
`s' = s - index_eq`, `acc_shift = 10·acc + (digit - 48)`, `acc' = (acc_shift - acc)·s' + acc`.
`acc'` is a quadratic signal in Circom, hence the `share`. -/
def asciiDigitsToScalar.step (st de : F p × F p) : ClapM p (F p × F p) := do
  let s' ← st.1 - de.2
  let c10 ← mkF 10
  let c48 ← mkF 48
  let t ← c10 * st.2
  let d' ← de.1 - c48
  let shift ← t + d'
  let diff ← shift - st.2
  let m ← diff * s'
  let acc' ← m + st.2
  let acc'' ← share acc'
  return (s', acc'')

/-- Everything after the digit check: the index flags, their sum asserted to be `1`, and the
accumulator loop. -/
def asciiDigitsToScalar.accumulate [p.AtLeastTwo] {w : ℕ} (inp : FString p (w + 1)) :
    ClapM p (F p) := do
  let hot ← oneHotRaw (w + 1) inp.len
  let ieq : FArray p w := hot.tail.cast (Nat.add_sub_cancel w 1)
  let ieqSum ← FArray.sum ieq
  let one ← mkF 1
  assert_eq ieqSum one
  let c48 ← mkF 48
  let acc0 ← inp.data[0] - c48
  let digits : FVec p w := inp.data.tail.cast (Nat.add_sub_cancel w 1)
  let final ← (digits.zip ieq).foldlM asciiDigitsToScalar.step (one, acc0)
  return final.2

/-- The ASCII digits `inp.data[0, len)` as one field element

Satisfiable exactly when `1 ≤ len ≤ w`, `len = MAX_LEN` is
rejected, and so is `MAX_LEN = 1`), every position is below `2^9` and the first `len` are
digits. Like Circom, it does not detect a number reaching `p`

Circom's `index_eq[i-1]` is a hint, constrained only by `index_eq[i-1]·(len - i) = 0` and by the
sum being 1. Here it is the tail of `oneHotRaw`, which pins the same values. -/
def asciiDigitsToScalar [p.AtLeastTwo] {w : ℕ} (inp : FString p (w + 1)) : ClapM p (F p) := do
  assertIsAsciiDigits inp
  asciiDigitsToScalar.accumulate inp

namespace asciiDigitsToScalar

/-- What `step` computes. -/
def stepPure (st de : ZMod p × ZMod p) : ZMod p × ZMod p :=
  (st.1 - de.2, (10 * st.2 + (de.1 - 48) - st.2) * (st.1 - de.2) + st.2)

/-- What the circuit computes for any `len`: the digits up to `len` when `1 ≤ len ≤ w`, and
otherwise all `w + 1` of them, because no `index_eq` fires and `s` stays `1` -/
def value {w : ℕ} (vals : Vector (ZMod p) (w + 1)) (len : ℕ) : ZMod p :=
  digitsValue vals (if 0 < len ∧ len ≤ w then len else w + 1)

lemma value_of {w : ℕ} {vals : Vector (ZMod p) (w + 1)} {len : ℕ} (h0 : 0 < len) (hw : len ≤ w) :
    value vals len = digitsValue vals len := by
  simp [value, h0, hw]

private lemma digitsValue_succ {n : ℕ} (vals : Vector (ZMod p) n) (k : ℕ) (hk : k < n) :
    digitsValue vals (k + 1) = 10 * digitsValue vals k + (vals[k] - 48) := by
  unfold digitsValue
  rw [List.take_add_one, List.foldl_append]
  simp [hk]

/-- The loop invariant: after `k` iterations, `(s, acc)` is `(0, value up to len)` if `len` was
among the first `k` indices, and `(1, value of the first k + 1 digits)` otherwise. -/
private lemma fold_take {w : ℕ} (D : Vector (ZMod p) (w + 1)) (L : ℕ) :
    ∀ k, k ≤ w →
      (((Vector.ofFn fun i : Fin w ↦ (D[i.val + 1], if i.val + 1 = L then (1 : ZMod p) else 0)
        ).toList.take k).foldl stepPure (1, D[0] - 48)) =
        if 0 < L ∧ L ≤ k then (0, digitsValue D L) else (1, digitsValue D (k + 1))
  | 0, _ => by
    simp only [List.take_zero, List.foldl_nil, Nat.le_zero, show ¬(0 < L ∧ L = 0) by omega,
      if_false]
    rw [digitsValue_succ D 0 (by omega)]
    simp [digitsValue]
  | k + 1, hk => by
    rw [List.take_add_one, List.foldl_append, fold_take D L k (by omega)]
    simp only [Vector.toList_ofFn, List.getElem?_ofFn, show k < w by omega, dite_true,
      Option.toList_some, List.foldl_cons, List.foldl_nil]
    by_cases h1 : 0 < L ∧ L ≤ k
    · have hne : ¬ (k + 1 = L) := by omega
      simp [h1, hne, stepPure, show 0 < L ∧ L ≤ k + 1 by omega]
    · by_cases h2 : L = k + 1
      · subst h2
        simp [stepPure]
      · have h3 : ¬ (0 < L ∧ L ≤ k + 1) := by omega
        have hne : ¬ (k + 1 = L) := by omega
        simp only [h1, h3, hne, if_false, stepPure, sub_zero, mul_one]
        rw [digitsValue_succ D (k + 1) (by omega)]
        ring_nf

private lemma step_convertsM
  {state : ClapMState p}
  {st de : F p × F p}
  {st_val de_val : ZMod p × ZMod p}
  (h_st : Converts FPair.conversion state st st_val)
  (h_de : Converts FPair.conversion state de de_val)
:
  ConvertsM FPair.conversion (step st de) state (stepPure st_val de_val) True
:= by
  have h_s := FPair.converts_fst h_st
  have h_a := FPair.converts_snd h_st
  have h_d := FPair.converts_fst h_de
  have h_e := FPair.converts_snd h_de
  clear h_st h_de
  unfold step
  step mkSub.convertsM h_s h_e as s'
  step mkF.convertsM as c10
  step mkF.convertsM as c48
  step mkMul.convertsM h_c10 h_a as t
  step mkSub.convertsM h_d h_c48 as d'
  step mkAdd.convertsM h_t h_d' as shift
  step mkSub.convertsM h_shift h_a as diff
  step mkMul.convertsM h_diff h_s' as m
  step mkAdd.convertsM h_m h_a as acc'
  step share.convertsM h_acc' as acc''
  apply convertsM_pure
  · exact FPair.converts_intro h_s' h_acc''
  · trivial

/-- The number of `i ∈ [1, w]` equal to `L`. -/
private lemma sum_flags {w L : ℕ} :
    ∑ i : Fin w, (if i.val + 1 = L then (1 : ZMod p) else 0) = if 0 < L ∧ L ≤ w then 1 else 0 := by
  split
  · rename_i h
    rw [Fintype.sum_eq_single ⟨L - 1, by omega⟩]
    · simp [show L - 1 + 1 = L by omega]
    · intro i hi
      have : i.val + 1 ≠ L := fun h' ↦ hi (Fin.ext (by simp; omega))
      simp [this]
  · rename_i h
    apply Finset.sum_eq_zero
    intro i _
    have : i.val + 1 ≠ L := by omega
    simp [this]

namespace accumulate

lemma convertsM
  [p.AtLeastTwo]
  {w : ℕ}
  {state : ClapMState p}
  {inp : FString p (w + 1)}
  {data_vals : Vector (ZMod p) (w + 1)}
  {len_val : ZMod p}
  (h_data : Converts FVec.conversion state inp.data data_vals)
  (h_len : Converts F.conversion state inp.len len_val)
  (h_w : w + 1 < p)
:
  ConvertsM F.conversion (accumulate inp) state (value data_vals len_val.val)
    (0 < len_val.val ∧ len_val.val ≤ w)
:= by
  unfold accumulate
  step oneHotRaw.convertsM h_len h_w as hot
  dsimp only
  have h_ieq := FArray.converts_vector_cast (FArray.converts_tail h_hot) (Nat.add_sub_cancel w 1)
  step FArray.sum.convertsM h_ieq as ieqSum
  -- the flags are `[i + 1 = len]`, so they sum to `[len ∈ [1, w]]`
  have h_flags : (Vector.cast (Nat.add_sub_cancel w 1)
      (Vector.ofFn fun x : Fin (w + 1) ↦ x.val == len_val.val).tail).map
        (fun x ↦ if x = true then (1 : ZMod p) else 0) =
      Vector.ofFn (fun i : Fin w ↦ if i.val + 1 = len_val.val then (1 : ZMod p) else 0) := by
    ext i hi
    simp [beq_iff_eq, Nat.add_comm]
  have h_sum := converts_of_converts h_ieqSum
    (by rw [h_flags, ← Vector.sum_toList, Vector.toList_ofFn, List.sum_ofFn, sum_flags])
  clear h_ieqSum
  step mkF.convertsM as one
  step assert_eq.convertsM h_sum h_one as chk
  step mkF.convertsM as c48
  step mkSub.convertsM (FVec.converts_getElem h_data (Nat.zero_lt_succ w)) h_c48 as acc0
  dsimp only
  have h_digits := FVec.converts_vector_cast (FVec.converts_tail h_data) (Nat.add_sub_cancel w 1)
  have h_elems := fun i : Fin w ↦
    FVec.converts_zip h_digits (FVec.converts_of_FArray_converts h_ieq) i.isLt
  step (convertsM_foldlM (C_acc := FPair.conversion) (f_spec := stepPure) h_elems
    (FPair.converts_intro h_one h_acc0) step_convertsM) as final
  apply convertsM_pure
  · refine converts_of_converts (FPair.converts_snd h_final) ?_
    have h_zip : (Vector.cast (Nat.add_sub_cancel w 1) data_vals.tail).zip
        (Vector.map (fun x ↦ if x = true then (1 : ZMod p) else 0)
          (Vector.cast (Nat.add_sub_cancel w 1)
            (Vector.ofFn fun x : Fin (w + 1) ↦ x.val == len_val.val).tail)) =
        Vector.ofFn (fun i : Fin w ↦
          (data_vals[i.val + 1], if i.val + 1 = len_val.val then (1 : ZMod p) else 0)) := by
      ext i hi <;> simp [beq_iff_eq, Nat.add_comm]
    have hf := fold_take data_vals len_val.val w le_rfl
    rw [List.take_of_length_le (by simp)] at hf
    rw [h_zip, ← Vector.foldl_toList, hf, value]
    split <;> rfl
  · simp
  · simp

end accumulate

lemma convertsM
  [p.AtLeastTwo]
  {w : ℕ}
  {state : ClapMState p}
  {inp : FString p (w + 1)}
  {data_vals : Vector (ZMod p) (w + 1)}
  {len_val : ZMod p}
  (h_data : Converts FVec.conversion state inp.data data_vals)
  (h_len : Converts F.conversion state inp.len len_val)
  (h_w : w + 1 < p)
  (hw : 2 ^ (minBits' (w + 1) + 1) < p)
  (hp : 2 ^ 10 < p)
:
  ConvertsM F.conversion (asciiDigitsToScalar inp) state (value data_vals len_val.val)
    ((∀ i : Fin (w + 1), data_vals[i].val < 2 ^ 9) ∧ 0 < len_val.val ∧ len_val.val ≤ w ∧
      ∀ i : Fin (w + 1), i.val < len_val.val → 48 ≤ data_vals[i].val ∧ data_vals[i].val ≤ 57)
:= by
  unfold asciiDigitsToScalar
  have hA := assertIsAsciiDigits.convertsM h_data h_len h_w hw hp
  apply convertsM_of_convertsM (convertsM_bind_and (function := fun _ ↦ accumulate inp) hA
    (accumulate.convertsM (converts_skip hA h_data) (converts_skip hA h_len) h_w))
  · rfl
  · have h_pow := lt_two_pow_minBits' (w + 1)
    constructor
    · rintro ⟨⟨h_bytes, -, -, -, h_digits⟩, h_len0, h_lenw⟩
      exact ⟨h_bytes, h_len0, h_lenw, h_digits⟩
    · rintro ⟨h_bytes, h_len0, h_lenw, h_digits⟩
      exact ⟨⟨h_bytes, by omega, h_len0, by omega, h_digits⟩, h_len0, h_lenw⟩

/-- The decimal number a list of ASCII digits spells. -/
def decimalValue (l : List Char) : ℕ := l.foldl (fun n c ↦ 10 * n + (c.toNat - 48)) 0

private lemma foldl_digits_cast (l : List Char) (hd : ∀ c ∈ l, 48 ≤ c.toNat ∧ c.toNat ≤ 57)
    (acc : ℕ) :
    l.foldl (fun (a : ZMod p) c ↦ 10 * a + (((c.toUInt8.toNat : ℕ) : ZMod p) - 48)) (acc : ZMod p)
      = ((l.foldl (fun n c ↦ 10 * n + (c.toNat - 48)) acc : ℕ) : ZMod p) := by
  induction l generalizing acc with
  | nil => rfl
  | cons c l ih =>
    have hc := hd c (List.mem_cons_self ..)
    have h_byte : c.toUInt8.toNat = c.toNat := by
      show (c.val.toUInt8).toNat = c.val.toNat
      rw [UInt32.toNat_toUInt8]
      exact Nat.mod_eq_of_lt (by change c.toNat < 256; omega)
    rw [List.foldl_cons, List.foldl_cons, ← ih (fun c' hc' ↦ hd c' (List.mem_cons_of_mem _ hc'))]
    congr 1
    rw [h_byte]
    push_cast [Nat.cast_sub hc.1]
    ring

/-- On a digit string encoded by `FString.encodeV`, `digitsValue` is its decimal value, mod `p`. -/
lemma digitsValue_encodeV {w : ℕ} {s : String} (hs : s.length ≤ w)
    (hd : ∀ c ∈ s.toList, 48 ≤ c.toNat ∧ c.toNat ≤ 57) :
    digitsValue (encodeV (p := p) w s) s.length = (decimalValue s.toList : ZMod p) := by
  have h_take : (encodeV (p := p) w s).toList.take s.length =
      s.toList.map fun c ↦ ((c.toUInt8.toNat : ℕ) : ZMod p) := by
    apply List.ext_getElem
    · simp [String.length_toList]; omega
    · intro i h1 h2
      simp only [List.getElem_take, List.getElem_map, Vector.getElem_toList]
      simp [encodeV, show i < s.toList.length by simpa using h2]
  rw [digitsValue, h_take, List.foldl_map, decimalValue]
  have := foldl_digits_cast (p := p) s.toList hd 0
  rwa [Nat.cast_zero] at this

/-- `asciiDigitsToScalar` of a digit string `s`, `1 ≤ s.length ≤ w`, encoded by `FString.encodeV`
(as `FString.conversion` gives), computes the number `s` spells, mod `p`. -/
lemma value_encodeV {w : ℕ} {s : String} (h0 : 0 < s.length) (hw : s.length ≤ w)
    (hd : ∀ c ∈ s.toList, 48 ≤ c.toNat ∧ c.toNat ≤ 57) :
    value (encodeV (p := p) (w + 1) s) s.length = (decimalValue s.toList : ZMod p) := by
  rw [value_of h0 hw, digitsValue_encodeV (by omega) hd]

end asciiDigitsToScalar

end asciiDigitsToScalar

section examples

/-! ASCII: `'0' = 48` … `'9' = 57`.

They cannot run through `Circuit.toWg` / `Circuit.toCs`: the witness generator evaluates every
expression once, from the public inputs alone, so a `share` of an expression over an earlier
witness (here the accumulator over `isZero` outputs) finds no value and panics. The same defect
stops `poseidonBN254` from lowering. So these check the *value* in the varStore the circuit's own
semantics produces, not satisfiability; the old `= none` vectors, which are about the
constraints, are carried as comments below. `q` exceeds every value, so nothing wraps. -/

private abbrev q : ℕ := 65537

local instance instFactPrimeAsciiDigitsToScalarQ : Fact (Nat.Prime q) := ⟨by norm_num⟩

private def toScalar {n : ℕ} (d : Vector (ZMod q) (n + 1)) (len : ZMod q) : Option (ZMod q) :=
  let cmd : ClapM q (HashConsSt q × ExprRef) := do
    let data ← d.mapM (fun x ↦ liftM (HashConsM.mkConstant (p := q) x))
    let l ← liftM (HashConsM.mkConstant (p := q) len)
    let r ← asciiDigitsToScalar ⟨data, l⟩
    let σ ← getThe (HashConsSt q)
    return (σ, r)
  let Γ := cmd.getVarStore {} 0 {}
  let r := (cmd.run 0 {}).1.1.1
  [Γ, r.1|r.2]

example : toScalar #v[55, 0, 0] 1 = some 7 := by native_decide
example : toScalar #v[49, 50, 0] 2 = some 12 := by native_decide
example : toScalar #v[49, 50, 51, 0] 3 = some 123 := by native_decide
example : toScalar #v[49, 50, 51, 52, 53, 0] 5 = some 12345 := by native_decide
example : toScalar #v[48, 0, 0] 1 = some 0 := by native_decide
example : toScalar #v[51, 48, 53, 0] 3 = some 305 := by native_decide
example : toScalar #v[57, 56, 55, 54, 0] 4 = some 9876 := by native_decide
-- non-digit padding past `len` is ignored
example : toScalar #v[52, 50, 100, 100] 2 = some 42 := by native_decide
-- out of range the value is `value`'s fallback, all `w + 1` positions; slot 5 rejects these
example : toScalar #v[49, 50, 51] 3 = some 123 := by native_decide
example : toScalar #v[49, 50, 51] 0 = some 123 := by native_decide

/- The old model's rejections, which are statements about slot 5 and so cannot be evaluated:
- `#v[49, 50, 51]` at `len = 3` and `#v[57, 56, 55, 54]` at `len = 4`: `len = MAX_LEN`.
- `#v[49, 50, 51]` at `len = 0`.
- `#v[55]` at `len = 1`: `MAX_LEN = 1`.
- `#v[65, 49, 0]` at `len = 2`: `'A' = 65` is not a digit. -/

end examples

end Clap.Lang.FString
