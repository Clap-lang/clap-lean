import Clap.Lang.Core.Combinators.foldlM
import Clap.Lang.Core.Combinators.ofFnM
import Clap.Lang.Core.FB.eq
import Clap.Lang.Data.FString.assertIsAsciiDigits
import Clap.Lang.Gate.eq0
import Clap.Lang.Gate.share

namespace Clap.Lang.FString

variable {p : ℕ}

section asciiDigitsToScalar

/-- The first `len` entries of `vals`, read as ASCII decimal digits, most significant first:
`Σ (vals[j] - 48) · 10^(len-1-j)`, in `ZMod p`, so it wraps once the number reaches `p`. -/
def digitsValue {n : ℕ} (vals : Vector (ZMod p) n) (len : ℕ) : ZMod p :=
  (vals.toList.take len).foldl (fun a d ↦ 10 * a + (d - 48)) 0

/-- One iteration of Circom's loop, on `(s, accumulators[i-1])` and `(digits[i], i)`.

Circom's `index_eq[i-1]` is a hint (`<--`) checked by one constraint. There is no hint gate, so the
flag comes from `eq len i`, an `isZero (len - i)`: its witnessed inverse stands in for the hint, and
its second constraint, `(len - i) · index_eq = 0`, is Circom's. -/
def asciiDigitsToScalar.step [p.AtLeastTwo] (len : F p) (st de : F p × F p) : ClapM p (F p × F p) := do
  -- Circom: `index_eq[i-1] <-- (len == i) ? 1 : 0;` and `index_eq[i-1] * (len-i) === 0;`
  let ieq ← eq len de.2
  -- Circom: `s = s - index_eq[i - 1];`
  let s' ← st.1 - ieq
  -- Circom: `acc_shifts[i - 1] <== 10 * accumulators[i - 1] + (digits[i] - 48);`, linear, so no
  -- `share`
  let t ← (← mkF 10) * st.2
  let d' ← de.1 - (← mkF 48)
  let shift ← t + d'
  -- Circom: `accumulators[i] <== (acc_shifts[i - 1] - accumulators[i - 1])*s + accumulators[i - 1];`
  let diff ← shift - st.2
  let m ← diff * s'
  let acc' ← m + st.2
  let acc'' ← share acc'
  return (s', acc'')

def asciiDigitsToScalar [p.AtLeastTwo] {w : ℕ} (inp : FString p (w + 1)) : ClapM p (F p) := do
  -- Circom: `AssertIsAsciiDigits(MAX_LEN)(digits, len);`
  assertIsAsciiDigits inp
  -- Circom: `accumulators[0] <== digits[0]-48;`
  let acc0 ← inp.data[0] - (← mkF 48)
  -- Circom: `var s = 1;` and `for (var i=1; i < MAX_LEN; i++) { … }`, one `step` per `i`
  let one ← mkF 1
  let idx ← Vector.ofFnM fun i : Fin w ↦ mkF (((i.val + 1 : ℕ)) : ZMod p)
  -- Circom: `signal input digits[MAX_LEN];`, from `digits[1]` on: the `digits[i]`,
  -- `i ∈ [1, MAX_LEN)`, the loop reads. `digits[0]` is `acc0`
  let digits : FVec p w := inp.data.tail.cast (Nat.add_sub_cancel w 1)
  let final ← (digits.zip idx).foldlM (asciiDigitsToScalar.step inp.len) (one, acc0)
  -- Circom: `index_eq_sum ==> success;` and `success === 1;`. The sum is `1 - s`, so this is `s = 0`
  eq0 final.1
  -- Circom: `out <== accumulators[MAX_LEN - 1];`
  return final.2

namespace asciiDigitsToScalar

/-- What `step` computes, given the flag `index_eq[i-1]` in place of `i`. -/
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

/-- The loop invariant, Circom's comment on `accumulators`: after `k` iterations, `(s, acc)` is
`(0, value up to len)` if `len` was among the first `k` indices, and `(1, value of the first k + 1
digits)` otherwise. -/
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
  [p.AtLeastTwo]
  {state : ClapMState p}
  {len : F p}
  {len_val : ZMod p}
  {st de : F p × F p}
  {st_val de_val : ZMod p × ZMod p}
  (h_len : Converts F.conversion state len len_val)
  (h_st : Converts FPair.conversion state st st_val)
  (h_de : Converts FPair.conversion state de de_val)
:
  ConvertsM FPair.conversion (step len st de) state
    (stepPure st_val (de_val.1, if len_val = de_val.2 then 1 else 0)) True
:= by
  have h_s := FPair.converts_fst h_st
  have h_a := FPair.converts_snd h_st
  have h_d := FPair.converts_fst h_de
  have h_e := FPair.converts_snd h_de
  clear h_st h_de
  unfold step
  step eq.convertsM h_len h_e as ieq
  step mkSub.convertsM h_s (F.converts_of_FB_converts h_ieq) as s'
  step mkF.convertsM as c10
  step mkMul.convertsM h_c10 h_a as t
  step mkF.convertsM as c48
  step mkSub.convertsM h_d h_c48 as d'
  step mkAdd.convertsM h_t h_d' as shift
  step mkSub.convertsM h_shift h_a as diff
  step mkMul.convertsM h_diff h_s' as m
  step mkAdd.convertsM h_m h_a as acc'
  step share.convertsM h_acc' as acc''
  apply convertsM_pure
  · refine converts_of_converts (FPair.converts_intro h_s' h_acc'') ?_
    simp [stepPure, beq_iff_eq]
  · trivial

/-- `asciiDigitsToScalar` computes `value`, which is the number the first `len` digits spell,
mod `p`, whenever the constraints hold (`value_of`). The constraints, purpose first, with the
Circom line each comes from:
- the first `len` positions are ASCII digits: `AssertIsAsciiDigits`'
  `(1 - is_ascii_digit) * selector[i] === 0`;
- `0 < len`: `ArraySelector(0, len)`'s `start_idx < end_idx`;
- `len ≤ w`, i.e. `len < MAX_LEN`: `success === 1`, as `index_eq` only covers `[1, MAX_LEN)`. So
  `len = MAX_LEN` is rejected, and every input when `w = 0`;
- every position is a byte: `Num2Bits(9)(in[i])`, at 8 bits.

`assertIsAsciiDigits`' own `len < 2 ^ minBits' (w + 1)` and `0 < w + 1` follow from these. -/
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
  (hp : 2 ^ 9 < p)
:
  ConvertsM F.conversion (asciiDigitsToScalar inp) state (value data_vals len_val.val)
    ((∀ i : Fin (w + 1), i.val < len_val.val → 48 ≤ data_vals[i].val ∧ data_vals[i].val ≤ 57) ∧
      0 < len_val.val ∧ len_val.val ≤ w ∧ ∀ i : Fin (w + 1), data_vals[i].val < 2 ^ 8)
:= by
  unfold asciiDigitsToScalar
  -- `assertIsAsciiDigits` and the final `eq0` both assert, so the first bind is
  -- `convertsM_bind_and`. Clearing the pre-state hypotheses keeps the later `step`s from
  -- reframing them through `assertIsAsciiDigits` (a `whnf` timeout).
  have hA := assertIsAsciiDigits.convertsM h_data h_len h_w hw hp
  have h_data1 := converts_skip hA h_data
  have h_len1 := converts_skip hA h_len
  refine convertsM_of_convertsM (convertsM_bind_and (function_val := value data_vals len_val.val)
    (constraints2 := 0 < len_val.val ∧ len_val.val ≤ w) hA ?_) rfl ?_
  · clear hA h_data h_len
    step mkF.convertsM as c48
    step mkSub.convertsM (FVec.converts_getElem h_data1 (Nat.zero_lt_succ w)) h_c48 as acc0
    step mkF.convertsM as one
    step (convertsM_ofFnM (vals := Vector.ofFn fun i : Fin w ↦ (((i.val + 1 : ℕ)) : ZMod p))
      (fun i _ ↦ by
        simp only [Fin.getElem_fin, Vector.getElem_ofFn]
        exact mkF.convertsM)) as idx
    dsimp only
    have h_digits := FVec.converts_vector_cast (FVec.converts_tail h_data1) (Nat.add_sub_cancel w 1)
    have h_elems := fun i : Fin w ↦ FVec.converts_zip h_digits h_idx i.isLt
    step (convertsM_foldlM_ctx (C_acc := FPair.conversion)
      (f_spec := fun (l : ZMod p) (st de : ZMod p × ZMod p) ↦
        stepPure st (de.1, if l = de.2 then 1 else 0)) h_len1 h_elems
      (FPair.converts_intro h_one h_acc0) step_convertsM) as final
    -- The flag `len_val = i + 1` is `[i + 1 = len]`, so the loop is `fold_take`'s.
    have h_zip : ((Vector.cast (Nat.add_sub_cancel w 1) data_vals.tail).zip
          (Vector.ofFn fun i : Fin w ↦ (((i.val + 1 : ℕ)) : ZMod p))).toList.map
          (fun de ↦ (de.1, if len_val = de.2 then (1 : ZMod p) else 0)) =
        (Vector.ofFn (fun i : Fin w ↦
          (data_vals[i.val + 1], if i.val + 1 = len_val.val then (1 : ZMod p) else 0))).toList := by
      apply List.ext_getElem
      · simp
      · intro i h1 h2
        have hi : i < w := by simpa using h2
        have h_iff : len_val = (i : ZMod p) + 1 ↔ i + 1 = len_val.val := by
          rw [show (i : ZMod p) + 1 = ((i + 1 : ℕ) : ZMod p) by push_cast; rfl]
          constructor
          · rintro rfl; rw [ZMod.val_natCast_of_lt (by omega)]
          · intro h; rw [h, ZMod.natCast_zmod_val]
        simp [h_iff, Nat.add_comm 1]
    have hf := fold_take data_vals len_val.val w le_rfl
    rw [List.take_of_length_le (by simp)] at hf
    have h_fold : Vector.foldl (fun st de ↦ stepPure st (de.1, if len_val = de.2 then 1 else 0))
        (1, data_vals[0] - 48)
        ((Vector.cast (Nat.add_sub_cancel w 1) data_vals.tail).zip
          (Vector.ofFn fun i : Fin w ↦ (((i.val + 1 : ℕ)) : ZMod p))) =
        if 0 < len_val.val ∧ len_val.val ≤ w then (0, digitsValue data_vals len_val.val)
        else (1, digitsValue data_vals (w + 1)) := by
      rw [← Vector.foldl_toList, ← hf, ← h_zip, List.foldl_map]
    have h_out := converts_of_converts h_final h_fold
    clear h_final
    step eq0.convertsM (FPair.converts_fst h_out) as chk
    apply convertsM_pure
    · refine converts_of_converts (FPair.converts_snd h_out) ?_
      rw [value]; split <;> rfl
    · split <;> simp_all
    · split <;> simp_all
  · have h_pow := lt_two_pow_minBits' (w + 1)
    constructor
    · rintro ⟨⟨h_digits, h_len0, -, -, h_bytes⟩, -, h_lenw⟩
      exact ⟨h_digits, h_len0, h_lenw, h_bytes⟩
    · rintro ⟨h_digits, h_len0, h_lenw, h_bytes⟩
      exact ⟨⟨h_digits, h_len0, by omega, by omega, h_bytes⟩, h_len0, h_lenw⟩

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

/-- A digit list spells a number below `10 ^ length`, so its value does not wrap when
`10 ^ length ≤ p`. -/
lemma decimalValue_lt (l : List Char) (hd : ∀ c ∈ l, 48 ≤ c.toNat ∧ c.toNat ≤ 57) :
    decimalValue l < 10 ^ l.length := by
  unfold decimalValue
  suffices ∀ n, l.foldl (fun n c ↦ 10 * n + (c.toNat - 48)) n < (n + 1) * 10 ^ l.length by
    simpa using this 0
  induction l with
  | nil => intro n; simp
  | cons c l ih =>
    intro n
    have hc := hd c (List.mem_cons_self ..)
    rw [List.foldl_cons]
    refine lt_of_lt_of_le (ih (fun c' h' ↦ hd c' (List.mem_cons_of_mem _ h')) _) ?_
    rw [List.length_cons, pow_succ]
    calc (10 * n + (c.toNat - 48) + 1) * 10 ^ l.length
        ≤ (10 * n + 10) * 10 ^ l.length := Nat.mul_le_mul_right _ (by omega)
      _ = (n + 1) * (10 ^ l.length * 10) := by ring

/-- `convertsM` for the encoding of a string `s` (as `FString.conversion` gives) of at most `w + 1`
characters, each below 256: the circuit accepts exactly the strings of `1` to `w` decimal digits,
and computes the number they spell, mod `p` (`decimalValue_lt` bounds it). On the strings it
rejects the value is still `value`'s, as the value slot must be right for every input. -/
lemma convertsM_string
  [p.AtLeastTwo]
  {w : ℕ}
  {state : ClapMState p}
  {inp : FString p (w + 1)}
  {s : String}
  (h_inp : Converts FString.conversion state inp s)
  (h_s_len : s.length ≤ w + 1)
  (h_chars : ∀ c ∈ s.toList, c.toNat < 256)
  (h_w : w + 1 < p)
  (hw : 2 ^ (minBits' (w + 1) + 1) < p)
  (hp : 2 ^ 9 < p)
:
  ConvertsM F.conversion (asciiDigitsToScalar inp) state
    (if 0 < s.length ∧ s.length ≤ w ∧ ∀ c ∈ s.toList, 48 ≤ c.toNat ∧ c.toNat ≤ 57
      then (decimalValue s.toList : ZMod p) else value (encodeV (w + 1) s) s.length)
    (0 < s.length ∧ s.length ≤ w ∧ ∀ c ∈ s.toList, 48 ≤ c.toNat ∧ c.toNat ≤ 57)
:= by
  apply convertsM_of_convertsM
    (convertsM (FString.converts_data h_inp) (FString.converts_len h_inp) h_w hw hp)
  · rw [ZMod.val_natCast_of_lt (show s.length < p by omega)]
    split
    · rename_i h
      exact value_encodeV h.1 h.2.1 h.2.2
    · rfl
  · have h_list : s.toList.length = s.length := by simp [String.length_toList]
    rw [ZMod.val_natCast_of_lt (show s.length < p by omega)]
    -- The `i`-th slot, for `i < s.length`, is the `i`-th character.
    have h_at : ∀ (i : ℕ) (hi_w : i < w + 1) (hi : i < s.toList.length),
        ((encodeV (p := p) (w + 1) s)[i]'hi_w).val = (s.toList[i]'hi).toNat := by
      intro i hi_w hi
      have hc := h_chars _ (List.getElem_mem hi)
      rw [encodeV_getElem_of_lt hi_w hi, toUInt8_toNat_of_lt hc,
        ZMod.val_natCast_of_lt (by omega)]
    constructor
    · rintro ⟨h_digits, h_len0, h_lenw, -⟩
      refine ⟨h_len0, h_lenw, fun c hc ↦ ?_⟩
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
      have h := h_digits ⟨i, by omega⟩ (show i < s.length by omega)
      simp only [Fin.getElem_fin] at h
      rwa [h_at i (by omega) hi] at h
    · rintro ⟨h_len0, h_lenw, h_digits⟩
      refine ⟨fun i hi ↦ ?_, h_len0, h_lenw,
        fun i ↦ lt_of_lt_of_le (encodeV_val_lt i.isLt) (by norm_num)⟩
      simp only [Fin.getElem_fin]
      rw [h_at i.val i.isLt (by omega)]
      exact h_digits _ (List.getElem_mem _)

end asciiDigitsToScalar

end asciiDigitsToScalar

section examples

/-! ASCII: `'0' = 48` … `'9' = 57`. -/

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
-- like Circom, the number wraps mod `p`: "65538" is `65537 + 1`
example : toScalar #v[54, 53, 53, 51, 56, 0] 5 = some 1 := by native_decide

/- The old model's rejections, which are statements about slot 5 and so cannot be evaluated.
Each falsifies a conjunct of `asciiDigitsToScalar.convertsM`'s constraint:
- `#v[49, 50, 51]` at `len = 3` and `#v[57, 56, 55, 54]` at `len = 4`: `len ≤ w`, as
  `len = MAX_LEN`.
- `#v[49, 50, 51]` at `len = 0`: `0 < len`.
- `#v[55]` at `len = 1`: `len ≤ w`, with `w = 0` (`MAX_LEN = 1`).
- `#v[65, 49, 0]` at `len = 2`: the digits, as `'A' = 65` is not one. -/

end examples

end Clap.Lang.FString
