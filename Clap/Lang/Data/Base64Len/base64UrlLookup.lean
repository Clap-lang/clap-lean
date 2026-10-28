import Clap.Lang.Core.F.lessThan
import Clap.Lang.Core.F.mkAdd
import Clap.Lang.Core.F.mkMul
import Clap.Lang.Core.F.mkSub
import Clap.Lang.Core.FB.and
import Clap.Lang.Core.FB.eq
import Clap.Lang.Gate.eq0
import Clap.Lang.Gate.isZero
import Clap.Lang.Gate.share

namespace Clap.Lang.Base64

variable {p : ℕ}

def base64UrlLookup.rangeFlag (a b : ℕ) (i : F p) : ClapM p (FB p) := do
  -- Circom: `component le = LessThan(8); le.in[0] <== in; le.in[1] <== b;`
  let le ← lessThan 8 i (← mkF (b : ZMod p))
  -- Circom: `component ge = GreaterThan(8); ge.in[0] <== in; ge.in[1] <== a;`
  let ge ← greaterThan 8 i (← mkF (a : ZMod p))
  -- Circom: `signal range <== ge.out * le.out;`
  share (← FB.and ge le)

def base64UrlLookup [p.AtLeastTwo] (i : F p) : ClapM p (F p) := do
  -- Circom: `// ['A', 'Z']`, with `LessThan(8)` against `90+1`, `GreaterThan(8)` against `65-1`
  let range_AZ ← base64UrlLookup.rangeFlag 64 91 i
  -- Circom: `signal sum_AZ <== range_AZ * (in - 65);`
  let sum_AZ ← share (← mkMul range_AZ (← mkSub i (← mkF 65)))
  -- Circom: `// ['a', 'z']`, against `122+1` and `97-1`
  let range_az ← base64UrlLookup.rangeFlag 96 123 i
  -- Circom: `signal sum_az <== sum_AZ + range_az * (in - 71);`
  let sum_az ← share (← mkAdd sum_AZ (← mkMul range_az (← mkSub i (← mkF 71))))
  -- Circom: `// ['0', '9']`, against `57+1` and `48-1`
  let range_09 ← base64UrlLookup.rangeFlag 47 58 i
  -- Circom: `signal sum_09 <== sum_az + range_09 * (in + 4);`
  let sum_09 ← share (← mkAdd sum_az (← mkMul range_09 (← mkAdd i (← mkF 4))))
  -- Circom: `component equal_minus = IsZero(); equal_minus.in <== in - 45;`
  let equal_minus ← eq i (← mkF 45)
  -- Circom: `signal sum_minus <== sum_09 + equal_minus.out * 62;`, linear, so no `share`
  let sum_minus ← mkAdd sum_09 (← mkMul equal_minus (← mkF 62))
  -- Circom: `component equal_underscore = IsZero(); equal_underscore.in <== in - 95;`
  let equal_underscore ← eq i (← mkF 95)
  -- Circom: `signal sum_underscore <== sum_minus + equal_underscore.out * 63;`, linear
  let sum_underscore ← mkAdd sum_minus (← mkMul equal_underscore (← mkF 63))
  -- Circom: `component equal_eqsign = IsZero(); equal_eqsign.in <== in - 61;`
  let equal_eqsign ← eq i (← mkF 61)
  -- Circom: `component zero_padding = IsZero(); zero_padding.in <== in;`
  let zero_padding ← isZero i
  -- Circom: `signal result <== range_AZ + range_az + range_09 + equal_minus.out
  --   + equal_underscore.out + equal_eqsign.out + zero_padding.out;`, linear
  let result ← mkAdd range_AZ range_az
  let result ← mkAdd result range_09
  let result ← mkAdd result equal_minus
  let result ← mkAdd result equal_underscore
  let result ← mkAdd result equal_eqsign
  let result ← mkAdd result zero_padding
  -- Circom: `1 === result;`
  eq0 (← mkSub result (← mkF 1))
  -- Circom: `out <== sum_underscore;`
  return sum_underscore

namespace base64UrlLookup

/-- `rangeFlag a b` at any input: the raw bits of `GreaterThan(8)(in, a)` and `LessThan(8)(in, b)`. -/
def flagRaw (a b : ℕ) (v : ZMod p) : Bool :=
  lessThan.lessThanRaw 8 (a : ZMod p) v && lessThan.lessThanRaw 8 v (b : ZMod p)

/-- The constraint `rangeFlag a b` emits: both comparators' `Num2Bits(9)` range checks. -/
def flagOk (a b : ℕ) (v : ZMod p) : Prop :=
  lessThan.lessThanOk 8 v (b : ZMod p) ∧ lessThan.lessThanOk 8 (a : ZMod p) v

/-- The base64url index of a byte: `A`–`Z` ↦ 0–25, `a`–`z` ↦ 26–51, `0`–`9` ↦ 52–61, `-` ↦ 62, `_` ↦ 63, and 0 off the alphabet. -/
def index (n : ℕ) : ℕ :=
  if 65 ≤ n ∧ n ≤ 90 then n - 65
  else if 97 ≤ n ∧ n ≤ 122 then n - 71
  else if 48 ≤ n ∧ n ≤ 57 then n + 4
  else if n = 45 then 62
  else if n = 95 then 63
  else 0

/-- The 66 inputs the circuit accepts: NUL, `-`, `_`, `=`, `A`–`Z`, `a`–`z` and `0`–`9`. -/
def accepts (n : ℕ) : Prop :=
  n = 0 ∨ n = 45 ∨ n = 95 ∨ n = 61 ∨ (65 ≤ n ∧ n ≤ 90) ∨ (97 ≤ n ∧ n ≤ 122) ∨ (48 ≤ n ∧ n ≤ 57)

instance (n : ℕ) : Decidable (accepts n) := by unfold accepts; infer_instance

def value (v : ZMod p) : ZMod p :=
  (if flagRaw 64 91 v then v - 65 else 0) + (if flagRaw 96 123 v then v - 71 else 0)
    + (if flagRaw 47 58 v then v + 4 else 0) + (if v = 45 then 62 else 0)
    + (if v = 95 then 63 else 0)

def result (v : ZMod p) : ZMod p :=
  (if flagRaw 64 91 v then 1 else 0) + (if flagRaw 96 123 v then 1 else 0)
    + (if flagRaw 47 58 v then 1 else 0) + (if v = 45 then 1 else 0) + (if v = 95 then 1 else 0)
    + (if v = 61 then 1 else 0) + (if v = 0 then 1 else 0)

/-- The top bit of the offset, read arithmetically. -/
private lemma lessThanRaw_eq_decide (h_p : 2 < p) (x y : ZMod p) :
    lessThan.lessThanRaw 8 x y = decide ((x - y + 2 ^ 8).val / 2 ^ 8 % 2 = 0) := by
  haveI : Fact (1 < p) := ⟨by omega⟩
  unfold lessThan.lessThanRaw
  rw [num2bitsLsbPureV_getElem_last 8 _]
  have hk : (x - y + 2 ^ 8).val / 2 ^ 8 % 2 < 2 := Nat.mod_lt _ (by norm_num)
  generalize (x - y + 2 ^ 8).val / 2 ^ 8 % 2 = k at *
  interval_cases k <;> simp

private lemma mod_of_lt_two_mul {x : ℕ} (h : x < 2 * p) : x % p = if x < p then x else x - p := by
  split
  · exact Nat.mod_eq_of_lt ‹_›
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

/-- The offset of `lessThan 8 a v`, `a - v + 2^8`, in `ℕ`. -/
private lemma val_const_sub [NeZero p] (a : ℕ) (v : ZMod p) :
    ((a : ZMod p) - v + 2 ^ 8).val = (a + 256 + (p - v.val)) % p := by
  rw [← ZMod.val_natCast]
  congr 1
  push_cast [Nat.cast_sub (ZMod.val_lt v).le]
  rw [ZMod.natCast_self, ZMod.natCast_zmod_val]
  ring

/-- The offset of `lessThan 8 v b`, `v - b + 2^8`, in `ℕ`. -/
private lemma val_sub_const [NeZero p] {b : ℕ} (hb : b ≤ 256) (v : ZMod p) :
    (v - (b : ZMod p) + 2 ^ 8).val = (v.val + (256 - b)) % p := by
  rw [← ZMod.val_natCast]
  congr 1
  push_cast [Nat.cast_sub hb]
  rw [ZMod.natCast_zmod_val]
  ring

/-- Whenever both range checks pass, the flag is the exact test `a < v.val < b`, for every field
element -/
lemma flagRaw_eq (h_p : 2 ^ 9 < p) {a b : ℕ} (hab : a < b) (hb : b < 2 ^ 8) {v : ZMod p}
    (h : flagOk a b v) : flagRaw a b v = decide (a < v.val ∧ v.val < b) := by
  haveI : NeZero p := ⟨by omega⟩
  have hn := ZMod.val_lt v
  obtain ⟨h_le, h_ge⟩ := h
  unfold lessThan.lessThanOk at h_le h_ge
  unfold flagRaw
  rw [lessThanRaw_eq_decide (by omega), lessThanRaw_eq_decide (by omega)]
  rw [val_const_sub] at h_ge ⊢
  rw [val_sub_const (by omega)] at h_le ⊢
  rw [mod_of_lt_two_mul (p := p) (x := a + 256 + (p - v.val)) (by omega)] at h_ge ⊢
  rw [mod_of_lt_two_mul (p := p) (x := v.val + (256 - b)) (by omega)] at h_le ⊢
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  norm_num at h_le h_ge ⊢
  split_ifs at h_le h_ge ⊢ <;> omega

/-- On a byte both range checks pass. -/
lemma flagOk_of_lt (h_p : 2 ^ 9 < p) {a b : ℕ} (ha : a < 2 ^ 8) (hb : b < 2 ^ 8) {v : ZMod p}
    (hv : v.val < 2 ^ 8) : flagOk a b v := by
  have hb' : ((b : ℕ) : ZMod p).val < 2 ^ 8 := by rw [ZMod.val_natCast_of_lt (by omega)]; exact hb
  have ha' : ((a : ℕ) : ZMod p).val < 2 ^ 8 := by rw [ZMod.val_natCast_of_lt (by omega)]; exact ha
  exact ⟨lessThan.lessThanOk_of hv hb' h_p, lessThan.lessThanOk_of ha' hv h_p⟩

private lemma eq_natCast_iff [NeZero p] {c : ℕ} (hc : c < p) (v : ZMod p) :
    v = (c : ZMod p) ↔ v.val = c := by
  constructor
  · rintro rfl
    exact ZMod.val_natCast_of_lt hc
  · intro h
    rw [← ZMod.natCast_zmod_val v, h]

/-- Under the three range checks, `result` counts which of the seven classes `v.val` is in. -/
private def count (n : ℕ) : ℕ :=
  (if 64 < n ∧ n < 91 then 1 else 0) + (if 96 < n ∧ n < 123 then 1 else 0)
    + (if 47 < n ∧ n < 58 then 1 else 0) + (if n = 45 then 1 else 0) + (if n = 95 then 1 else 0)
    + (if n = 61 then 1 else 0) + (if n = 0 then 1 else 0)

private lemma result_eq (h_p : 2 ^ 9 < p) {v : ZMod p} (h₁ : flagOk 64 91 v)
    (h₂ : flagOk 96 123 v) (h₃ : flagOk 47 58 v) : result v = (count v.val : ZMod p) := by
  haveI : NeZero p := ⟨by omega⟩
  unfold result count
  rw [flagRaw_eq h_p (by norm_num) (by norm_num) h₁, flagRaw_eq h_p (by norm_num) (by norm_num) h₂,
    flagRaw_eq h_p (by norm_num) (by norm_num) h₃]
  have e45 := eq_natCast_iff (c := 45) (by omega) v
  have e95 := eq_natCast_iff (c := 95) (by omega) v
  have e61 := eq_natCast_iff (c := 61) (by omega) v
  have e0 : v = 0 ↔ v.val = 0 := (ZMod.val_eq_zero v).symm
  push_cast at e45 e95 e61
  simp only [decide_eq_true_eq, e45, e95, e61, e0]
  push_cast
  rfl

lemma constraints_iff (h_p : 2 ^ 9 < p) (v : ZMod p) :
    (flagOk 64 91 v ∧ flagOk 96 123 v ∧ flagOk 47 58 v ∧ result v = 1) ↔ accepts v.val := by
  haveI : Fact (1 < p) := ⟨by omega⟩
  have key : ∀ n, count n = 1 ↔ accepts n := by
    intro n
    unfold count accepts
    split_ifs <;> omega
  constructor
  · rintro ⟨h₁, h₂, h₃, h⟩
    rw [result_eq h_p h₁ h₂ h₃] at h
    have h_val := congrArg ZMod.val h
    have h_le : count v.val ≤ 7 := by unfold count; split_ifs <;> omega
    rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_one] at h_val
    exact (key _).1 h_val
  · intro h
    have hv : v.val < 2 ^ 8 := by unfold accepts at h; omega
    have h₁ := flagOk_of_lt (a := 64) (b := 91) h_p (by norm_num) (by norm_num) hv
    have h₂ := flagOk_of_lt (a := 96) (b := 123) h_p (by norm_num) (by norm_num) hv
    have h₃ := flagOk_of_lt (a := 47) (b := 58) h_p (by norm_num) (by norm_num) hv
    refine ⟨h₁, h₂, h₃, ?_⟩
    rw [result_eq h_p h₁ h₂ h₃, (key _).2 h, Nat.cast_one]

/-- On every byte, the circuit outputs the base64url index. -/
lemma value_of_lt (h_p : 2 ^ 9 < p) {v : ZMod p} (hv : v.val < 2 ^ 8) :
    value v = (index v.val : ZMod p) := by
  haveI : NeZero p := ⟨by omega⟩
  unfold value
  rw [flagRaw_eq h_p (by norm_num) (by norm_num) (flagOk_of_lt h_p (by norm_num) (by norm_num) hv),
    flagRaw_eq h_p (by norm_num) (by norm_num) (flagOk_of_lt h_p (by norm_num) (by norm_num) hv),
    flagRaw_eq h_p (by norm_num) (by norm_num) (flagOk_of_lt h_p (by norm_num) (by norm_num) hv)]
  have e45 := eq_natCast_iff (c := 45) (by omega) v
  have e95 := eq_natCast_iff (c := 95) (by omega) v
  push_cast at e45 e95
  simp only [decide_eq_true_eq, e45, e95]
  have hv' := (ZMod.natCast_zmod_val v).symm
  generalize v.val = n at *
  subst hv'
  unfold index
  split_ifs <;> first
    | (exfalso; omega)
    | (rw [Nat.cast_sub (show 65 ≤ n by omega)]; ring1)
    | (rw [Nat.cast_sub (show 71 ≤ n by omega)]; ring1)
    | (push_cast; ring1)

/-- On the accepted values, the circuit outputs the base64url index. -/
lemma value_of_accepts (h_p : 2 ^ 9 < p) {v : ZMod p} (h : accepts v.val) :
    value v = (index v.val : ZMod p) :=
  value_of_lt h_p (by unfold accepts at h; omega)

namespace rangeFlag

/-- `rangeFlag` on an arbitrary field element: the comparators' raw bits, and their two range
checks as the constraint. -/
lemma convertsM_unchecked
  [p.AtLeastTwo]
  {state : ClapMState p}
  {a b : ℕ}
  {i : F p}
  {v : ZMod p}
  (h_i : Converts F.conversion state i v)
:
  ConvertsM FB.conversion (rangeFlag a b i) state (flagRaw a b v) (flagOk a b v)
:= by
  unfold rangeFlag greaterThan flagRaw flagOk
  step mkF.convertsM as cb
  simp only [true_implies]
  -- Both comparisons assert, so the first is sequenced with `convertsM_bind_and`.
  have h_le := lessThan.convertsM_unchecked (w := 8) h_i h_cb
  have h_i' := converts_skip h_le h_i
  have h_ler := h_le.result
  clear h_i h_cb
  apply convertsM_bind_and h_le
  clear h_le
  generalize (lessThan 8 i cb_result).getResult cb_state.numAlloc cb_state.σ = le_result at *
  generalize (lessThan 8 i cb_result).getState cb_state = le_state at *
  step mkF.convertsM as ca
  simp only [true_implies]
  step lessThan.convertsM_unchecked h_ca h_i' as ge
  step FB.and.convertsM h_ge h_ler as rng
  apply convertsM_of_convertsM
    (FB.convertsM_of_F_convertsM (share.convertsM (F.converts_of_FB_converts h_rng)) ?_)
  · cases lessThan.lessThanRaw 8 (a : ZMod p) v && lessThan.lessThanRaw 8 v (b : ZMod p) <;> simp
  · exact iff_of_true trivial (fun _ h ↦ h)
  · cases lessThan.lessThanRaw 8 (a : ZMod p) v && lessThan.lessThanRaw 8 v (b : ZMod p) <;> simp

/-- On a byte, `rangeFlag a b` is the test `a < v.val < b`, and its range checks cannot fail. -/
lemma convertsM
  [p.AtLeastTwo]
  {state : ClapMState p}
  {a b : ℕ}
  {i : F p}
  {v : ZMod p}
  (h_i : Converts F.conversion state i v)
  (hv : v.val < 2 ^ 8)
  (ha : a < 2 ^ 8)
  (hb : b < 2 ^ 8)
  (h_p : 2 ^ 9 < p)
:
  ConvertsM FB.conversion (rangeFlag a b i) state (decide (a < v.val ∧ v.val < b)) True
:= by
  have ha' : ((a : ℕ) : ZMod p).val < 2 ^ 8 := by rw [ZMod.val_natCast_of_lt (by omega)]; exact ha
  have hb' : ((b : ℕ) : ZMod p).val < 2 ^ 8 := by rw [ZMod.val_natCast_of_lt (by omega)]; exact hb
  apply convertsM_of_convertsM (convertsM_unchecked h_i)
  · rw [flagRaw, lessThan.lessThanRaw_eq ha' hv h_p, lessThan.lessThanRaw_eq hv hb' h_p,
      ZMod.val_natCast_of_lt (show a < p by omega), ZMod.val_natCast_of_lt (show b < p by omega)]
    simp
  · exact iff_true_intro (flagOk_of_lt h_p ha hb hv)

end rangeFlag

lemma convertsM
  [p.AtLeastTwo]
  {state : ClapMState p}
  {m : F p}
  {m_val : ZMod p}
  (h_m : Converts F.conversion state m m_val)
  (h_p : 2 ^ 9 < p)
:
  ConvertsM F.conversion (base64UrlLookup m) state (value m_val) (accepts m_val.val)
:= by
  refine convertsM_of_convertsM (constraints1 := flagOk 64 91 m_val ∧ flagOk 96 123 m_val ∧
    flagOk 47 58 m_val ∧ result m_val = 1) ?_ rfl (constraints_iff h_p m_val)
  unfold base64UrlLookup
  -- `['A', 'Z']`. Each range flag asserts, so it is sequenced with `convertsM_bind_and`.
  have h_AZ := rangeFlag.convertsM_unchecked (a := 64) (b := 91) h_m
  have h_m1 := converts_skip h_AZ h_m
  have h_range_AZ := h_AZ.result
  clear h_m
  apply convertsM_bind_and h_AZ
  clear h_AZ
  generalize (rangeFlag 64 91 m).getResult state.numAlloc state.σ = range_AZ at *
  generalize (rangeFlag 64 91 m).getState state = s_AZ at *
  step mkF.convertsM as c65
  step mkSub.convertsM h_m1 h_c65 as d_AZ
  step mkMul.convertsM (F.converts_of_FB_converts h_range_AZ) h_d_AZ as p_AZ
  step share.convertsM h_p_AZ as sum_AZ
  clear h_c65 h_d_AZ h_p_AZ
  simp only [true_implies]
  -- `['a', 'z']`
  have h_az := rangeFlag.convertsM_unchecked (a := 96) (b := 123) h_m1
  have h_m2 := converts_skip h_az h_m1
  have h_range_AZ' := converts_skip h_az h_range_AZ
  have h_sum_AZ' := converts_skip h_az h_sum_AZ
  have h_range_az := h_az.result
  clear h_m1 h_range_AZ h_sum_AZ
  apply convertsM_bind_and h_az
  clear h_az
  generalize (rangeFlag 96 123 m).getResult sum_AZ_state.numAlloc sum_AZ_state.σ = range_az at *
  generalize (rangeFlag 96 123 m).getState sum_AZ_state = s_az at *
  step mkF.convertsM as c71
  step mkSub.convertsM h_m2 h_c71 as d_az
  step mkMul.convertsM (F.converts_of_FB_converts h_range_az) h_d_az as p_az
  step mkAdd.convertsM h_sum_AZ' h_p_az as t_az
  step share.convertsM h_t_az as sum_az
  clear h_c71 h_d_az h_p_az h_t_az h_sum_AZ'
  simp only [true_implies]
  -- `['0', '9']`
  have h_09 := rangeFlag.convertsM_unchecked (a := 47) (b := 58) h_m2
  have h_m3 := converts_skip h_09 h_m2
  have h_range_AZ'' := converts_skip h_09 h_range_AZ'
  have h_range_az' := converts_skip h_09 h_range_az
  have h_sum_az' := converts_skip h_09 h_sum_az
  have h_range_09 := h_09.result
  clear h_m2 h_range_AZ' h_range_az h_sum_az
  apply convertsM_bind_and h_09
  clear h_09
  generalize (rangeFlag 47 58 m).getResult sum_az_state.numAlloc sum_az_state.σ = range_09 at *
  generalize (rangeFlag 47 58 m).getState sum_az_state = s_09 at *
  step mkF.convertsM as c4
  step mkAdd.convertsM h_m3 h_c4 as d_09
  step mkMul.convertsM (F.converts_of_FB_converts h_range_09) h_d_09 as p_09
  step mkAdd.convertsM h_sum_az' h_p_09 as t_09
  step share.convertsM h_t_09 as sum_09
  clear h_c4 h_d_09 h_p_09 h_t_09 h_sum_az'
  -- From here on `step` alone reframes the live facts, rebuilding each one through
  -- `converts_skip` with the step that consumed it inside. `instantiateMVars` substitutes those
  -- rebuilt proofs, so the proof term doubles per consuming step as a tree (its DAG stays
  -- linear). On e93a313's unsealed chain the tree reached 6·10⁸ nodes after `['0', '9']`, and
  -- the proof did not finish in 13 minutes. `replace h := h` binds each proof once, as a `have`.
  replace h_m3 := h_m3
  replace h_range_AZ'' := h_range_AZ''
  replace h_range_az' := h_range_az'
  replace h_range_09 := h_range_09
  replace h_sum_09 := h_sum_09
  -- `'-'`
  step mkF.convertsM as c45
  step eq.convertsM h_m3 h_c45 as equal_minus
  step mkF.convertsM as c62
  step mkMul.convertsM (F.converts_of_FB_converts h_equal_minus) h_c62 as p_minus
  step mkAdd.convertsM h_sum_09 h_p_minus as sum_minus
  clear h_c45 h_c62 h_p_minus h_sum_09
  replace h_m3 := h_m3
  replace h_range_AZ'' := h_range_AZ''
  replace h_range_az' := h_range_az'
  replace h_range_09 := h_range_09
  replace h_equal_minus := h_equal_minus
  replace h_sum_minus := h_sum_minus
  -- `'_'`
  step mkF.convertsM as c95
  step eq.convertsM h_m3 h_c95 as equal_underscore
  step mkF.convertsM as c63
  step mkMul.convertsM (F.converts_of_FB_converts h_equal_underscore) h_c63 as p_us
  step mkAdd.convertsM h_sum_minus h_p_us as sum_underscore
  clear h_c95 h_c63 h_p_us h_sum_minus
  replace h_m3 := h_m3
  replace h_range_AZ'' := h_range_AZ''
  replace h_range_az' := h_range_az'
  replace h_range_09 := h_range_09
  replace h_equal_minus := h_equal_minus
  replace h_equal_underscore := h_equal_underscore
  replace h_sum_underscore := h_sum_underscore
  -- `'='` and the zero padding
  step mkF.convertsM as c61
  step eq.convertsM h_m3 h_c61 as equal_eqsign
  step isZero.convertsM h_m3 as zero_padding
  clear h_c61 h_m3
  replace h_range_AZ'' := h_range_AZ''
  replace h_range_az' := h_range_az'
  replace h_range_09 := h_range_09
  replace h_equal_minus := h_equal_minus
  replace h_equal_underscore := h_equal_underscore
  replace h_equal_eqsign := h_equal_eqsign
  replace h_zero_padding := h_zero_padding
  replace h_sum_underscore := h_sum_underscore
  -- `result`, then `1 === result`
  step mkAdd.convertsM (F.converts_of_FB_converts h_range_AZ'')
    (F.converts_of_FB_converts h_range_az') as r1
  step mkAdd.convertsM h_r1 (F.converts_of_FB_converts h_range_09) as r2
  step mkAdd.convertsM h_r2 (F.converts_of_FB_converts h_equal_minus) as r3
  step mkAdd.convertsM h_r3 (F.converts_of_FB_converts h_equal_underscore) as r4
  step mkAdd.convertsM h_r4 (F.converts_of_FB_converts h_equal_eqsign) as r5
  step mkAdd.convertsM h_r5 (F.converts_of_FB_converts h_zero_padding) as r6
  clear h_r1 h_r2 h_r3 h_r4 h_r5 h_range_AZ'' h_range_az' h_range_09 h_equal_minus
    h_equal_underscore h_equal_eqsign h_zero_padding
  step mkF.convertsM as c1
  step mkSub.convertsM h_r6 h_c1 as diff
  simp only [true_implies]
  step eq0.convertsM h_diff as check
  · apply convertsM_pure
    · refine converts_of_converts h_sum_underscore ?_
      simp only [value, beq_iff_eq, ite_mul, one_mul, zero_mul]
    · simp only [result, beq_iff_eq, sub_eq_zero]
      exact id
  · simp only [result, beq_iff_eq, sub_eq_zero]
    exact id

private lemma char_toNat_ofNat_of_lt {n : ℕ} (h : n < 256) : (Char.ofNat n).toNat = n := by
  have hv : n.isValidChar := by unfold Nat.isValidChar; omega
  rw [Char.ofNat, dif_pos hv]
  simp [Char.ofNatAux, Char.toNat]

private lemma isUpper_iff_toNat {c : Char} :
    c.isUpper ↔ 'A'.toNat ≤ c.toNat ∧ c.toNat ≤ 'Z'.toNat := by
  simp [Char.isUpper, ge_iff_le, UInt32.le_iff_toNat_le, ← Char.toNat_val]

private lemma isLower_iff_toNat {c : Char} :
    c.isLower ↔ 'a'.toNat ≤ c.toNat ∧ c.toNat ≤ 'z'.toNat := by
  simp [Char.isLower, UInt32.le_iff_toNat_le, ← Char.toNat_val]

/-- The accepted set, read as characters, in the shape `base64UrlDecode` states. -/
lemma accepts_iff_char {n : ℕ} (h : n < 2 ^ 8) :
    accepts n ↔ Char.ofNat n ∈ [Char.ofNat 0, '-', '_', '='] ∨ (Char.ofNat n).isUpper ∨
      (Char.ofNat n).isLower ∨ (Char.ofNat n).isDigit := by
  have hc := char_toNat_ofNat_of_lt (show n < 256 by omega)
  have h0 := char_toNat_ofNat_of_lt (show 0 < 256 by omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false, ← Char.toNat_inj, hc, h0,
    isUpper_iff_toNat, isLower_iff_toNat, Char.isDigit_iff_toNat]
  rw [show '-'.toNat = 45 from rfl, show '_'.toNat = 95 from rfl, show '='.toNat = 61 from rfl,
    show 'A'.toNat = 65 from rfl, show 'Z'.toNat = 90 from rfl, show 'a'.toNat = 97 from rfl,
    show 'z'.toNat = 122 from rfl, show '0'.toNat = 48 from rfl, show '9'.toNat = 57 from rfl]
  unfold accepts
  omega

lemma convertsM_byte
  [p.AtLeastTwo]
  {state : ClapMState p}
  {m : F p}
  {m_val : ZMod p}
  (h_m : Converts F.conversion state m m_val)
  (h_p : 2 ^ 9 < p)
  (hv : m_val.val < 2 ^ 8)
:
  ConvertsM F.conversion (base64UrlLookup m) state (index m_val.val) (accepts m_val.val)
:= by
  apply convertsM_of_convertsM (convertsM h_m h_p)
  · exact value_of_lt h_p hv
  · exact Iff.rfl

/-- `convertsM` on a byte, read through `Char` -/
lemma convertsM_char
  [p.AtLeastTwo]
  {state : ClapMState p}
  {m : F p}
  {m_val : ZMod p}
  (h_m : Converts F.conversion state m m_val)
  (h_byte : m_val.val < 2^8)
  (h_p : 2^(8+1) < p)
:
  ConvertsM F.conversion (base64UrlLookup m) state
    (if (Char.ofNat m_val.val).isUpper then m_val - 65 else
      if (Char.ofNat m_val.val).isLower then m_val - 71 else
        if (Char.ofNat m_val.val).isDigit then m_val + 4 else
          if m_val.val == '-'.toNat then 62 else
            if m_val.val == '_'.toNat then 63 else 0
    )
    ( m_val.val ∈
      [0, '-'.toNat, '_'.toNat, '='.toNat] ++
      List.range' 'A'.toNat 26 ++
      List.range' 'a'.toNat 26 ++
      List.range' '0'.toNat 10
    )
:= by
  apply convertsM_of_convertsM (convertsM h_m h_p)
  · have hc := char_toNat_ofNat_of_lt (show m_val.val < 256 by omega)
    rw [value_of_lt h_p h_byte]
    simp only [isUpper_iff_toNat, isLower_iff_toNat, Char.isDigit_iff_toNat, hc, beq_iff_eq]
    rw [show '-'.toNat = 45 from rfl, show '_'.toNat = 95 from rfl, show 'A'.toNat = 65 from rfl,
      show 'Z'.toNat = 90 from rfl, show 'a'.toNat = 97 from rfl, show 'z'.toNat = 122 from rfl,
      show '0'.toNat = 48 from rfl, show '9'.toNat = 57 from rfl]
    have hv' := (ZMod.natCast_zmod_val m_val).symm
    generalize m_val.val = n at *
    subst hv'
    unfold index
    split_ifs <;> first
      | (rw [Nat.cast_sub (show 65 ≤ n by omega), Nat.cast_ofNat])
      | (rw [Nat.cast_sub (show 71 ≤ n by omega), Nat.cast_ofNat])
      | (push_cast; rfl)
  · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_range'_1]
    rw [show '-'.toNat = 45 from rfl, show '_'.toNat = 95 from rfl, show '='.toNat = 61 from rfl,
      show 'A'.toNat = 65 from rfl, show 'a'.toNat = 97 from rfl, show '0'.toNat = 48 from rfl]
    unfold accepts
    omega

end base64UrlLookup

section examples

/-! Evaluation-style smoke tests, run on every residue of `q = 521`, the smallest prime above
`2 ^ 9`. The `share`s read `num2bits` witnesses, so the circuit cannot be lowered through `toWg`
(docs/porting-guide.md §Traps). Instead the circuit's own semantics computes every variable, and
the `eq0` and `num2bits` gates are evaluated in that store, as in
`FString/assertIsConcatenation.lean`. -/

private abbrev q : ℕ := 521

/-- Whether every gate holds, and the output, for the input `v`. -/
private def run (v : ℕ) : Bool × Option (ZMod q) :=
  let cmd : ClapM q (HashConsSt q × ExprRef) := do
    let x ← liftM (HashConsM.mkConstant (p := q) (v : ZMod q))
    let z ← base64UrlLookup x
    let σ ← getThe (HashConsSt q)
    return (σ, z)
  let Γ := cmd.getVarStore {} 0 {}
  let r := (cmd.run 0 {}).1.1.1
  let holds := (cmd.getCircuit 0 {}).all fun g ↦ match g with
    | .eq0 e => [Γ, r.1|e] == some 0
    | .num2bits w e => ([Γ, r.1|e].map fun x ↦ decide (x.val < 2 ^ w)).getD false
    | _ => true
  (holds, [Γ, r.1|r.2])

-- The gates hold exactly on the 66 accepted values, over every field element.
example : (List.range q).all (fun v ↦ (run v).1 == decide (base64UrlLookup.accepts v)) = true := by
  native_decide

-- The output is `value`, for every field element.
example : (List.range q).all
    (fun v ↦ (run v).2 == some (base64UrlLookup.value (v : ZMod q))) = true := by
  native_decide

-- On every byte, the output is the base64url index: `TWFu` is `19, 22, 5, 46`.
example : (List.range 256).all
    (fun v ↦ (run v).2 == some (base64UrlLookup.index v : ZMod q)) = true := by
  native_decide
example : ['T', 'W', 'F', 'u'].map (fun c ↦ (run c.toNat).2) = [some 19, some 22, some 5, some 46] := by
  native_decide

end examples

end Clap.Lang.Base64
