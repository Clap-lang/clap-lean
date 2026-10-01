import Clap.Lang.Core.Combinators.foldlM
import Clap.Lang.Core.F.lessThan
import Clap.Lang.Core.F.mkF
import Clap.Lang.Core.F.mkMul
import Clap.Lang.Core.FB.and
import Clap.Lang.Core.FB.not
import Clap.Lang.Core.FUnit.assert_range
import Clap.Lang.Data.FArray.arraySelector
import Clap.Lang.Gate.eq0
import Clap.Model.Convert.PaddedVector
import Clap.Model.ConstraintSystem.toCs
import Clap.Model.PublicInput
import Clap.Model.WitnessGenerator.toWg

namespace Clap.Lang.FString

variable {p : ℕ}

section assertIsAsciiDigits

/-- Circom's `is_ascii_digit`, `47 < x ∧ x < 58`, by two 8-bit comparisons. Like `lessThan`, it
does not range-check `x` -/
def assertIsAsciiDigits.isDigit [p.AtLeastTwo] (x : F p) : ClapM p (FB p) := do
  -- Circom: `GreaterThan(9)([in[i], 47])`, at 8 bits
  let gt ← greaterThan 8 x (← mkF 47)
  -- Circom: `LessThan(9)([in[i], 58])`, at 8 bits
  let lt ← lessThan 8 x (← mkF 58)
  -- Circom: `var is_ascii_digit = AND()(…, …);`
  FB.and gt lt

/-- One iteration of Circom's loop, for the slot `x = in[i]` and its selector bit `s = selector[i]`. -/
def assertIsAsciiDigits.slot [p.AtLeastTwo] (x s : F p) : ClapM p Unit := do
  -- Circom: `_ <== Num2Bits(9)(in[i]);`, at 8 bits
  assert_range 8 x
  let d ← assertIsAsciiDigits.isDigit x
  -- Circom: `(1 - is_ascii_digit) * selector[i] === 0;`
  let nd ← not d
  let prod ← nd * s
  eq0 prod

def assertIsAsciiDigits [p.AtLeastTwo] {w : ℕ} (inp : FString p w) : ClapM p Unit := do
  -- Circom: `signal selector[MAX_DIGITS] <== ArraySelector(MAX_DIGITS)(0, len);`
  let sel ← arraySelector w (← mkF 0) inp.len
  -- Circom: `for (var i = 0; i < MAX_DIGITS; i++) { … }`, one `slot` per `i`
  (inp.data.zip sel).foldlM (fun _ xs ↦ assertIsAsciiDigits.slot xs.1 xs.2) ()

namespace assertIsAsciiDigits

namespace isDigit

lemma convertsM_unchecked
  [p.AtLeastTwo]
  {state : ClapMState p}
  {x : F p}
  {x_val : ZMod p}
  (h_x : Converts F.conversion state x x_val)
:
  ConvertsM FB.conversion (isDigit x) state
    (lessThan.lessThanRaw 8 47 x_val && lessThan.lessThanRaw 8 x_val 58)
    (lessThan.lessThanOk 8 47 x_val ∧ lessThan.lessThanOk 8 x_val 58)
:= by
  unfold isDigit greaterThan
  step mkF.convertsM as c47
  simp only [true_implies]
  -- Both comparisons assert, so the first is sequenced with `convertsM_bind_and`.
  have h_gt := lessThan.convertsM_unchecked (w := 8) h_c47 h_x
  have h_x' := converts_skip h_gt h_x
  have h_gtr := h_gt.result
  clear h_x h_c47
  apply convertsM_bind_and h_gt
  clear h_gt
  generalize (lessThan 8 c47_result x).getResult c47_state.numAlloc c47_state.σ = gt_result at *
  generalize (lessThan 8 c47_result x).getState c47_state = gt_state at *
  step mkF.convertsM as c58
  simp only [true_implies]
  step lessThan.convertsM_unchecked h_x' h_c58 as lt
  apply convertsM_of_convertsM (FB.and.convertsM h_gtr h_lt)
  · rfl
  · exact iff_of_true trivial (fun h ↦ h)

/-- For a byte `x`, the two comparisons are the real ones and cannot fail. -/
lemma convertsM
  [p.AtLeastTwo]
  {state : ClapMState p}
  {x : F p}
  {x_val : ZMod p}
  (h_x : Converts F.conversion state x x_val)
  (hx : x_val.val < 2 ^ 8)
  (hp : 2 ^ 9 < p)
:
  ConvertsM FB.conversion (isDigit x) state (decide (48 ≤ x_val.val ∧ x_val.val ≤ 57)) True
:= by
  have h9 : 2 ^ (8 + 1) < p := by simpa using hp
  have h47 : ((47 : ℕ) : ZMod p).val < 2 ^ 8 := by
    rw [ZMod.val_natCast_of_lt (by omega)]; norm_num
  have h58 : ((58 : ℕ) : ZMod p).val < 2 ^ 8 := by
    rw [ZMod.val_natCast_of_lt (by omega)]; norm_num
  have e47 : (47 : ZMod p) = ((47 : ℕ) : ZMod p) := by norm_cast
  have e58 : (58 : ZMod p) = ((58 : ℕ) : ZMod p) := by norm_cast
  apply convertsM_of_convertsM (convertsM_unchecked h_x)
  · rw [e47, e58, lessThan.lessThanRaw_eq h47 hx h9, lessThan.lessThanRaw_eq hx h58 h9,
      ZMod.val_natCast_of_lt (show 47 < p by omega), ZMod.val_natCast_of_lt (show 58 < p by omega)]
    by_cases h1 : 48 ≤ x_val.val <;> by_cases h2 : x_val.val ≤ 57 <;> simp [h1, h2] <;> omega
  · rw [e47, e58]
    exact iff_true_intro ⟨lessThan.lessThanOk_of h47 hx h9, lessThan.lessThanOk_of hx h58 h9⟩

end isDigit

namespace slot

lemma convertsM
  [p.AtLeastTwo]
  {state : ClapMState p}
  {x s : F p}
  {x_val s_val : ZMod p}
  (h_x : Converts F.conversion state x x_val)
  (h_s : Converts F.conversion state s s_val)
  (hp : 2 ^ 9 < p)
:
  ConvertsM FUnit.conversion (slot x s) state ()
    (x_val.val < 2 ^ 8 ∧ (s_val = 0 ∨ (47 < x_val.val ∧ x_val.val < 58)))
:= by
  unfold slot
  have hA := assert_range.convertsM (w := 8) h_x
  have h_x1 := converts_skip hA h_x
  have h_s1 := converts_skip hA h_s
  -- The rest asserts twice: the comparisons' offsets, then the `eq0`.
  have hRest : ConvertsM FUnit.conversion
      (do
        let d ← isDigit x
        let nd ← not d
        let prod ← nd * s
        eq0 prod)
      ((assert_range 8 x).getState state) ()
      ((lessThan.lessThanOk 8 47 x_val ∧ lessThan.lessThanOk 8 x_val 58) ∧
        (lessThan.lessThanRaw 8 47 x_val && lessThan.lessThanRaw 8 x_val 58 ∨ s_val = 0)) := by
    have hD := isDigit.convertsM_unchecked h_x1
    have h_s2 := converts_skip hD h_s1
    have h_dr := hD.result
    clear h_x h_s h_x1 h_s1 hA
    apply convertsM_of_convertsM (convertsM_bind_and hD ?_) rfl Iff.rfl
    clear hD
    generalize (isDigit x).getResult ((assert_range 8 x).getState state).numAlloc
      ((assert_range 8 x).getState state).σ = d_result at *
    generalize (isDigit x).getState ((assert_range 8 x).getState state) = d_state at *
    step not.convertsM h_dr as nd
    step mkMul.convertsM (F.converts_of_FB_converts h_nd) h_s2 as prod
    apply convertsM_of_convertsM (eq0.convertsM h_prod)
    · rfl
    · simp only [true_implies, Bool.not_eq_eq_eq_not, Bool.not_true]
      cases (lessThan.lessThanRaw 8 47 x_val && lessThan.lessThanRaw 8 x_val 58) <;> simp
  refine convertsM_of_convertsM (convertsM_bind_guard hA hRest ?_) rfl Iff.rfl
  -- Under the range check, the comparisons are the real ones and their offsets fit.
  intro hx
  have h9 : 2 ^ (8 + 1) < p := by simpa using hp
  have h47 : ((47 : ℕ) : ZMod p).val < 2 ^ 8 := by
    rw [ZMod.val_natCast_of_lt (by omega)]; norm_num
  have h58 : ((58 : ℕ) : ZMod p).val < 2 ^ 8 := by
    rw [ZMod.val_natCast_of_lt (by omega)]; norm_num
  have e47 : (47 : ZMod p) = ((47 : ℕ) : ZMod p) := by norm_cast
  have e58 : (58 : ZMod p) = ((58 : ℕ) : ZMod p) := by norm_cast
  rw [e47, e58, lessThan.lessThanRaw_eq h47 hx h9, lessThan.lessThanRaw_eq hx h58 h9,
    ZMod.val_natCast_of_lt (show 47 < p by omega), ZMod.val_natCast_of_lt (show 58 < p by omega)]
  simp only [lessThan.lessThanOk_of h47 hx h9, lessThan.lessThanOk_of hx h58 h9, and_self,
    true_and, Bool.and_eq_true, decide_eq_true_eq]
  exact or_comm

end slot

/-- The per-position checks, over any data and selector vectors. Stated on its own, at an
abstract state, so that the fold is not elaborated against `arraySelector`'s concrete post-state
(a `whnf` timeout). -/
lemma fold_convertsM
  [p.AtLeastTwo]
  {w : ℕ}
  {state : ClapMState p}
  {data sel : FVec p w}
  {data_vals sel_vals : Vector (ZMod p) w}
  (h_data : Converts FVec.conversion state data data_vals)
  (h_sel : Converts FVec.conversion state sel sel_vals)
  (hp : 2 ^ 9 < p)
:
  ConvertsM FUnit.conversion ((data.zip sel).foldlM (fun _ xs ↦ slot xs.1 xs.2) ()) state ()
    (∀ i : Fin w, data_vals[i].val < 2 ^ 8 ∧
      (sel_vals[i] = 0 ∨ (47 < data_vals[i].val ∧ data_vals[i].val < 58)))
:= by
  apply convertsM_of_convertsM
    (convertsM_foldlM_constraints (C_acc := FUnit.conversion) (init_val := ())
      (f_spec := fun _ _ ↦ ())
      (step_constraints := fun xy : ZMod p × ZMod p ↦
        xy.1.val < 2 ^ 8 ∧ (xy.2 = 0 ∨ (47 < xy.1.val ∧ xy.1.val < 58)))
      (fun i ↦ FVec.converts_zip h_data h_sel i.isLt) FUnit.converts
      (fun _ h_xy ↦ slot.convertsM (FPair.converts_fst h_xy) (FPair.converts_snd h_xy) hp))
  · rfl
  · simp

/-- The selector followed by the per-position checks, over an abstract selector action. With the
action abstract, sequencing the two assertions cannot unfold `arraySelector` (a `whnf` timeout). -/
lemma bind_fold_convertsM
  [p.AtLeastTwo]
  {w : ℕ}
  {state : ClapMState p}
  {action : ClapM p (FArray p w)}
  {data : FVec p w}
  {data_vals : Vector (ZMod p) w}
  {sel_vals : Vector Bool w}
  {C_sel : Prop}
  (h_action : ConvertsM FArray.conversion action state sel_vals C_sel)
  (h_data : Converts FVec.conversion state data data_vals)
  (hp : 2 ^ 9 < p)
:
  ConvertsM FUnit.conversion
    (action >>= fun sel ↦ (data.zip sel).foldlM (fun _ xs ↦ slot xs.1 xs.2) ()) state ()
    (C_sel ∧ ∀ i : Fin w, data_vals[i].val < 2 ^ 8 ∧
      ((if sel_vals[i] then (1 : ZMod p) else 0) = 0 ∨
        (47 < data_vals[i].val ∧ data_vals[i].val < 58)))
:= by
  apply convertsM_of_convertsM (convertsM_bind_and h_action
    (fold_convertsM (converts_skip h_action h_data)
      (FVec.converts_of_FArray_converts h_action.result) hp))
  · rfl
  · simp

lemma convertsM
  [p.AtLeastTwo]
  {w : ℕ}
  {state : ClapMState p}
  {inp : FString p w}
  {data_vals : Vector (ZMod p) w}
  {len_val : ZMod p}
  (h_data : Converts FVec.conversion state inp.data data_vals)
  (h_len : Converts F.conversion state inp.len len_val)
  (h_w : w < p)
  (hw : 2 ^ (minBits' w + 1) < p)
  (hp : 2 ^ 9 < p)
:
  ConvertsM FUnit.conversion (assertIsAsciiDigits inp) state ()
    ((∀ i : Fin w, i.val < len_val.val → 48 ≤ data_vals[i].val ∧ data_vals[i].val ≤ 57) ∧
      0 < len_val.val ∧ len_val.val < 2 ^ minBits' w ∧ 0 < w ∧
      ∀ i : Fin w, data_vals[i].val < 2 ^ 8)
:= by
  unfold assertIsAsciiDigits
  step mkF.convertsM as z
  apply convertsM_of_convertsM
    (bind_fold_convertsM (arraySelector.convertsM h_z h_len h_w hw) h_data hp)
  · rfl
  · simp only [true_implies, ZMod.val_zero, Nat.zero_le, decide_true, Bool.true_xor,
      Fin.getElem_fin, Vector.getElem_ofFn,
      Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, not_le]
    have h10 : (1 : ZMod p) ≠ 0 := one_ne_zero
    constructor
    · rintro ⟨⟨-, h_lenb, h_w0, h_len0⟩, h_all⟩
      refine ⟨fun i hi ↦ ?_, h_len0, h_lenb, h_w0, fun i ↦ (h_all i).1⟩
      rcases (h_all i).2 with h | h
      · simp [hi, h10] at h
      · omega
    · rintro ⟨h_digits, h_len0, h_lenb, h_w0, h_bytes⟩
      refine ⟨⟨by positivity, h_lenb, h_w0, h_len0⟩, fun i ↦ ⟨h_bytes i, ?_⟩⟩
      by_cases hi : i.val < len_val.val
      · right
        have := h_digits i hi
        omega
      · left
        simp [hi]

/-- `convertsM` for the encoding of a string `s` (as `FString.conversion` gives) of at most `w`
characters, each below 256. The circuit accepts exactly the non-empty strings of decimal digits.
An encoding is bytes throughout, and its length is in `[0, w]`, so every other conjunct of
`convertsM` holds automatically. -/
lemma convertsM_string
  [p.AtLeastTwo]
  {w : ℕ}
  {state : ClapMState p}
  {inp : FString p w}
  {s : String}
  (h_inp : Converts FString.conversion state inp s)
  (h_s_len : s.length ≤ w)
  (h_chars : ∀ c ∈ s.toList, c.toNat < 256)
  (h_w : w < p)
  (hw : 2 ^ (minBits' w + 1) < p)
  (hp : 2 ^ 9 < p)
:
  ConvertsM FUnit.conversion (assertIsAsciiDigits inp) state ()
    (0 < s.length ∧ ∀ c ∈ s.toList, 48 ≤ c.toNat ∧ c.toNat ≤ 57)
:= by
  apply convertsM_of_convertsM
    (convertsM (FString.converts_data h_inp) (FString.converts_len h_inp) h_w hw hp)
  · rfl
  · have h_list : s.toList.length = s.length := by simp [String.length_toList]
    rw [ZMod.val_natCast_of_lt (show s.length < p by omega)]
    -- The `i`-th slot, for `i < s.length`, is the `i`-th character.
    have h_at : ∀ (i : ℕ) (hi_w : i < w) (hi : i < s.toList.length),
        ((encodeV (p := p) w s)[i]'hi_w).val = (s.toList[i]'hi).toNat := by
      intro i hi_w hi
      have hc := h_chars _ (List.getElem_mem hi)
      rw [encodeV_getElem_of_lt hi_w hi, toUInt8_toNat_of_lt hc,
        ZMod.val_natCast_of_lt (by omega)]
    constructor
    · rintro ⟨h_digits, h_len0, -, -, -⟩
      refine ⟨h_len0, fun c hc ↦ ?_⟩
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
      have h := h_digits ⟨i, by omega⟩ (show i < s.length by omega)
      simp only [Fin.getElem_fin] at h
      rwa [h_at i (by omega) hi] at h
    · rintro ⟨h_len0, h_digits⟩
      refine ⟨fun i hi ↦ ?_, h_len0, lt_of_le_of_lt h_s_len (lt_two_pow_minBits' w), by omega,
        fun i ↦ lt_of_lt_of_le (encodeV_val_lt i.isLt) (by norm_num)⟩
      simp only [Fin.getElem_fin]
      rw [h_at i.val i.isLt (by omega)]
      exact h_digits _ (List.getElem_mem _)

end assertIsAsciiDigits

end assertIsAsciiDigits

section examples

private abbrev q : ℕ := 521

local instance instFactPrimeAsciiDigitsQ : Fact (Nat.Prime q) := ⟨by norm_num⟩

private def digitsOk {n} (d : Vector (ZMod q) n) (len : ZMod q) : Bool :=
  let c : ClapM q Unit := do
    let data ← d.mapM mkF
    let l ← mkF len
    assertIsAsciiDigits ⟨data, l⟩
  let circ  := c.getCircuit 0 (HashConsSt.empty q)
  let cache := c.getHashConsState 0 (HashConsSt.empty q)
  (circ.toCs cache 0).run ((circ.toWg cache 0).run #v[])

example : digitsOk #v[48, 57, 0] 2 = true := by native_decide
example : digitsOk #v[48, 49, 50] 3 = true := by native_decide
-- a non-digit past `len` is fine, as long as it is a byte
example : digitsOk #v[48, 49, 100] 2 = true := by native_decide
example : digitsOk #v[47, 48, 0] 2 = false := by native_decide   -- '/' = 47 below '0'
example : digitsOk #v[48, 58, 0] 2 = false := by native_decide   -- ':' = 58 above '9'
-- every slot, padding included, is range-checked to 8 bits
example : digitsOk #v[48, 49, 255] 2 = true := by native_decide
example : digitsOk #v[48, 49, 300] 2 = false := by native_decide  -- Circom's 9 bits accept it
-- `ArraySelector(0, len)` needs `0 < len`
example : digitsOk #v[48, 49, 50] 0 = false := by native_decide

/-- `assertIsAsciiDigits` at width `w`, lowered once over input wires. -/
private def acceptsOn (w : ℕ) : Vector (ZMod q) (w + 1) → Bool :=
  let (inp, σ) := (mkInputFString (p := q) 0 w).run (HashConsSt.empty q)
  let c := assertIsAsciiDigits inp.1
  let circ := c.getCircuit (w + 1) σ
  let σ' := c.getHashConsState (w + 1) σ
  let cs := circ.toCs σ' (w + 1)
  let wg := circ.toWg σ' (w + 1)
  fun inputs ↦ cs.run (wg.run inputs)

private def accepts1 := acceptsOn 1
private def accepts2 := acceptsOn 2
private def accepts3 := acceptsOn 3
private def accepts5 := acceptsOn 5

/-- `convertsM`'s constraint, executable, on the canonical values. -/
private def specOk {w} (d : Vector ℕ w) (len : ℕ) : Bool :=
  (List.finRange w).all (fun i ↦ decide (i.val < len → 48 ≤ d[i] ∧ d[i] ≤ 57)) &&
    decide (0 < len) && decide (len < 2 ^ minBits' w) && decide (0 < w) &&
    (List.finRange w).all (fun i ↦ decide (d[i] < 2 ^ 8))

-- A selected slot: exactly the ten digits, among all `q` field elements.
example : (List.range q).all (fun x ↦
    accepts1 #v[x, 1] == decide (48 ≤ x ∧ x ≤ 57)) = true := by native_decide
-- A padding slot: exactly the bytes.
example : (List.range q).all (fun x ↦
    accepts2 #v[48, x, 1] == decide (x < 256)) = true := by native_decide
-- Five digits, every `len`: `0` is rejected, `[6, 7]` saturates, `8 = 2 ^ minBits' 5` is out.
example : (List.range q).all (fun l ↦
    accepts5 #v[48, 49, 50, 51, 52, l] == decide (1 ≤ l ∧ l ≤ 7)) = true := by native_decide
-- "0A1", every `len`: the `'A'` counts only once it is below `len`.
example : (List.range q).all (fun l ↦
    accepts3 #v[48, 65, 49, l] == decide (l = 1)) = true := by native_decide
-- The boundary values in both slots, against `convertsM`'s constraint.
example :
    let vals : List ℕ := [0, 47, 48, 57, 58, 255, 256, 511, 520]
    vals.all (fun a ↦ vals.all (fun b ↦ ([0, 1, 2, 3, 4, 520] : List ℕ).all (fun l ↦
      accepts2 #v[(a : ZMod q), b, l] == specOk #v[a, b] l))) = true := by native_decide

end examples

end Clap.Lang.FString
