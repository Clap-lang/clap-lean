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
import Clap.Model.WitnessGenerator.toWg

namespace Clap.Lang.FString

variable {p : ℕ}

section assertIsAsciiDigits

/-- `47 < x ∧ x < 58` by two 9-bit comparisons, the inner test of Circom's `AssertIsAsciiDigits`.
Like `lessThan` it does not range-check `x` -/
def assertIsAsciiDigits.isDigit [p.AtLeastTwo] (x : F p) : ClapM p (FB p) := do
  let c47 ← mkF 47
  let c58 ← mkF 58
  let gt ← greaterThan 9 x c47
  let lt ← lessThan 9 x c58
  FB.and gt lt

/-- One position of Circom's `AssertIsAsciiDigits`: `Num2Bits(9)(in[i])`, then
`(1 - is_ascii_digit) * selector[i] === 0`. -/
def assertIsAsciiDigits.slot [p.AtLeastTwo] (x s : F p) : ClapM p Unit := do
  assert_range 9 x
  let d ← assertIsAsciiDigits.isDigit x
  let nd ← not d
  let prod ← nd * s
  eq0 prod

/-- Every value of `inp.data` below `inp.len` is an ASCII digit, in `[48, 57]`. Circom's
`AssertIsAsciiDigits`.

As there, every position, padding included, is range-checked to 9 bits, and
`ArraySelector(0, len)` forces `0 < len` with `len` in `minBits' w` bits. -/
def assertIsAsciiDigits [p.AtLeastTwo] {w : ℕ} (inp : FString p w) : ClapM p Unit := do
  let z ← mkF 0
  let sel ← arraySelector w z inp.len
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
    (lessThan.lessThanRaw 9 47 x_val && lessThan.lessThanRaw 9 x_val 58)
    (lessThan.lessThanOk 9 47 x_val ∧ lessThan.lessThanOk 9 x_val 58)
:= by
  unfold isDigit greaterThan
  step mkF.convertsM as c47
  step mkF.convertsM as c58
  simp only [true_implies]
  -- Both comparisons assert, so the first is sequenced with `convertsM_bind_and`.
  have h_gt := lessThan.convertsM_unchecked (w := 9) h_c47 h_x
  have h_x' := converts_skip h_gt h_x
  have h_c58' := converts_skip h_gt h_c58
  have h_gtr := h_gt.result
  clear h_x h_c47 h_c58
  apply convertsM_bind_and h_gt
  clear h_gt
  generalize (lessThan 9 c47_result x).getResult c58_state.numAlloc c58_state.σ = gt_result at *
  generalize (lessThan 9 c47_result x).getState c58_state = gt_state at *
  step lessThan.convertsM_unchecked h_x' h_c58' as lt
  apply convertsM_of_convertsM (FB.and.convertsM h_gtr h_lt)
  · rfl
  · exact iff_of_true trivial (fun h ↦ h)

end isDigit

namespace slot

private lemma val_const {c : ℕ} (hc : c < p) : ((c : ℕ) : ZMod p).val = c :=
  ZMod.val_natCast_of_lt hc

lemma convertsM
  [p.AtLeastTwo]
  {state : ClapMState p}
  {x s : F p}
  {x_val s_val : ZMod p}
  (h_x : Converts F.conversion state x x_val)
  (h_s : Converts F.conversion state s s_val)
  (hp : 2 ^ 10 < p)
:
  ConvertsM FUnit.conversion (slot x s) state ()
    (x_val.val < 2 ^ 9 ∧ (s_val = 0 ∨ (47 < x_val.val ∧ x_val.val < 58)))
:= by
  unfold slot
  have hA := assert_range.convertsM (w := 9) h_x
  have h_x1 := converts_skip hA h_x
  have h_s1 := converts_skip hA h_s
  -- The rest asserts twice: the comparisons' offsets, then the `eq0`.
  have hRest : ConvertsM FUnit.conversion
      (do
        let d ← isDigit x
        let nd ← not d
        let prod ← nd * s
        eq0 prod)
      ((assert_range 9 x).getState state) ()
      ((lessThan.lessThanOk 9 47 x_val ∧ lessThan.lessThanOk 9 x_val 58) ∧
        (lessThan.lessThanRaw 9 47 x_val && lessThan.lessThanRaw 9 x_val 58 ∨ s_val = 0)) := by
    have hD := isDigit.convertsM_unchecked h_x1
    have h_s2 := converts_skip hD h_s1
    have h_dr := hD.result
    clear h_x h_s h_x1 h_s1 hA
    apply convertsM_of_convertsM (convertsM_bind_and hD ?_) rfl Iff.rfl
    clear hD
    generalize (isDigit x).getResult ((assert_range 9 x).getState state).numAlloc
      ((assert_range 9 x).getState state).σ = d_result at *
    generalize (isDigit x).getState ((assert_range 9 x).getState state) = d_state at *
    step not.convertsM h_dr as nd
    step mkMul.convertsM (F.converts_of_FB_converts h_nd) h_s2 as prod
    apply convertsM_of_convertsM (eq0.convertsM h_prod)
    · rfl
    · simp only [true_implies, Bool.not_eq_eq_eq_not, Bool.not_true]
      cases (lessThan.lessThanRaw 9 47 x_val && lessThan.lessThanRaw 9 x_val 58) <;> simp
  refine convertsM_of_convertsM (convertsM_bind_guard hA hRest ?_) rfl Iff.rfl
  -- Under the range check, the comparisons are the real ones and their offsets fit.
  intro hx
  have h9 : 2 ^ (9 + 1) < p := by simpa using hp
  have h47 : ((47 : ℕ) : ZMod p).val < 2 ^ 9 := by rw [val_const (by omega)]; norm_num
  have h58 : ((58 : ℕ) : ZMod p).val < 2 ^ 9 := by rw [val_const (by omega)]; norm_num
  have e47 : (47 : ZMod p) = ((47 : ℕ) : ZMod p) := by norm_cast
  have e58 : (58 : ZMod p) = ((58 : ℕ) : ZMod p) := by norm_cast
  rw [e47, e58, lessThan.lessThanRaw_eq h47 hx h9, lessThan.lessThanRaw_eq hx h58 h9,
    val_const (show 47 < p by omega), val_const (show 58 < p by omega)]
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
  (hp : 2 ^ 10 < p)
:
  ConvertsM FUnit.conversion ((data.zip sel).foldlM (fun _ xs ↦ slot xs.1 xs.2) ()) state ()
    (∀ i : Fin w, data_vals[i].val < 2 ^ 9 ∧
      (sel_vals[i] = 0 ∨ (47 < data_vals[i].val ∧ data_vals[i].val < 58)))
:= by
  apply convertsM_of_convertsM
    (convertsM_foldlM_constraints (C_acc := FUnit.conversion) (init_val := ())
      (f_spec := fun _ _ ↦ ())
      (step_constraints := fun xy : ZMod p × ZMod p ↦
        xy.1.val < 2 ^ 9 ∧ (xy.2 = 0 ∨ (47 < xy.1.val ∧ xy.1.val < 58)))
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
  (hp : 2 ^ 10 < p)
:
  ConvertsM FUnit.conversion
    (action >>= fun sel ↦ (data.zip sel).foldlM (fun _ xs ↦ slot xs.1 xs.2) ()) state ()
    (C_sel ∧ ∀ i : Fin w, data_vals[i].val < 2 ^ 9 ∧
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
  (hp : 2 ^ 10 < p)
:
  ConvertsM FUnit.conversion (assertIsAsciiDigits inp) state ()
    ((∀ i : Fin w, data_vals[i].val < 2 ^ 9) ∧ 0 < w ∧ 0 < len_val.val ∧
      len_val.val < 2 ^ minBits' w ∧
      ∀ i : Fin w, i.val < len_val.val → 48 ≤ data_vals[i].val ∧ data_vals[i].val ≤ 57)
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
      refine ⟨fun i ↦ (h_all i).1, h_w0, h_len0, h_lenb, fun i hi ↦ ?_⟩
      rcases (h_all i).2 with h | h
      · simp [hi, h10] at h
      · omega
    · rintro ⟨h_bytes, h_w0, h_len0, h_lenb, h_digits⟩
      refine ⟨⟨by positivity, h_lenb, h_w0, h_len0⟩, fun i ↦ ⟨h_bytes i, ?_⟩⟩
      by_cases hi : i.val < len_val.val
      · right
        have := h_digits i hi
        omega
      · left
        simp [hi]

end assertIsAsciiDigits

end assertIsAsciiDigits

section examples

private abbrev q : ℕ := 1031

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
-- a non-digit past `len` is fine, as long as it fits in 9 bits
example : digitsOk #v[48, 49, 100] 2 = true := by native_decide
example : digitsOk #v[47, 48, 0] 2 = false := by native_decide   -- '/' = 47 below '0'
example : digitsOk #v[48, 58, 0] 2 = false := by native_decide   -- ':' = 58 above '9'
-- Circom range-checks the padding too
example : digitsOk #v[48, 49, 600] 2 = false := by native_decide
-- `ArraySelector(0, len)` needs `0 < len`
example : digitsOk #v[48, 49, 50] 0 = false := by native_decide

end examples

end Clap.Lang.FString
