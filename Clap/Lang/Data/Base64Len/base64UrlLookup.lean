import Clap.Lang.Gate.num2bits
import Clap.Lang.Core.FB.ofBool
import Clap.Lang.Core.F.mkAdd
import Clap.Lang.Core.F.mkSub
import Clap.Lang.Core.F.lessThan
import Clap.Lang.Core.FB.and
import Clap.Lang.Core.FB.eq
import Clap.Lang.Data.FBitVec.bits2numV

namespace Clap.Lang.Base64

variable {p : ℕ}

def base64UrlLookup [p.AtLeastTwo] (i : F p) : ClapM p (F p) := do
  -- check if i ∈ ['A', 'Z']
  let ge_A ← greaterEqThan 8 i (← mkF 'A'.toNat)
  let le_Z ← lessEqThan 8 i (← mkF 'Z'.toNat)
  let range_AZ ← ge_A.and le_Z
  let sixtyFive ← mkF 65
  let sum_AZ : F p ← mkMul (range_AZ : F p) (← mkSub i sixtyFive)

  -- check if i ∈ ['a', 'z']
  let ge_a ← greaterEqThan 8 i (← mkF 'a'.toNat)
  let le_z ← lessEqThan 8 i (← mkF 'z'.toNat)
  let range_az ← ge_a.and le_z
  let seventyOne ← mkF 71
  let diff ← mkSub i seventyOne
  let sum_az ← mkAdd sum_AZ (← mkMul (range_az : F p) diff)

  -- check if i ∈ ['0', '9']
  let ge_a ← greaterEqThan 8 i (← mkF '0'.toNat)
  let le_z ← lessEqThan 8 i (← mkF '9'.toNat)
  let range_09 ← ge_a.and le_z
  let four ← mkF 4
  let sum_09 ← mkAdd sum_az (← mkMul (range_09 : F p) (← mkAdd i four))

  -- check if i is '-'
  let eq_minus ← eq i (← mkF '-'.toNat)
  let sixtyTwo ← mkF 62
  let sum_minus ← mkAdd sum_09 (← mkMul (eq_minus : F p) sixtyTwo)

  -- check if i is '_'
  let eq_underscore ← eq i (← mkF '_'.toNat)
  let sixtyThree ← mkF 63
  let sum_underscore ← mkAdd sum_minus (← mkMul (eq_underscore : F p) sixtyThree)

  -- check if i is '='
  let eq_eqsign ← eq i (← mkF '='.toNat)

  -- check if i is zero
  let zero_padding ← isZero i

  -- exactly one case has to be true
  let sum ←
    [range_AZ, range_az, range_09, eq_minus, eq_underscore, eq_eqsign, zero_padding]
    |> List.foldrM mkAdd (←mkF 0)

  eq0 (← sum - (← mkF 1))
  pure sum_underscore

namespace base64UrlLookup

private lemma flagRangeAZ [p.AtLeastTwo] {state : ClapMState p} {m : F p} {m_val : ZMod p}
    (h_m : Converts F.conversion state m m_val) (h_byte : m_val.val < 2^8) (h_p : 2^(8+1) < p) :
  ConvertsM FB.conversion
    (do
      let ge_A ← greaterEqThan 8 m (← mkF 'A'.toNat)
      let le_Z ← lessEqThan 8 m (← mkF 'Z'.toNat)
      ge_A.and le_Z)
    state (decide (65 ≤ m_val.val) && decide (m_val.val ≤ 90)) True
:= by
  have hp512 : 512 < p := by simpa using h_p
  have eA : ('A'.toNat : ℕ) = 65 := rfl
  have eZ : ('Z'.toNat : ℕ) = 90 := rfl
  step mkF.convertsM as aConst
  rw [eA] at h_aConst
  step greaterEqThan.convertsM h_m h_aConst
    (ha := h_byte) (hb := by rw [ZMod.val_natCast_of_lt (by omega)]; norm_num) (hw := h_p)
    as ge_A
  step mkF.convertsM as zConst
  rw [eZ] at h_zConst
  step lessEqThan.convertsM h_m h_zConst
    (ha := h_byte) (hb := by rw [ZMod.val_natCast_of_lt (by omega)]; norm_num) (hw := h_p)
    as le_Z
  exact convertsM_of_convertsM (FB.and.convertsM h_ge_A h_le_Z)
    (by rw [ZMod.val_natCast_of_lt (show (65:ℕ) < p by omega),
            ZMod.val_natCast_of_lt (show (90:ℕ) < p by omega)])
    (by simp)

private lemma flagRangeAz [p.AtLeastTwo] {state : ClapMState p} {m : F p} {m_val : ZMod p}
    (h_m : Converts F.conversion state m m_val) (h_byte : m_val.val < 2^8) (h_p : 2^(8+1) < p) :
  ConvertsM FB.conversion
    (do
      let ge_a ← greaterEqThan 8 m (← mkF 'a'.toNat)
      let le_z ← lessEqThan 8 m (← mkF 'z'.toNat)
      ge_a.and le_z)
    state (decide (97 ≤ m_val.val) && decide (m_val.val ≤ 122)) True
:= by
  have hp512 : 512 < p := by simpa using h_p
  have ea : ('a'.toNat : ℕ) = 97 := rfl
  have ez : ('z'.toNat : ℕ) = 122 := rfl
  step mkF.convertsM as aConst
  rw [ea] at h_aConst
  step greaterEqThan.convertsM h_m h_aConst
    (ha := h_byte) (hb := by rw [ZMod.val_natCast_of_lt (by omega)]; norm_num) (hw := h_p)
    as ge_a
  step mkF.convertsM as zConst
  rw [ez] at h_zConst
  step lessEqThan.convertsM h_m h_zConst
    (ha := h_byte) (hb := by rw [ZMod.val_natCast_of_lt (by omega)]; norm_num) (hw := h_p)
    as le_z
  exact convertsM_of_convertsM (FB.and.convertsM h_ge_a h_le_z)
    (by rw [ZMod.val_natCast_of_lt (show (97:ℕ) < p by omega),
            ZMod.val_natCast_of_lt (show (122:ℕ) < p by omega)])
    (by simp)

private lemma flagRange09 [p.AtLeastTwo] {state : ClapMState p} {m : F p} {m_val : ZMod p}
    (h_m : Converts F.conversion state m m_val) (h_byte : m_val.val < 2^8) (h_p : 2^(8+1) < p) :
  ConvertsM FB.conversion
    (do
      let ge_0 ← greaterEqThan 8 m (← mkF '0'.toNat)
      let le_9 ← lessEqThan 8 m (← mkF '9'.toNat)
      ge_0.and le_9)
    state (decide (48 ≤ m_val.val) && decide (m_val.val ≤ 57)) True
:= by
  have hp512 : 512 < p := by simpa using h_p
  have e0 : ('0'.toNat : ℕ) = 48 := rfl
  have e9 : ('9'.toNat : ℕ) = 57 := rfl
  step mkF.convertsM as zeroConst
  rw [e0] at h_zeroConst
  step greaterEqThan.convertsM h_m h_zeroConst
    (ha := h_byte) (hb := by rw [ZMod.val_natCast_of_lt (by omega)]; norm_num) (hw := h_p)
    as ge_0
  step mkF.convertsM as nineConst
  rw [e9] at h_nineConst
  step lessEqThan.convertsM h_m h_nineConst
    (ha := h_byte) (hb := by rw [ZMod.val_natCast_of_lt (by omega)]; norm_num) (hw := h_p)
    as le_9
  exact convertsM_of_convertsM (FB.and.convertsM h_ge_0 h_le_9)
    (by rw [ZMod.val_natCast_of_lt (show (48:ℕ) < p by omega),
            ZMod.val_natCast_of_lt (show (57:ℕ) < p by omega)])
    (by simp)

private lemma flagEqChar [p.AtLeastTwo] {state : ClapMState p} {m : F p} {m_val : ZMod p}
    (h_m : Converts F.conversion state m m_val) (c : Char) :
  ConvertsM FB.conversion
    (do eq m (← mkF c.toNat))
    state (m_val == (c.toNat : ZMod p)) True
:= by
  step mkF.convertsM as cConst
  exact convertsM_of_convertsM (eq.convertsM h_m h_cConst) rfl (by simp)

private lemma foldSum [p.AtLeastTwo] {state : ClapMState p}
    {z0 : F p}
    {range_AZ range_az range_09 eq_minus eq_underscore eq_eqsign zero_padding : FB p}
    {range_AZ_val range_az_val range_09_val eq_minus_val eq_underscore_val eq_eqsign_val zero_padding_val : Bool}
    (h_z0 : Converts F.conversion state z0 (0 : ZMod p))
    (h_range_AZ : Converts FB.conversion state range_AZ range_AZ_val)
    (h_range_az : Converts FB.conversion state range_az range_az_val)
    (h_range_09 : Converts FB.conversion state range_09 range_09_val)
    (h_eq_minus : Converts FB.conversion state eq_minus eq_minus_val)
    (h_eq_underscore : Converts FB.conversion state eq_underscore eq_underscore_val)
    (h_eq_eqsign : Converts FB.conversion state eq_eqsign eq_eqsign_val)
    (h_zero_padding : Converts FB.conversion state zero_padding zero_padding_val) :
  ConvertsM F.conversion
    ([range_AZ, range_az, range_09, eq_minus, eq_underscore, eq_eqsign, zero_padding]
      |> List.foldrM mkAdd z0)
    state
    ((if range_AZ_val then (1:ZMod p) else 0) + (if range_az_val then 1 else 0)
      + (if range_09_val then 1 else 0) + (if eq_minus_val then 1 else 0)
      + (if eq_underscore_val then 1 else 0) + (if eq_eqsign_val then 1 else 0)
      + (if zero_padding_val then 1 else 0))
    True
:= by
  unfold List.foldrM
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    List.foldlM_cons, List.foldlM_nil]
  have h_zero_padding_f := F.converts_of_FB_converts h_zero_padding
  clear h_zero_padding
  step mkAdd.convertsM h_zero_padding_f h_z0 as s1
  clear h_zero_padding_f h_z0
  have h_eq_eqsign_f := F.converts_of_FB_converts h_eq_eqsign
  clear h_eq_eqsign
  step mkAdd.convertsM h_eq_eqsign_f h_s1 as s2
  clear h_eq_eqsign_f h_s1
  have h_eq_underscore_f := F.converts_of_FB_converts h_eq_underscore
  clear h_eq_underscore
  step mkAdd.convertsM h_eq_underscore_f h_s2 as s3
  clear h_eq_underscore_f h_s2
  have h_eq_minus_f := F.converts_of_FB_converts h_eq_minus
  clear h_eq_minus
  step mkAdd.convertsM h_eq_minus_f h_s3 as s4
  clear h_eq_minus_f h_s3
  have h_range_09_f := F.converts_of_FB_converts h_range_09
  clear h_range_09
  step mkAdd.convertsM h_range_09_f h_s4 as s5
  clear h_range_09_f h_s4
  have h_range_az_f := F.converts_of_FB_converts h_range_az
  clear h_range_az
  step mkAdd.convertsM h_range_az_f h_s5 as s6
  clear h_range_az_f h_s5
  have h_range_AZ_f := F.converts_of_FB_converts h_range_AZ
  clear h_range_AZ
  step mkAdd.convertsM h_range_AZ_f h_s6 as s7
  clear h_range_AZ_f h_s6
  apply convertsM_of_convertsM (convertsM_pure F.conversion h_s7 trivial)
  · ring
  · simp

private lemma finalAssert [p.AtLeastTwo] {state : ClapMState p}
    {range_AZ range_az range_09 eq_minus eq_underscore eq_eqsign zero_padding : FB p}
    {range_AZ_val range_az_val range_09_val eq_minus_val eq_underscore_val eq_eqsign_val zero_padding_val : Bool}
    (h_range_AZ : Converts FB.conversion state range_AZ range_AZ_val)
    (h_range_az : Converts FB.conversion state range_az range_az_val)
    (h_range_09 : Converts FB.conversion state range_09 range_09_val)
    (h_eq_minus : Converts FB.conversion state eq_minus eq_minus_val)
    (h_eq_underscore : Converts FB.conversion state eq_underscore eq_underscore_val)
    (h_eq_eqsign : Converts FB.conversion state eq_eqsign eq_eqsign_val)
    (h_zero_padding : Converts FB.conversion state zero_padding zero_padding_val)
    (hp512 : 512 < p) :
  ConvertsM FUnit.conversion
    (do
      let sum ←
        [range_AZ, range_az, range_09, eq_minus, eq_underscore, eq_eqsign, zero_padding]
        |> List.foldrM mkAdd (←mkF 0)
      eq0 (← sum - (← mkF 1)))
    state ()
    ( ((if range_AZ_val then 1 else 0) + (if range_az_val then 1 else 0) + (if range_09_val then 1 else 0)
      + (if eq_minus_val then 1 else 0) + (if eq_underscore_val then 1 else 0) + (if eq_eqsign_val then 1 else 0)
      + (if zero_padding_val then 1 else 0) : ℕ) = 1 )
:= by
  step mkF.convertsM as z0
  step foldSum h_z0 h_range_AZ h_range_az h_range_09 h_eq_minus h_eq_underscore h_eq_eqsign h_zero_padding as sum
  step mkF.convertsM as one
  step mkSub.convertsM h_sum h_one as diff
  haveI : Fact (1 < p) := ⟨by omega⟩
  apply convertsM_of_convertsM (eq0.convertsM h_diff)
  · rfl
  · simp only [true_implies]
    rw [sub_eq_zero]
    have hcast :
      (if range_AZ_val then (1:ZMod p) else 0) + (if range_az_val then 1 else 0)
        + (if range_09_val then 1 else 0) + (if eq_minus_val then 1 else 0)
        + (if eq_underscore_val then 1 else 0) + (if eq_eqsign_val then 1 else 0)
        + (if zero_padding_val then 1 else 0)
      = (((if range_AZ_val then 1 else 0) + (if range_az_val then 1 else 0)
        + (if range_09_val then 1 else 0) + (if eq_minus_val then 1 else 0)
        + (if eq_underscore_val then 1 else 0) + (if eq_eqsign_val then 1 else 0)
        + (if zero_padding_val then 1 else 0) : ℕ) : ZMod p) := by
      cases range_AZ_val <;> cases range_az_val <;> cases range_09_val <;> cases eq_minus_val <;>
        cases eq_underscore_val <;> cases eq_eqsign_val <;> cases zero_padding_val <;>
        push_cast <;> ring
    rw [hcast]
    constructor
    · intro h
      have h2 := congrArg ZMod.val h
      rwa [ZMod.val_natCast_of_lt (by
          cases range_AZ_val <;> cases range_az_val <;> cases range_09_val <;> cases eq_minus_val <;>
            cases eq_underscore_val <;> cases eq_eqsign_val <;> cases zero_padding_val <;> simp <;> omega),
        ZMod.val_one] at h2
    · intro h
      rw [h]
      simp

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

set_option maxHeartbeats 300000000 in
lemma convertsM [p.AtLeastTwo]
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
  have hp512 : 512 < p := by simpa using h_p
  have eA : ('A'.toNat : ℕ) = 65 := rfl
  have eZ : ('Z'.toNat : ℕ) = 90 := rfl
  have ea : ('a'.toNat : ℕ) = 97 := rfl
  have ez : ('z'.toNat : ℕ) = 122 := rfl
  have e0 : ('0'.toNat : ℕ) = 48 := rfl
  have e9 : ('9'.toNat : ℕ) = 57 := rfl
  have edash : ('-'.toNat : ℕ) = 45 := rfl
  have eus : ('_'.toNat : ℕ) = 95 := rfl
  have eeq : ('='.toNat : ℕ) = 61 := rfl
  unfold base64UrlLookup
  step mkF.convertsM as aConst
  rw [eA] at h_aConst
  step greaterEqThan.convertsM h_m h_aConst
    (ha := h_byte) (hb := by rw [ZMod.val_natCast_of_lt (by omega)]; norm_num) (hw := h_p)
    as ge_A
  -- Seal `ge_A`'s post-state/result opaque immediately: `greaterEqThan` goes through `num2bits`
  -- at the concrete width 9, and leaving these as transparent `set`-lets means every later
  -- `step`'s `whnf`/unification re-walks the width-deep `Vector.ofFnM` recursion through the
  -- whole accumulated chain. See `F8/isWhitespace.lean` for the same fix on a smaller example.
  generalize ge_A_result = ge_A_result' at *
  generalize ge_A_state = ge_A_state' at *
  clear h_aConst
  step mkF.convertsM as zConst
  rw [eZ] at h_zConst
  step lessEqThan.convertsM h_m h_zConst
    (ha := h_byte) (hb := by rw [ZMod.val_natCast_of_lt (by omega)]; norm_num) (hw := h_p)
    as le_Z
  generalize le_Z_result = le_Z_result' at *
  generalize le_Z_state = le_Z_state' at *
  clear h_zConst
  step FB.and.convertsM h_ge_A h_le_Z as range_AZ
  generalize range_AZ_result = range_AZ_result' at *
  generalize range_AZ_state = range_AZ_state' at *
  clear h_ge_A h_le_Z
  step mkF.convertsM as sixtyFive
  generalize sixtyFive_result = sixtyFive_result' at *
  generalize sixtyFive_state = sixtyFive_state' at *
  step mkSub.convertsM h_m h_sixtyFive as sub_AZ
  generalize sub_AZ_result = sub_AZ_result' at *
  generalize sub_AZ_state = sub_AZ_state' at *
  have h_range_AZ_f := F.converts_of_FB_converts h_range_AZ
  step mkMul.convertsM h_range_AZ_f h_sub_AZ as sum_AZ
  generalize sum_AZ_result = sum_AZ_result' at *
  generalize sum_AZ_state = sum_AZ_state' at *
  clear h_sixtyFive h_sub_AZ h_range_AZ_f

  step mkF.convertsM as lowercase_a
  generalize lowercase_a_result = lowercase_a_result' at *
  generalize lowercase_a_state = lowercase_a_state' at *
  rw [ea] at h_lowercase_a
  step greaterEqThan.convertsM h_m h_lowercase_a
    (ha := h_byte) (hb := by rw [ZMod.val_natCast_of_lt (by omega)]; norm_num) (hw := h_p)
    as ge_a
  generalize ge_a_result = ge_a_result' at *
  generalize ge_a_state = ge_a_state' at *
  clear h_lowercase_a
  step mkF.convertsM as lowercase_z
  generalize lowercase_z_result = lowercase_z_result' at *
  generalize lowercase_z_state = lowercase_z_state' at *
  rw [ez] at h_lowercase_z
  step lessEqThan.convertsM h_m h_lowercase_z
    (ha := h_byte) (hb := by rw [ZMod.val_natCast_of_lt (by omega)]; norm_num) (hw := h_p)
    as le_z
  generalize le_z_result = le_z_result' at *
  generalize le_z_state = le_z_state' at *
  clear h_lowercase_z
  step FB.and.convertsM h_ge_a h_le_z as range_az
  generalize range_az_result = range_az_result' at *
  generalize range_az_state = range_az_state' at *
  clear h_ge_a h_le_z
  step mkF.convertsM as seventyOne
  generalize seventyOne_result = seventyOne_result' at *
  generalize seventyOne_state = seventyOne_state' at *
  step mkSub.convertsM h_m h_seventyOne as diff
  generalize diff_result = diff_result' at *
  generalize diff_state = diff_state' at *
  clear h_seventyOne
  have h_range_az_f := F.converts_of_FB_converts h_range_az
  step mkMul.convertsM h_range_az_f h_diff as mul_az
  generalize mul_az_result = mul_az_result' at *
  generalize mul_az_state = mul_az_state' at *
  clear h_diff h_range_az_f
  step mkAdd.convertsM h_sum_AZ h_mul_az as sum_az
  generalize sum_az_result = sum_az_result' at *
  generalize sum_az_state = sum_az_state' at *
  clear h_sum_AZ h_mul_az
  step mkF.convertsM as zeroConst
  generalize zeroConst_result = zeroConst_result' at *
  generalize zeroConst_state = zeroConst_state' at *
  rw [e0] at h_zeroConst
  step greaterEqThan.convertsM h_m h_zeroConst
    (ha := h_byte) (hb := by rw [ZMod.val_natCast_of_lt (by omega)]; norm_num) (hw := h_p)
    as ge_0
  generalize ge_0_result = ge_0_result' at *
  generalize ge_0_state = ge_0_state' at *
  clear h_zeroConst
  step mkF.convertsM as nineConst
  generalize nineConst_result = nineConst_result' at *
  generalize nineConst_state = nineConst_state' at *
  rw [e9] at h_nineConst
  step lessEqThan.convertsM h_m h_nineConst
    (ha := h_byte) (hb := by rw [ZMod.val_natCast_of_lt (by omega)]; norm_num) (hw := h_p)
    as le_9
  generalize le_9_result = le_9_result' at *
  generalize le_9_state = le_9_state' at *
  clear h_nineConst
  step FB.and.convertsM h_ge_0 h_le_9 as range_09
  generalize range_09_result = range_09_result' at *
  generalize range_09_state = range_09_state' at *
  clear h_ge_0 h_le_9
  step mkF.convertsM as four
  generalize four_result = four_result' at *
  generalize four_state = four_state' at *
  step mkAdd.convertsM h_m h_four as iplus4
  generalize iplus4_result = iplus4_result' at *
  generalize iplus4_state = iplus4_state' at *
  clear h_four
  have h_range_09_f := F.converts_of_FB_converts h_range_09
  step mkMul.convertsM h_range_09_f h_iplus4 as mul_09
  generalize mul_09_result = mul_09_result' at *
  generalize mul_09_state = mul_09_state' at *
  clear h_iplus4 h_range_09_f
  step mkAdd.convertsM h_sum_az h_mul_09 as sum_09
  generalize sum_09_result = sum_09_result' at *
  generalize sum_09_state = sum_09_state' at *
  clear h_sum_az h_mul_09

  step mkF.convertsM as dashConst
  generalize dashConst_result = dashConst_result' at *
  generalize dashConst_state = dashConst_state' at *
  rw [edash] at h_dashConst
  step eq.convertsM h_m h_dashConst as eq_minus
  generalize eq_minus_result = eq_minus_result' at *
  generalize eq_minus_state = eq_minus_state' at *
  clear h_dashConst
  step mkF.convertsM as sixtyTwo
  generalize sixtyTwo_result = sixtyTwo_result' at *
  generalize sixtyTwo_state = sixtyTwo_state' at *
  have h_eq_minus_f := F.converts_of_FB_converts h_eq_minus
  step mkMul.convertsM h_eq_minus_f h_sixtyTwo as mul_minus
  generalize mul_minus_result = mul_minus_result' at *
  generalize mul_minus_state = mul_minus_state' at *
  step mkAdd.convertsM h_sum_09 h_mul_minus as sum_minus
  generalize sum_minus_result = sum_minus_result' at *
  generalize sum_minus_state = sum_minus_state' at *
  clear h_sixtyTwo h_mul_minus h_eq_minus_f h_sum_09

  step mkF.convertsM as usConst
  generalize usConst_result = usConst_result' at *
  generalize usConst_state = usConst_state' at *
  rw [eus] at h_usConst
  step eq.convertsM h_m h_usConst as eq_underscore
  generalize eq_underscore_result = eq_underscore_result' at *
  generalize eq_underscore_state = eq_underscore_state' at *
  clear h_usConst
  step mkF.convertsM as sixtyThree
  generalize sixtyThree_result = sixtyThree_result' at *
  generalize sixtyThree_state = sixtyThree_state' at *
  have h_eq_underscore_f := F.converts_of_FB_converts h_eq_underscore
  step mkMul.convertsM h_eq_underscore_f h_sixtyThree as mul_underscore
  generalize mul_underscore_result = mul_underscore_result' at *
  generalize mul_underscore_state = mul_underscore_state' at *
  step mkAdd.convertsM h_sum_minus h_mul_underscore as sum_underscore
  generalize sum_underscore_result = sum_underscore_result' at *
  generalize sum_underscore_state = sum_underscore_state' at *
  clear h_sixtyThree h_mul_underscore h_eq_underscore_f h_sum_minus

  step mkF.convertsM as eqConst
  generalize eqConst_result = eqConst_result' at *
  generalize eqConst_state = eqConst_state' at *
  rw [eeq] at h_eqConst
  step eq.convertsM h_m h_eqConst as eq_eqsign
  generalize eq_eqsign_result = eq_eqsign_result' at *
  generalize eq_eqsign_state = eq_eqsign_state' at *
  clear h_eqConst
  step isZero.convertsM h_m as zero_padding
  generalize zero_padding_result = zero_padding_result' at *
  generalize zero_padding_state = zero_padding_state' at *

  have h_final := finalAssert h_range_AZ h_range_az h_range_09 h_eq_minus h_eq_underscore
    h_eq_eqsign h_zero_padding hp512
  have h_sum_underscore' := converts_skip h_final h_sum_underscore

  have hIsUpper : (Char.ofNat m_val.val).isUpper ↔ 65 ≤ m_val.val ∧ m_val.val ≤ 90 := by
    rw [isUpper_iff_toNat, char_toNat_ofNat_of_lt (show m_val.val < 256 by omega), eA, eZ]
  have hIsLower : (Char.ofNat m_val.val).isLower ↔ 97 ≤ m_val.val ∧ m_val.val ≤ 122 := by
    rw [isLower_iff_toNat, char_toNat_ofNat_of_lt (show m_val.val < 256 by omega), ea, ez]
  have hIsDigit : (Char.ofNat m_val.val).isDigit ↔ 48 ≤ m_val.val ∧ m_val.val ≤ 57 := by
    rw [Char.isDigit_iff_toNat, char_toNat_ofNat_of_lt (show m_val.val < 256 by omega), e0, e9]

  apply convertsM_of_convertsM
    (convertsM_bind_and h_final (convertsM_pure F.conversion h_sum_underscore' trivial))
  · have hmulTest : ∀ (b : Bool) (X : ZMod p), (if b then (1:ZMod p) else 0) * X = if b then X else 0 :=
      fun b X => by cases b <;> simp
    simp only [hIsUpper, hIsLower, hIsDigit, edash, eus, beq_iff_eq,
      Bool.and_eq_true, decide_eq_true_eq, hmulTest]
    -- Manual 6-way split (not `split_ifs`): each branch settles via a handful of `omega`-derived
    -- negations from disjointness, then `simp` closes the arithmetic. Keeps the case count linear
    -- instead of the combinatorial blowup a blind `split_ifs` over 5 shared conditions can hit.
    by_cases h1 : 65 ≤ m_val.val ∧ m_val.val ≤ 90
    · have hn2 : ¬(97 ≤ m_val.val ∧ m_val.val ≤ 122) := by omega
      have hn3 : ¬(48 ≤ m_val.val ∧ m_val.val ≤ 57) := by omega
      have hn4 : m_val.val ≠ 45 := by omega
      have hn5 : m_val.val ≠ 95 := by omega
      simp [h1, hn2, hn3, hn4, hn5]
    · by_cases h2 : 97 ≤ m_val.val ∧ m_val.val ≤ 122
      · have hn3 : ¬(48 ≤ m_val.val ∧ m_val.val ≤ 57) := by omega
        have hn4 : m_val.val ≠ 45 := by omega
        have hn5 : m_val.val ≠ 95 := by omega
        simp [h1, h2, hn3, hn4, hn5]
      · by_cases h3 : 48 ≤ m_val.val ∧ m_val.val ≤ 57
        · have hn4 : m_val.val ≠ 45 := by omega
          have hn5 : m_val.val ≠ 95 := by omega
          simp [h1, h2, h3, hn4, hn5]
        · by_cases h4 : m_val.val = 45
          · have hn5 : m_val.val ≠ 95 := by omega
            simp [h1, h2, h3, h4, hn5]
          · by_cases h5 : m_val.val = 95
            · simp [h1, h2, h3, h4, h5]
            · simp [h1, h2, h3, h4, h5]
  · simp only [and_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
      List.mem_append, List.mem_cons, List.mem_range', List.not_mem_nil, or_false]
    omega

end base64UrlLookup

end Clap.Lang.Base64
