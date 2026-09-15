import Clap.eDSLState.Convert.Specialised
import Clap.Lang.F.mkAdd
import Clap.Lang.F.mkF
import Clap.Lang.F.mkSub
import Clap.Lang.FArray.num2bits
import Clap.Lang.FB.not

namespace Clap.Lang

variable {p : ℕ}

/-- `a < b` for `a, b` known to lie in `[0, 2^w)`. Only satisfiable (constraint-wise it always
holds, but the *result* is only the correct boolean) when `w + 1 < p`, so that
`a - b + 2^w` cannot wrap around the field. -/
def lessThan (w : ℕ) (a b : F p) : ClapM p (FB p) := do
  let diff ← a - b
  let pow ← mkF ((2 : ZMod p) ^ w)
  let d ← diff + pow
  let d ← num2bits (w + 1) d
  not d[w]

def lessEqThan (w : ℕ) (a b : F p) : ClapM p (FB p) :=
  lessThan w a (b + 1)

def greaterThan (w : ℕ) (a b : F p) : ClapM p (FB p) :=
  lessThan w b a

def greaterEqThan (w : ℕ) (a b : F p) : ClapM p (FB p) :=
  lessThan w b (a + 1)

namespace lessThan

/-- The "offset trick": for `a, b ∈ [0, 2^w)` and `2^(w+1) < p`, `a - b + 2^w` never wraps the
field, and equals `a.val + 2^w - b.val` computed in `ℕ`. -/
private lemma diff_val_eq
    [NeZero p] {w : ℕ} {a_val b_val : ZMod p}
    (ha : a_val.val < 2^w) (hb : b_val.val < 2^w) (hw : 2^(w+1) < p) :
    (a_val - b_val + (2:ZMod p)^w).val = a_val.val + 2^w - b_val.val := by
  have h2w_lt_p : 2^w < p := lt_trans (by omega) hw
  have h2w_val : ((2:ZMod p)^w).val = 2^w := by
    have h : ((2:ZMod p)^w) = ((2^w : ℕ) : ZMod p) := by push_cast; ring
    rw [h]; exact ZMod.val_natCast_of_lt h2w_lt_p
  have h_a_plus_2w : (a_val + (2:ZMod p)^w).val = a_val.val + 2^w := by
    have h := ZMod.val_add_of_lt (a := a_val) (b := (2:ZMod p)^w) (by rw [h2w_val]; omega)
    rwa [h2w_val] at h
  have heq : a_val - b_val + (2:ZMod p)^w = a_val + (2:ZMod p)^w - b_val := by ring
  rw [heq, ZMod.val_sub (by rw [h_a_plus_2w]; omega), h_a_plus_2w]

/-- The MSB (index `w` of the `w+1`-bit decomposition) is `1` iff `a ≥ b`. -/
private lemma diff_val_div_eq
    [NeZero p] {w : ℕ} {a_val b_val : ZMod p}
    (ha : a_val.val < 2^w) (hb : b_val.val < 2^w) (hw : 2^(w+1) < p) :
    (a_val - b_val + (2:ZMod p)^w).val / 2^w = if a_val.val < b_val.val then 0 else 1 := by
  rw [diff_val_eq ha hb hw]
  have h2 : 2^(w+1) = 2^w + 2^w := by ring
  split
  · next hab => exact Nat.div_eq_of_lt (by omega)
  · next hab => exact Nat.div_eq_of_lt_le (by omega) (by omega)

lemma convertsM
  [p.AtLeastTwo]
  {state} {w : ℕ} {a b : F p} {a_val b_val : ZMod p}
  (h_a : Converts F.conversion state a a_val)
  (h_b : Converts F.conversion state b b_val)
  (ha : a_val.val < 2^w)
  (hb : b_val.val < 2^w)
  (hw : 2^(w+1) < p)
:
  ConvertsM FB.conversion (lessThan w a b) state (decide (a_val.val < b_val.val)) True
:= by
  unfold lessThan
  rw [sub_def]
  step mkSub.convertsM h_a h_b as diff
  step mkF.convertsM as pow
  rw [add_def]
  step mkAdd.convertsM h_diff h_pow as d
  step num2bits.convertsM h_d as bits
  have h_top := FArray.converts_getElem h_bits (show w < w + 1 by omega)
  simp only [Vector.getElem_map] at h_top
  rw [num2bitsLsbPureV_getElem_last w _, diff_val_div_eq ha hb hw] at h_top
  apply convertsM_of_convertsM (not.convertsM h_top)
  · by_cases hab : a_val.val < b_val.val <;> simp [hab]
  · trivial

-- Old-model native_decide test vectors (Clap/Lang.lean:1064-1080), carried over as documentation
-- since there is no way to re-run them against the new model:
--   F.lessThan 1 (0 : F p) 1 == some 1
--   F.lessThan 1 (0 : F p) 0 == some 0
--   F.lessThan 2 (1 : F p) 2 == some 1
--   F.lessThan 2 (2 : F p) 1 == some 0
--   F.lessThan 8 (42 : F p) (2^8 - 1) == some 1
--   F.lessThan 8 (2^8 - 1) (42 : F p) == some 0

end lessThan

end Clap.Lang
