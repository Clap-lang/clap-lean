import Clap.Lang.F.lessThan
import Clap.Lang.FB.eq

namespace Clap.Lang.F8

variable {p : ℕ}

def eq [p.AtLeastTwo] (a b : F p) : ClapM p (FB p) := Clap.Lang.eq a b

def lessThan (a b : F p) : ClapM p (FB p) := Clap.Lang.lessThan 8 a b

def greaterThan (a b : F p) : ClapM p (FB p) := Clap.Lang.greaterThan 8 a b

def lessEqThan (a b : F p) : ClapM p (FB p) := Clap.Lang.lessEqThan 8 a b

def greaterEqThan (a b : F p) : ClapM p (FB p) := Clap.Lang.greaterEqThan 8 a b

/-! ## Specifications

These gadgets are byte-width specialisations, so they take `F8.conversion` hypotheses
(`IdealT := UInt8`) and state their results over `UInt8`, while the underlying
`Clap.Lang.lessThan` family works over `ZMod p`. The two `val_*` lemmas below bridge the two
and are shared by all five specifications. -/

/-- A byte's field value is its `toNat`, when the field is big enough to hold a byte. -/
lemma val_eq {e_val : UInt8} (hp : 2 ^ (8 + 1) < p) :
    ((e_val.toNat : ZMod p)).val = e_val.toNat := by
  have h_lt : e_val.toNat < 256 := e_val.toNat_lt_size
  have h_pow : (2 : ℕ) ^ (8 + 1) = 512 := by norm_num
  exact ZMod.val_natCast_of_lt (by omega)

/-- The `< 2^8` bound the comparison family needs of each operand. -/
lemma val_lt {e_val : UInt8} (hp : 2 ^ (8 + 1) < p) :
    ((e_val.toNat : ZMod p)).val < 2 ^ 8 := by
  have h_lt : e_val.toNat < 256 := e_val.toNat_lt_size
  rw [val_eq hp]
  norm_num
  omega

namespace lessThan

lemma convertsM
  [p.AtLeastTwo]
  {state : ClapMState p}
  {a b : F8 p}
  {a_val b_val : UInt8}
  (hp : 2 ^ (8 + 1) < p)
  (h_a : Converts F8.conversion state a a_val)
  (h_b : Converts F8.conversion state b b_val)
:
  ConvertsM FB.conversion (F8.lessThan a b) state (decide (a_val < b_val)) True
:= by
  unfold F8.lessThan
  apply convertsM_of_convertsM
    (Clap.Lang.lessThan.convertsM
      (F.converts_of_F8_converts h_a) (F.converts_of_F8_converts h_b)
      (val_lt hp) (val_lt hp) hp)
  · rw [val_eq hp, val_eq hp]; rfl
  · trivial

end lessThan

namespace greaterThan

lemma convertsM
  [p.AtLeastTwo]
  {state : ClapMState p}
  {a b : F8 p}
  {a_val b_val : UInt8}
  (hp : 2 ^ (8 + 1) < p)
  (h_a : Converts F8.conversion state a a_val)
  (h_b : Converts F8.conversion state b b_val)
:
  ConvertsM FB.conversion (F8.greaterThan a b) state (decide (b_val < a_val)) True
:= by
  unfold F8.greaterThan
  apply convertsM_of_convertsM
    (Clap.Lang.greaterThan.convertsM
      (F.converts_of_F8_converts h_a) (F.converts_of_F8_converts h_b)
      (val_lt hp) (val_lt hp) hp)
  · rw [val_eq hp, val_eq hp]; rfl
  · trivial

end greaterThan

namespace lessEqThan

lemma convertsM
  [p.AtLeastTwo]
  {state : ClapMState p}
  {a b : F8 p}
  {a_val b_val : UInt8}
  (hp : 2 ^ (8 + 1) < p)
  (h_a : Converts F8.conversion state a a_val)
  (h_b : Converts F8.conversion state b b_val)
:
  ConvertsM FB.conversion (F8.lessEqThan a b) state (decide (a_val ≤ b_val)) True
:= by
  unfold F8.lessEqThan
  apply convertsM_of_convertsM
    (Clap.Lang.lessEqThan.convertsM
      (F.converts_of_F8_converts h_a) (F.converts_of_F8_converts h_b)
      (val_lt hp) (val_lt hp) hp)
  · rw [val_eq hp, val_eq hp]; rfl
  · trivial

end lessEqThan

namespace greaterEqThan

lemma convertsM
  [p.AtLeastTwo]
  {state : ClapMState p}
  {a b : F8 p}
  {a_val b_val : UInt8}
  (hp : 2 ^ (8 + 1) < p)
  (h_a : Converts F8.conversion state a a_val)
  (h_b : Converts F8.conversion state b b_val)
:
  ConvertsM FB.conversion (F8.greaterEqThan a b) state (decide (b_val ≤ a_val)) True
:= by
  unfold F8.greaterEqThan
  apply convertsM_of_convertsM
    (Clap.Lang.greaterEqThan.convertsM
      (F.converts_of_F8_converts h_a) (F.converts_of_F8_converts h_b)
      (val_lt hp) (val_lt hp) hp)
  · rw [val_eq hp, val_eq hp]; rfl
  · trivial

end greaterEqThan

namespace eq

lemma convertsM
  [p.AtLeastTwo]
  {state : ClapMState p}
  {a b : F8 p}
  {a_val b_val : UInt8}
  (hp : 2 ^ (8 + 1) < p)
  (h_a : Converts F8.conversion state a a_val)
  (h_b : Converts F8.conversion state b b_val)
:
  ConvertsM FB.conversion (F8.eq a b) state (decide (a_val = b_val)) True
:= by
  unfold F8.eq
  apply convertsM_of_convertsM
    (Clap.Lang.eq.convertsM (F.converts_of_F8_converts h_a) (F.converts_of_F8_converts h_b))
  · rw [Bool.eq_iff_iff]
    simp only [beq_iff_eq, decide_eq_true_eq]
    rw [← (ZMod.val_injective p).eq_iff, val_eq hp, val_eq hp, ← UInt8.toNat_inj]
  · trivial

end eq

end Clap.Lang.F8
