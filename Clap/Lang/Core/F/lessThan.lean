import Clap.Model.ConstraintSystem.toCs
import Clap.Model.Convert.Specialised
import Clap.Model.WitnessGenerator.toWg
import Clap.Lang.Core.F.mkAdd
import Clap.Lang.Core.F.mkF
import Clap.Lang.Core.F.mkSub
import Clap.Lang.Gate.num2bits
import Clap.Lang.Core.FB.assert_eq
import Clap.Lang.Core.FB.not
import Clap.Lang.Core.FB.ofBool
namespace Clap.Lang

variable {p : ℕ}

/-- `a < b` for `a, b` known to lie in `[0, 2^w)`, with `2^(w+1) < p`. Under those bounds
`a - b + 2^w` cannot wrap around the field, so it always passes `num2bits`' `(w + 1)`-bit range
check (hence `convertsM`'s slot 5 `True`), and its top bit is set exactly when `a ≥ b`.

Like circomlib's `LessThan`, it range-checks only that offset, never `a` or `b`. For operands
not known to be in range — top-level inputs, say — use `lessThan.convertsM_unchecked`, and
discharge the bounds once an earlier `assert_range` has established them, with
`convertsM_bind_guard` and the bridge lemmas `lessThanRaw_eq` / `lessThanOk_of`. -/
def lessThan (w : ℕ) (a b : F p) : ClapM p (FB p) := do
  let diff ← a - b
  let pow ← mkF ((2 : ZMod p) ^ w)
  let d ← diff + pow
  let d ← num2bits (w + 1) d
  not d[w]

/-- `a ≤ b`, as `¬(b < a)`.

The old model had this as `lessThan w a (b + 1)`. That spelling does
not survive the move to `F p = BoundRef p`: `F p` reduces through `abbrev` to `ℕ`, so `b + 1`
elaborates as `Nat.succ` on the heap index rather than a field addition, and the gadget
silently compares against whatever node sits at slot `b + 1`. -/
def lessEqThan (w : ℕ) (a b : F p) : ClapM p (FB p) := do
  let gt ← lessThan w b a
  not gt

def greaterThan (w : ℕ) (a b : F p) : ClapM p (FB p) :=
  lessThan w b a

/-- `a ≥ b`, as `¬(a < b)`. See `lessEqThan` for why this is not `lessThan w b (a + 1)`. -/
def greaterEqThan (w : ℕ) (a b : F p) : ClapM p (FB p) := do
  let lt ← lessThan w a b
  not lt

namespace lessThan

/-- What `lessThan w a b` computes for any inputs: the negated top bit of the (w+1)-bit
decomposition of `a - b + 2^w`. -/
def lessThanRaw (w : ℕ) (a b : ZMod p) : Bool :=
  !((num2bitsLsbPureV (w + 1) (a - b + (2 : ZMod p) ^ w))[w] == 1)

/-- The constraint `lessThan` emits: the offset fits in `w + 1` bits. -/
def lessThanOk (w : ℕ) (a b : ZMod p) : Prop := (a - b + (2 : ZMod p) ^ w).val < 2 ^ (w + 1)

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

/-- For operands in `[0, 2^w)` with `2^(w+1) < p`, the raw bit is the comparison. -/
lemma lessThanRaw_eq {w : ℕ} {a b : ZMod p}
    (ha : a.val < 2^w) (hb : b.val < 2^w) (hw : 2^(w+1) < p) :
    lessThanRaw w a b = decide (a.val < b.val) := by
  -- `simp` needs `(0 : ZMod p) ≠ 1`, and `hw` makes `p` big enough.
  have h1p : 1 < p := lt_of_le_of_lt Nat.one_le_two_pow hw
  haveI : Fact (1 < p) := ⟨h1p⟩
  haveI : NeZero p := ⟨by omega⟩
  unfold lessThanRaw
  rw [num2bitsLsbPureV_getElem_last w _, diff_val_div_eq ha hb hw]
  by_cases hab : a.val < b.val <;> simp [hab]

/-- For operands in `[0, 2^w)` with `2^(w+1) < p`, the offset always passes the range check. -/
lemma lessThanOk_of {w : ℕ} {a b : ZMod p}
    (ha : a.val < 2^w) (hb : b.val < 2^w) (hw : 2^(w+1) < p) :
    lessThanOk w a b := by
  have h1p : 1 < p := lt_of_le_of_lt Nat.one_le_two_pow hw
  haveI : NeZero p := ⟨by omega⟩
  unfold lessThanOk
  rw [diff_val_eq ha hb hw, pow_succ]
  omega

/-- `lessThan` on arbitrary inputs. There are no range hypotheses, so this composes after the
range checks that would establish them: its value is the raw top bit, and its slot 5 is the offset
range check the circuit really emits. For in-range operands `lessThanRaw_eq` / `lessThanOk_of`
turn the two into `decide (a_val.val < b_val.val)` and `True`. -/
lemma convertsM_unchecked
  [p.AtLeastTwo]
  {state} {w : ℕ} {a b : F p} {a_val b_val : ZMod p}
  (h_a : Converts F.conversion state a a_val)
  (h_b : Converts F.conversion state b b_val)
:
  ConvertsM FB.conversion (lessThan w a b) state (lessThanRaw w a_val b_val)
    (lessThanOk w a_val b_val)
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
  apply convertsM_of_convertsM (not.convertsM h_top)
  · rfl
  -- `num2bits`' range check on the offset is `lessThanOk` itself
  · exact iff_of_true trivial (fun h _ _ _ => h)
  -- `step`'s side goal for the `num2bits` bind: the spec's constraint implies the check
  · exact fun h => h trivial trivial trivial

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
:= convertsM_of_convertsM (convertsM_unchecked h_a h_b) (lessThanRaw_eq ha hb hw)
    (iff_true_intro (lessThanOk_of ha hb hw))

end lessThan

namespace greaterThan

lemma convertsM_unchecked
  [p.AtLeastTwo]
  {state} {w : ℕ} {a b : F p} {a_val b_val : ZMod p}
  (h_a : Converts F.conversion state a a_val)
  (h_b : Converts F.conversion state b b_val)
:
  ConvertsM FB.conversion (greaterThan w a b) state (lessThan.lessThanRaw w b_val a_val)
    (lessThan.lessThanOk w b_val a_val)
:= lessThan.convertsM_unchecked h_b h_a

lemma convertsM
  [p.AtLeastTwo]
  {state} {w : ℕ} {a b : F p} {a_val b_val : ZMod p}
  (h_a : Converts F.conversion state a a_val)
  (h_b : Converts F.conversion state b b_val)
  (ha : a_val.val < 2^w)
  (hb : b_val.val < 2^w)
  (hw : 2^(w+1) < p)
:
  ConvertsM FB.conversion (greaterThan w a b) state (decide (b_val.val < a_val.val)) True
:= lessThan.convertsM h_b h_a hb ha hw

end greaterThan

namespace lessEqThan

lemma convertsM_unchecked
  [p.AtLeastTwo]
  {state} {w : ℕ} {a b : F p} {a_val b_val : ZMod p}
  (h_a : Converts F.conversion state a a_val)
  (h_b : Converts F.conversion state b b_val)
:
  ConvertsM FB.conversion (lessEqThan w a b) state (!lessThan.lessThanRaw w b_val a_val)
    (lessThan.lessThanOk w b_val a_val)
:= by
  unfold lessEqThan
  step lessThan.convertsM_unchecked h_b h_a as gt
  apply convertsM_of_convertsM (not.convertsM h_gt)
  · rfl
  · simp

lemma convertsM
  [p.AtLeastTwo]
  {state} {w : ℕ} {a b : F p} {a_val b_val : ZMod p}
  (h_a : Converts F.conversion state a a_val)
  (h_b : Converts F.conversion state b b_val)
  (ha : a_val.val < 2^w)
  (hb : b_val.val < 2^w)
  (hw : 2^(w+1) < p)
:
  ConvertsM FB.conversion (lessEqThan w a b) state (decide (a_val.val ≤ b_val.val)) True
:= convertsM_of_convertsM (convertsM_unchecked h_a h_b)
    (by rw [lessThan.lessThanRaw_eq hb ha hw]; simp only [← decide_not, Nat.not_lt])
    (iff_true_intro (lessThan.lessThanOk_of hb ha hw))

end lessEqThan

namespace greaterEqThan

lemma convertsM_unchecked
  [p.AtLeastTwo]
  {state} {w : ℕ} {a b : F p} {a_val b_val : ZMod p}
  (h_a : Converts F.conversion state a a_val)
  (h_b : Converts F.conversion state b b_val)
:
  ConvertsM FB.conversion (greaterEqThan w a b) state (!lessThan.lessThanRaw w a_val b_val)
    (lessThan.lessThanOk w a_val b_val)
:= by
  unfold greaterEqThan
  step lessThan.convertsM_unchecked h_a h_b as lt
  apply convertsM_of_convertsM (not.convertsM h_lt)
  · rfl
  · simp

lemma convertsM
  [p.AtLeastTwo]
  {state} {w : ℕ} {a b : F p} {a_val b_val : ZMod p}
  (h_a : Converts F.conversion state a a_val)
  (h_b : Converts F.conversion state b b_val)
  (ha : a_val.val < 2^w)
  (hb : b_val.val < 2^w)
  (hw : 2^(w+1) < p)
:
  ConvertsM FB.conversion (greaterEqThan w a b) state (decide (b_val.val ≤ a_val.val)) True
:= convertsM_of_convertsM (convertsM_unchecked h_a h_b)
    (by rw [lessThan.lessThanRaw_eq ha hb hw]; simp only [← decide_not, Nat.not_lt])
    (iff_true_intro (lessThan.lessThanOk_of ha hb hw))

end greaterEqThan

section examples

/-! The old model's `native_decide` vectors (`old/Clap/Lang.lean:1064-1080`), now runnable: the
gadget is lowered with `Circuit.toWg` / `Circuit.toCs` and its result asserted equal to the
expected bit, so the circuit is satisfiable exactly when the gadget computes what the old
model computed.

These are also the regression test for `lessEqThan` / `greaterEqThan`, whose old spelling
`lessThan w a (b + 1)` silently did `Nat` arithmetic on the heap index — see the doc comment
on `lessEqThan`.

`q` must exceed `2^(w+1)`, so `2^9 = 512` for the `w = 8` vectors. `1031` has a cheap `norm_num`
primality proof, which keeps the test off the `sorry`'d primality of `Primes.goldilocks` and
`Primes.bn254` (`Clap/Util/Primes.lean`). -/

private abbrev q : ℕ := 1031

local instance instFactPrimeComparisonQ : Fact (Nat.Prime q) := ⟨by norm_num⟩

private def check (g : ℕ → F q → F q → ClapM q (FB q))
    (w : ℕ) (a b : ZMod q) (expected : Bool) : ClapM q Unit := do
  let a' ← mkF a
  let b' ← mkF b
  let r ← g w a' b'
  let e ← FB.ofBool expected
  FB.assert_eq r e

/-- `true` when `g w a b` really does evaluate to `expected` in the emitted circuit. -/
private def sat (g : ℕ → F q → F q → ClapM q (FB q))
    (w : ℕ) (a b : ZMod q) (expected : Bool) : Bool :=
  let c := check g w a b expected
  let circ  := c.getCircuit 0 (HashConsSt.empty q)
  let cache := c.getHashConsState 0 (HashConsSt.empty q)
  (circ.toCs cache 0).run ((circ.toWg cache 0).run #v[])

example : sat lessThan 1 0 1   true  = true := by native_decide
example : sat lessThan 1 0 0   false = true := by native_decide
example : sat lessThan 2 1 2   true  = true := by native_decide
example : sat lessThan 2 2 1   false = true := by native_decide
example : sat lessThan 8 42 255 true  = true := by native_decide
example : sat lessThan 8 255 42 false = true := by native_decide

example : sat lessEqThan 2 2 2 true  = true := by native_decide
example : sat lessEqThan 2 1 2 true  = true := by native_decide
example : sat lessEqThan 2 3 2 false = true := by native_decide

example : sat greaterThan 2 3 2 true  = true := by native_decide
example : sat greaterThan 2 2 2 false = true := by native_decide

example : sat greaterEqThan 2 3 2 true  = true := by native_decide
example : sat greaterEqThan 2 2 2 true  = true := by native_decide
example : sat greaterEqThan 2 2 3 false = true := by native_decide

end examples

end Clap.Lang
