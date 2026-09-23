import Clap.Lang.Core.F.mkAdd
import Clap.Lang.Data.FArray.bits2num
import Clap.Lang.Gate.num2bits
import Clap.Lang.Data.FArray.ofBitVec
import Clap.Lang.Data.FBitVec.assert_eq
import Clap.Model.ConstraintSystem.toCs
import Clap.Model.WitnessGenerator.toWg

namespace Clap.Lang.FBitVec

variable {p : ℕ}

/-- Add two `w`-bit vectors, returning `w+1` bits. -/
def binSum {w : ℕ} (a b : FBitVec p w) : ClapM p (FBitVec p (w + 1)) := do
  let av ← FArray.bits2num a
  let bv ← FArray.bits2num b
  let s ← av + bv
  num2bits (w + 1) s

namespace binSum

/-- `toNum` of `w` bits is the cast of a natural number below `2 ^ w`, so its value is below
`2 ^ w` too, whatever the modulus. -/
private lemma toNum_val_lt {w : ℕ} (bits : Vector Bool w) :
  (FArray.toNum (p := p) bits).val < 2 ^ w
:= by
  have key : ∀ l : List Bool, ∃ n : ℕ, n < 2 ^ l.length ∧
      l.foldr (fun b acc ↦ (if b then (1 : ZMod p) else 0) + 2 * acc) 0 = (n : ZMod p) := by
    intro l
    induction l with
    | nil => exact ⟨0, by simp, by simp⟩
    | cons b t ih =>
      obtain ⟨n, hn, h_eq⟩ := ih
      refine ⟨(if b then 1 else 0) + 2 * n, ?_, ?_⟩
      · rw [List.length_cons, pow_succ]
        split <;> omega
      · rw [List.foldr_cons, h_eq]
        cases b <;> simp
  obtain ⟨n, hn, h_eq⟩ := key bits.toList
  rw [Vector.length_toList] at hn
  have h_toNum : FArray.toNum (p := p) bits = (n : ZMod p) := by
    rw [← h_eq]
    simp [FArray.toNum]
  rw [h_toNum, ZMod.val_natCast]
  exact lt_of_le_of_lt (Nat.mod_le _ _) hn

lemma convertsM
  [p.AtLeastTwo]
  {w : ℕ}
  {state : ClapMState p}
  {a b : FBitVec p w}
  {a_vals b_vals : Vector Bool w}
  (h_a : Converts FArray.conversion state a a_vals)
  (h_b : Converts FArray.conversion state b b_vals)
:
  ConvertsM FArray.conversion (binSum a b) state
    (num2bitsLsbPureV (w + 1) (FArray.toNum (p := p) a_vals + FArray.toNum (p := p) b_vals)
      |>.map fun x ↦ x == 1)
    True
:= by
  unfold binSum
  step FArray.bits2num.convertsM h_a as av
  step FArray.bits2num.convertsM h_b as bv
  step mkAdd.convertsM h_av h_bv as s
  apply convertsM_of_convertsM (num2bits.convertsM h_s)
  · rfl
  · refine iff_of_true ?_ (fun _ _ _ ↦ trivial)
    have := toNum_val_lt (p := p) a_vals
    have := toNum_val_lt (p := p) b_vals
    exact lt_of_le_of_lt (ZMod.val_add_le _ _) (by rw [pow_succ]; omega)

section examples

/-! Smoke tests, run end to end through `Circuit.toWg` / `Circuit.toCs`

Bit vectors are LSB-first, so `(1 : BitVec 3)` is the old `#v[1,0,0]` and `(2 : BitVec 4)` is
the old `#v[0,1,0,0]`. A small prime with a real `norm_num` primality proof keeps the test off
the `sorry`'d primality of `Primes.goldilocks` and `Primes.bn254`. -/

private abbrev q : ℕ := 47

local instance instFactPrimeBinSumQ : Fact (Nat.Prime q) := ⟨by norm_num⟩

private def check (a b : BitVec 3) (e : BitVec 4) : ClapM q Unit := do
  let a' ← FArray.ofBitVec a
  let b' ← FArray.ofBitVec b
  let e' ← FArray.ofBitVec e
  FBitVec.assert_eq (← binSum a' b') e'

private def sat (a b : BitVec 3) (e : BitVec 4) : Bool :=
  let circ  := (check a b e).getCircuit 0 (HashConsSt.empty q)
  let cache := (check a b e).getHashConsState 0 (HashConsSt.empty q)
  (circ.toCs cache 0).run ((circ.toWg cache 0).run #v[])

-- old: testBinSum #v[1,0,0] #v[1,0,0] #v[0,1,0,0]
example : sat 1 1 2 = true := by native_decide
-- old: testBinSum #v[0,0,1] #v[0,0,1] #v[0,0,0,1]
example : sat 4 4 8 = true := by native_decide
-- old: testBinSum #v[1,1,1] #v[1,0,0] #v[0,0,0,1]
example : sat 7 1 8 = true := by native_decide
-- the carry out of bit 2 really does land in bit 3, not anywhere else
example : sat 7 7 14 = true  := by native_decide
example : sat 1 1 3  = false := by native_decide
example : sat 7 1 0  = false := by native_decide

end examples

end binSum

end Clap.Lang.FBitVec
