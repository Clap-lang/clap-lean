import Clap.Lang.F.mkAdd
import Clap.Lang.FArray.bits2num
import Clap.Lang.FArray.num2bits
import Clap.Lang.FArray.ofBitVec
import Clap.Lang.FBitVec.assert_eq
import Clap.eDSLState.ConstraintSystem.toCs
import Clap.eDSLState.WitnessGenerator.toWg

namespace Clap.Lang.FBitVec

variable {p : ℕ}

/-- Add two `w`-bit vectors, returning `w+1` bits. Old model: `FBitVec.binSum`
(`Clap/Lang.lean:401`), which was `num2bits (w+1) (a.toF + b.toF)`.

The result is the low `w+1` bits of `toNum a + toNum b`, because the `num2bits` gate truncates
in the `ConvertsM` semantics — see `Clap.Lang.assert_range` for the full story. When
`2^(w+1) ≤ p` there is nothing to truncate and the result is the exact sum, but that reading
is not stated separately: `num2bitsLsbPureV` is a concrete pure function, so the spec below
already pins every output bit as a function of the inputs. The smoke tests at the bottom of
this file are what guard the bit ordering. -/
def binSum {w : ℕ} (a b : FBitVec p w) : ClapM p (FBitVec p (w + 1)) := do
  let av ← FArray.bits2num a
  let bv ← FArray.bits2num b
  let s ← av + bv
  num2bits (w + 1) s

namespace binSum

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
  · trivial

section examples

/-! Smoke tests, run end to end through `Circuit.toWg` / `Circuit.toCs`. These are the old
model's `testBinSum` vectors (`Clap/Lang.lean:1088-1092`), which are worth keeping executable
because an off-by-one in bit order typechecks silently.

Bit vectors are LSB-first, so `(1 : BitVec 3)` is the old `#v[1,0,0]` and `(2 : BitVec 4)` is
the old `#v[0,1,0,0]`. A concrete prime with a real primality proof is required —
`Primes.goldilocks` and `Primes.bn254` are `sorry`'d and `native_decide` refuses `sorry`. -/

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
