import Clap.Lang.Data.FArray.assert_eq
import Clap.Lang.Data.FArray.default
import Clap.Lang.Gate.num2bits
import Clap.Lang.Data.FArray.ofBitVec
import Clap.Lang.Data.FArray.zeroExtend
import Clap.Lang.Data.FBitVec.binSum
import Clap.Model.ConstraintSystem.toCs
import Clap.Model.WitnessGenerator.toWg

/-!
# Fixed-width bit vectors
-/

namespace Clap.Lang

variable {p : ℕ}

abbrev FBV8 (p : ℕ) := FArray p 8
abbrev F32 (p : ℕ) := FArray p 32
abbrev F64 (p : ℕ) := FArray p 64

namespace FBV8

def ofUInt8 (u : UInt8) : ClapM p (FBV8 p) :=
  FArray.ofBitVec u.toBitVec

namespace ofUInt8

lemma convertsM
  [p.AtLeastTwo]
  {u : UInt8}
  {state : ClapMState p}
:
  ConvertsM FArray.conversion (ofUInt8 (p := p) u) state
    (Vector.ofFn (fun i ↦ u.toBitVec[i])) True
:= FArray.ofBitVec.convertsM

end ofUInt8

/-- Decompose a field element into 8 bits, range-checking it: slot 5 is `x_val.val < 2 ^ 8`. -/
def ofF (x : F p) : ClapM p (FBV8 p) :=
  num2bits 8 x

namespace ofF

lemma convertsM
  {x : F p}
  {x_val : ZMod p}
  {state : ClapMState p}
:
  Converts F.conversion state x x_val →
  ConvertsM FArray.conversion (ofF x) state
    (num2bitsLsbPureV 8 x_val |>.map fun y ↦ y == 1) (x_val.val < 2 ^ 8)
:= num2bits.convertsM

end ofF

end FBV8


namespace F32

def default : ClapM p (F32 p) :=
  FArray.default 32

namespace default

lemma convertsM
  [p.AtLeastTwo]
  {state : ClapMState p}
:
  ConvertsM FArray.conversion (default (p := p)) state (Vector.replicate 32 false) True
:= FArray.default.convertsM

end default

def ofUInt32 (u : UInt32) : ClapM p (F32 p) :=
  FArray.ofBitVec u.toBitVec

namespace ofUInt32

lemma convertsM
  [p.AtLeastTwo]
  {u : UInt32}
  {state : ClapMState p}
:
  ConvertsM FArray.conversion (ofUInt32 (p := p) u) state
    (Vector.ofFn (fun i ↦ u.toBitVec[i])) True
:= FArray.ofBitVec.convertsM

end ofUInt32

/-- Decompose a field element into 32 bits, range-checking it: slot 5 is `x_val.val < 2 ^ 32`. -/
def ofF (x : F p) : ClapM p (F32 p) :=
  num2bits 32 x

namespace ofF

lemma convertsM
  {x : F p}
  {x_val : ZMod p}
  {state : ClapMState p}
:
  Converts F.conversion state x x_val →
  ConvertsM FArray.conversion (ofF x) state
    (num2bitsLsbPureV 32 x_val |>.map fun y ↦ y == 1) (x_val.val < 2 ^ 32)
:= num2bits.convertsM

end ofF

/-- Zero-extend a byte to 32 bits. -/
def ofFBV8 (u8 : FBV8 p) : ClapM p (F32 p) :=
  FArray.zeroExtend u8 24

namespace ofFBV8

lemma convertsM
  [p.AtLeastTwo]
  {u8 : FBV8 p}
  {vals : Vector Bool 8}
  {state : ClapMState p}
  (h_u8 : Converts FArray.conversion state u8 vals)
:
  ConvertsM FArray.conversion (ofFBV8 u8) state
    (vals ++ Vector.replicate 24 false) True
:= FArray.zeroExtend.convertsM (w' := 24) h_u8

end ofFBV8

/-- 32-bit wrapping addition. -/
def add (a b : F32 p) : ClapM p (F32 p) := do
  let s ← FBitVec.binSum a b
  return (s.take 32).cast (by omega)

namespace add

lemma convertsM
  [p.AtLeastTwo]
  {a b : F32 p}
  {a_vals b_vals : Vector Bool 32}
  {state : ClapMState p}
  (h_a : Converts FArray.conversion state a a_vals)
  (h_b : Converts FArray.conversion state b b_vals)
:
  ConvertsM FArray.conversion (add a b) state
    ((((num2bitsLsbPureV (32 + 1)
          (FArray.toNum (p := p) a_vals + FArray.toNum (p := p) b_vals)).map
        fun x ↦ x == 1).take 32).cast (by omega))
    True
:= by
  unfold add
  step FBitVec.binSum.convertsM h_a h_b as s
  apply convertsM_pure
  · exact FArray.converts_vector_cast (FArray.converts_take h_s) (by omega)
  · trivial

end add

def assert_eq (a b : F32 p) : ClapM p Unit :=
  FArray.assert_eq a b

namespace assert_eq

lemma convertsM
  [p.AtLeastTwo]
  {a b : F32 p}
  {a_vals b_vals : Vector Bool 32}
  {state : ClapMState p}
  (h_a : Converts FArray.conversion state a a_vals)
  (h_b : Converts FArray.conversion state b b_vals)
:
  ConvertsM FUnit.conversion (assert_eq a b) state ()
    (∀ i : Fin 32, a_vals[i] = b_vals[i])
:= FArray.assert_eq.convertsM h_a h_b

end assert_eq

end F32


namespace F64

/-- Decompose a field element into 64 bits, range-checking it: slot 5 is `x_val.val < 2 ^ 64`. -/
def ofF (x : F p) : ClapM p (F64 p) :=
  num2bits 64 x

namespace ofF

lemma convertsM
  {x : F p}
  {x_val : ZMod p}
  {state : ClapMState p}
:
  Converts F.conversion state x x_val →
  ConvertsM FArray.conversion (ofF x) state
    (num2bitsLsbPureV 64 x_val |>.map fun y ↦ y == 1) (x_val.val < 2 ^ 64)
:= num2bits.convertsM

end ofF

end F64


section examples

/-! Smoke test for `F32.add`, run end to end through `Circuit.toWg` / `Circuit.toCs`.

The modulus must exceed `2^33` so the 33-bit `binSum` cannot wrap the field. `8589934609` has a
cheap `norm_num` primality proof, which keeps the test off the `sorry`'d primality of
`Primes.goldilocks` and `Primes.bn254` (`Clap/Util/Primes.lean`). -/

private abbrev q : ℕ := 8589934609

local instance instFactPrimeWidthsQ : Fact (Nat.Prime q) := ⟨by norm_num⟩

private def check (a b e : BitVec 32) : ClapM q Unit := do
  let a' ← FArray.ofBitVec a
  let b' ← FArray.ofBitVec b
  let e' ← FArray.ofBitVec e
  F32.assert_eq (← F32.add a' b') e'

private def sat (a b e : BitVec 32) : Bool :=
  let circ  := (check a b e).getCircuit 0 (HashConsSt.empty q)
  let cache := (check a b e).getHashConsState 0 (HashConsSt.empty q)
  (circ.toCs cache 0).run ((circ.toWg cache 0).run #v[])

example : sat 1 1 2 = true := by native_decide
example : sat 65535 65535 131070 = true := by native_decide
-- old: letI a : UInt32 := 2^32 - 1; F32.add a 1 = UInt32.add a 1
example : sat 4294967295 1 0 = true := by native_decide
example : sat 4294967295 2 1 = true := by native_decide
example : sat 1 1 3 = false := by native_decide
-- the dropped 33rd bit is not silently kept anywhere
example : sat 2147483648 2147483648 0 = true := by native_decide

end examples

end Clap.Lang
