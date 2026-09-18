import Clap.Lang.Gate.num2bits
import Clap.Model.ConstraintSystem.toCs
import Clap.Model.WitnessGenerator.toWg

namespace Clap.Lang

variable {p : ℕ}

/-- Range-check `e` to `w` bits. Old model: `F.assert_range` (`old/Clap/Lang.lean:25`), where
`num2bits` was `Option`-valued and returned `none` for `e ≥ 2^w`.

**The constraints slot is `True`, and that is deliberate.** In the `ConvertsM` semantics the
`num2bits` gate asserts nothing: `stepNum2bits` (`Clap/Model/CircuitEvalSt.lean:412`)
stores the *truncated* low `w` bits of the input, and `constraints_stepNum2bits` contributes
only allocatedness. So `True` is the honest slot 5 for this gadget as the model stands.

The emitted circuit is stronger. The `toCs` lowering
(`Clap/Model/ConstraintSystem/num2bits.lean`) emits `bits2num(bits) - expr` alongside the
booleanity constraints, and genuinely rejects out-of-range inputs — see the smoke test at the
bottom of this file, which shows a single-gate `assert_range 4` accepting `5` and rejecting
`20` and `31`.

Closing that gap means strengthening `stepNum2bits` to carry the range condition and reproving
`num2bits.constraints` as `e_val.val < 2^w`; every gadget built on `num2bits` (`lessThan` and
the whole comparison family, `binSum`, `F32.add`) would then need to discharge it. That is a
change to the core semantics and is deliberately not made here. -/
def assert_range (w : ℕ) (e : F p) : ClapM p Unit := do
  let _ ← num2bits w e
  return ()

namespace assert_range

lemma convertsM
  {state}
  {w : ℕ}
  {e : F p}
  {e_val : ZMod p}
  (h_e : Converts F.conversion state e e_val)
:
  ConvertsM FUnit.conversion (assert_range w e) state () True
:= by
  unfold assert_range
  step num2bits.convertsM h_e as bits
  apply convertsM_pure
  · exact FUnit.converts
  · trivial

section examples

/-! Smoke tests. These run the gadget through `Circuit.toWg` and `Circuit.toCs`, so unlike the
`convertsM` above they observe the constraints the circuit *actually* emits. They are the
evidence for the doc comment on `assert_range`: the emitted circuit rejects out-of-range inputs
even though the `ConvertsM` constraints slot is `True`.

A concrete prime with a real primality proof is needed — `Primes.goldilocks` and
`Primes.bn254` are `sorry`'d in `Clap/Util/Primes.lean`, and `native_decide` refuses anything
depending on `sorry`. -/

private abbrev q : ℕ := 47

local instance instFactPrimeAssertRangeQ : Fact (Nat.Prime q) := ⟨by norm_num⟩

/-- `assert_range 4` applied to a single public input. -/
private def rangeCheck : ClapM q Unit := do
  let x ← liftM (HashConsM.mkVar (p := q) 0)
  assert_range 4 x

private def sat (x : ZMod q) : Bool :=
  let circ  := rangeCheck.getCircuit 1 (HashConsSt.empty q)
  let cache := rangeCheck.getHashConsState 1 (HashConsSt.empty q)
  (circ.toCs cache 1).run ((circ.toWg cache 1).run #v[x])

example : sat 0  = true  := by native_decide
example : sat 5  = true  := by native_decide
example : sat 15 = true  := by native_decide
-- The gadget's `convertsM` says `True`, but the circuit is unsatisfiable here:
example : sat 16 = false := by native_decide
example : sat 20 = false := by native_decide
example : sat 31 = false := by native_decide

end examples

end assert_range

end Clap.Lang
