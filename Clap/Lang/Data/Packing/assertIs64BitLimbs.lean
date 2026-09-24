import Clap.Lang.Core.Combinators.foldlM
import Clap.Lang.Core.FUnit.assert_range
import Clap.Model.ConstraintSystem.toCs
import Clap.Model.WitnessGenerator.toWg

namespace Clap.Lang.Packing

variable {p : ℕ}

/-- Range-check every element of `a` to 64 bits -/
def assertIs64BitLimbs {numLimbs : ℕ} (a : FVec p numLimbs) : ClapM p Unit :=
  a.foldlM (fun _ x ↦ assert_range 64 x) ()

namespace assertIs64BitLimbs

lemma convertsM
  {numLimbs : ℕ}
  {state : ClapMState p}
  {a : FVec p numLimbs}
  {a_vals : Vector (ZMod p) numLimbs}
  (h_a : Converts FVec.conversion state a a_vals)
:
  ConvertsM FUnit.conversion (assertIs64BitLimbs a) state () (∀ i : Fin numLimbs, a_vals[i].val < 2 ^ 64)
:= by
  unfold assertIs64BitLimbs
  apply convertsM_of_convertsM
    (convertsM_foldlM_constraints (C_acc := FUnit.conversion) (init_val := ())
      (f_spec := fun _ _ ↦ ()) (step_constraints := fun (x : ZMod p) ↦ x.val < 2 ^ 64)
      (fun i ↦ FVec.converts_getElem h_a i.isLt) FUnit.converts
      (fun _ h_x ↦ assert_range.convertsM h_x))
  . rfl
  . trivial

end assertIs64BitLimbs

section examples

private abbrev q : ℕ := Primes.bn254

/-- `assertIs64BitLimbs` over `n` public inputs. -/
private def check (n : ℕ) : ClapM q Unit := do
  let xs ← (Vector.range n).mapM (fun i ↦ liftM (HashConsM.mkVar (p := q) i))
  assertIs64BitLimbs xs

private def sat {n : ℕ} (xs : Vector (ZMod q) n) : Bool :=
  let circ  := (check n).getCircuit n (HashConsSt.empty q)
  let cache := (check n).getHashConsState n (HashConsSt.empty q)
  (circ.toCs cache n).run ((circ.toWg cache n).run xs)

example : sat #v[1, 2, 3, 4] = true := by native_decide
example : sat #v[1, 2, 3, 2^64 - 1] = true := by native_decide
example : sat #v[2^64] = false := by native_decide
example : sat #v[1, 2, 2^64 + 5] = false := by native_decide

end examples

end Clap.Lang.Packing
