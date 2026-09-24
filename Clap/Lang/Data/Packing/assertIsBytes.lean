import Clap.Lang.Core.Combinators.foldlM
import Clap.Lang.Core.FUnit.assert_range
import Clap.Model.ConstraintSystem.toCs
import Clap.Model.WitnessGenerator.toWg

namespace Clap.Lang.Packing

variable {p : ℕ}

/-- Range-check every element of `a` to a byte -/
def assertIsBytes {numBytes : ℕ} (a : FVec p numBytes) : ClapM p Unit :=
  a.foldlM (fun _ x ↦ assert_range 8 x) ()

namespace assertIsBytes

lemma convertsM
  {numBytes : ℕ}
  {state : ClapMState p}
  {a : FVec p numBytes}
  {a_vals : Vector (ZMod p) numBytes}
  (h_a : Converts FVec.conversion state a a_vals)
:
  ConvertsM FUnit.conversion (assertIsBytes a) state ()
    (∀ i : Fin numBytes, a_vals[i].val < 2 ^ 8)
:= by
  unfold assertIsBytes
  apply convertsM_of_convertsM
    (convertsM_foldlM_constraints (C_acc := FUnit.conversion) (init_val := ())
      (f_spec := fun _ _ ↦ ()) (step_constraints := fun (x : ZMod p) ↦ x.val < 2 ^ 8)
      (fun i ↦ FVec.converts_getElem h_a i.isLt) FUnit.converts
      (fun _ h_x ↦ assert_range.convertsM h_x))
  . rfl
  . trivial

end assertIsBytes

section examples

private abbrev q : ℕ := 1031

local instance instFactPrimeAssertIsBytesQ : Fact (Nat.Prime q) := ⟨by norm_num⟩

/-- `assertIsBytes` over `n` public inputs. -/
private def check (n : ℕ) : ClapM q Unit := do
  let xs ← (Vector.range n).mapM (fun i ↦ liftM (HashConsM.mkVar (p := q) i))
  assertIsBytes xs

private def sat {n : ℕ} (xs : Vector (ZMod q) n) : Bool :=
  let circ  := (check n).getCircuit n (HashConsSt.empty q)
  let cache := (check n).getHashConsState n (HashConsSt.empty q)
  (circ.toCs cache n).run ((circ.toWg cache n).run xs)

example : sat #v[1, 2, 3, 4] = true := by native_decide
example : sat #v[1, 2, 3, 255] = true := by native_decide
example : sat #v[256] = false := by native_decide
example : sat #v[1, 2, 261] = false := by native_decide

end examples

end Clap.Lang.Packing
