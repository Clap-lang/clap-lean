import Clap.Lang.Core.Combinators.foldlM
import Clap.Lang.Core.F.mkAdd
import Clap.Lang.Core.F.mkF
import Clap.Lang.Core.F.mkMul
namespace Clap.Lang

variable {p : ℕ}

section dotProduct

/-- `∑ i, a[i] * b[i]`. The old model's `(a.zipWith (· * ·) b).foldl (· + ·) 0` was a pure
fold; every node now has to be allocated, so it is a `foldlM`. -/
def dotProduct {w} (a b : FVec p w) : ClapM p (F p) := do
  let acc0 ← mkF 0
  (a.zip b).foldlM (fun acc xy ↦ do acc + (← xy.1 * xy.2)) acc0

namespace dotProduct

private lemma step_convertsM
  {state : ClapMState p}
  {acc : F p}
  {acc_val : ZMod p}
  {xy : F p × F p}
  {xy_val : ZMod p × ZMod p}
  (h_acc : Converts F.conversion state acc acc_val)
  (h_xy : Converts FPair.conversion state xy xy_val)
:
  ConvertsM F.conversion (do acc + (← xy.1 * xy.2)) state
    (acc_val + xy_val.1 * xy_val.2) True
:= by
  have h_x := FPair.converts_fst h_xy
  have h_y := FPair.converts_snd h_xy
  step mkMul.convertsM h_x h_y as prod
  apply convertsM_of_convertsM (mkAdd.convertsM h_acc h_prod)
  . rfl
  . trivial

lemma convertsM
  {w}
  {state : ClapMState p}
  {a b : FVec p w}
  {a_vals b_vals : Vector (ZMod p) w}
  (h_a : Converts FVec.conversion state a a_vals)
  (h_b : Converts FVec.conversion state b b_vals)
:
  ConvertsM F.conversion (dotProduct a b) state
    ((a_vals.zip b_vals).foldl (fun acc xy ↦ acc + xy.1 * xy.2) 0) True
:= by
  unfold dotProduct

  step mkF.convertsM as acc0

  have h_elems : ∀ i : Fin w,
      Converts FPair.conversion acc0_state (a.zip b)[i] ((a_vals.zip b_vals)[i]) :=
    fun i ↦ FVec.converts_zip h_a h_b i.isLt

  apply convertsM_of_convertsM
    (convertsM_foldlM
      (f_spec := fun (acc : ZMod p) (xy : ZMod p × ZMod p) ↦ acc + xy.1 * xy.2)
      h_elems h_acc0 step_convertsM)
  . rfl
  . trivial

end dotProduct
end dotProduct

end Clap.Lang
