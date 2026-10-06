import Clap.Lang.Core.Combinators.foldlM
import Clap.Lang.Core.FUnit.assert_eq
namespace Clap.Lang.FVec

variable {p : ℕ}

section assert_eq

/-- Assert two vectors of field elements are equal, position by position. This is the same circuit
as `FArray.assert_eq`; only the conversion cited in the specification differs. -/
def assert_eq {w : ℕ} (a b : FVec p w) : ClapM p Unit :=
  (a.zip b).foldlM (fun _ xy ↦ _root_.Clap.Lang.assert_eq xy.1 xy.2) ()

namespace assert_eq

private lemma step_convertsM
  [p.AtLeastTwo]
  {state : ClapMState p}
  {acc : Unit}
  {acc_val : Unit}
  {xy : F p × F p}
  {xy_val : ZMod p × ZMod p}
  (_h_acc : Converts FUnit.conversion state acc acc_val)
  (h_xy : Converts FPair.conversion state xy xy_val)
:
  ConvertsM FUnit.conversion (_root_.Clap.Lang.assert_eq xy.1 xy.2) state ()
    (xy_val.1 = xy_val.2)
:= _root_.Clap.Lang.assert_eq.convertsM (FPair.converts_fst h_xy) (FPair.converts_snd h_xy)

lemma convertsM
  [p.AtLeastTwo]
  {w : ℕ}
  {state : ClapMState p}
  {a b : FVec p w}
  {a_vals b_vals : Vector (ZMod p) w}
  (h_a : Converts FVec.conversion state a a_vals)
  (h_b : Converts FVec.conversion state b b_vals)
:
  ConvertsM FUnit.conversion (assert_eq a b) state () (a_vals = b_vals)
:= by
  unfold assert_eq
  apply convertsM_of_convertsM
    (convertsM_foldlM_constraints
      (f_spec := fun (_ : Unit) (_ : ZMod p × ZMod p) ↦ ())
      (step_constraints := fun (xy : ZMod p × ZMod p) ↦ xy.1 = xy.2)
      (init_val := ())
      (fun i ↦ FVec.converts_zip h_a h_b i.isLt) FUnit.converts step_convertsM)
  . rfl
  . constructor
    . intro h
      ext i h_i
      simpa using h ⟨i, h_i⟩
    . rintro rfl i
      simp

end assert_eq
end assert_eq

end Clap.Lang.FVec
