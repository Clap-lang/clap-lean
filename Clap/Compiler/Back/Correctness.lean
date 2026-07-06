import Clap.Compiler.Back.Compilation
import Clap.Compiler.Back.Correctness.IsZero
import Clap.Compiler.Back.Correctness.Num2Bits
import Clap.Compiler.Back.Correctness.FpMul
import Clap.Compiler.Back.Correctness.WF
import Clap.Compiler.Back.Simulation


variable {p : ℕ} {var : Type} [inst : Fact (Nat.Prime p)] [inst' : Fact (p > 2)]

namespace Clap

open Simulation

theorem soundness {c : Circuitₑ p} : circuitWF c → wrBisim c.eval c.toCs.eval := by
  induction c with
  | nil =>
    intros h
    simp [Circuit.eval,Circuit.toCs]
    constructor
  | lam k ih =>
    intros h
    unfold circuitWF at h
    simp [Circuit.eval,Circuit.toCs]
    constructor
    exact fun x ↦ ih _ (h x)
  | eq0 e c ih =>
    intros h
    simp [Circuit.eval,Cs.eval,Circuit.toCs]
    split
    apply ih h
    constructor
  | share e c ih =>
    intros h
    simp [Circuit.eval,Cs.eval,Circuit.toCs]
    apply wrBisim.right
    intro x
    simp [Exp.eval]
    split
    have hmy : x = Exp.eval e := by grind
    rw [<-hmy]
    apply ih _ (h x)
    constructor
  | isZero e c ih =>
    apply IsZero.isZero_soundness ih
  | num2bits w e c ih =>
    apply Num2Bits.num2bits_soundness ih
  | fpmul w k a b p' c ih =>
    apply FpMul.fpmul_soundness ih


theorem soundness' {c : Circuit' p} :
  circuitWF (c (ZMod p)) → wrBisim (Circuit.eval' c) (eval' (toCs' c)) := by
  apply soundness

def completeness [Fact (Nat.Prime p)] {c : Circuitₑ p} :
  circuitWF c → c.eval = (wrap c.toWg c.toCs).eval := by
  induction c with
  | nil =>
    aesop (add simp [Circuit.eval,Circuit.toCs,Circuit.toWg,wrap])
  | lam k h =>
    aesop (add simp [Circuit.eval,Cs.eval,Circuit.toCs,Circuit.toWg,wrap])
  | eq0 e c h =>
    aesop (add simp [Circuit.eval,Cs.eval,Circuit.toCs,Circuit.toWg,wrap])
  | share e c h =>
    aesop (add simp [Exp.eval,Circuit.eval,Cs.eval,Circuit.toCs,Circuit.toWg,wrap])
  | isZero e c ih =>
    apply IsZero.isZero_completeness ih
  | num2bits w e c ih =>
    apply Clap.Num2Bits.num2bits_completeness ih
  | fpmul w k a b p' c ih =>
    apply FpMul.fpmul_completeness ih

end Clap
