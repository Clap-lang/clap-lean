import Clap.Compiler.Back.Compilation
import Clap.Compiler.Back.Correctness.WF
import Clap.Compiler.Back.IsZero
import Clap.Compiler.Back.Simulation

open Clap Simulation

namespace Clap.IsZero

variable {p : ℕ} {var : Type} [inst : Fact (Nat.Prime p)] [inst' : Fact (p > 2)]

omit inst' in
lemma isZero_soundness {e : Exp p (ZMod p)} {c : ZMod p → Circuit p (ZMod p)}
    (ih : ∀ (a : ZMod p), circuitWF (c a) → wrBisim (c a).eval (c a).toCs.eval) :
  circuitWF (Circuit.isZero e c) → wrBisim (Circuit.isZero e c).eval (Circuit.isZero e c).toCs.eval := by
  intros h
  apply wrBisim.right
  intro inv
  apply wrBisim.right
  intro o
  simp [Exp.eval,Circuit.eval,Cs.eval]
  split
  case isTrue he0 =>
    split
    case isTrue hsub =>
      split
      case isTrue hmul =>
        simp [*] at *
        have hmy : o=1 := by grind
        rw [hmy]
        apply ih _ (h 1)
      case isFalse hmul => constructor
    case isFalse hsub => constructor
  case isFalse he0 =>
    split
    case isTrue hsub =>
      split
      case isTrue hmul => aesop
      case isFalse hmul => constructor
    case isFalse hsub => constructor

omit inst' in
lemma isZero_completeness {e : Exp p (ZMod p)} {c : ZMod p → Circuit p (ZMod p)}
      (h : ∀ (a : ZMod p), circuitWF (c a) → (c a).eval = (wrap (c a).toWg (c a).toCs).eval) :
    circuitWF (Circuit.isZero e c) →
      (Circuit.isZero e c).eval = (wrap (Circuit.isZero e c).toWg (Circuit.isZero e c).toCs).eval := by
  aesop (add simp [Circuit.eval, Circuit.toCs, Circuit.toWg, IsZero.isZero_circuit, IsZero.isZero_wg, Exp.eval, Cs.eval, wrap])


end Clap.IsZero
