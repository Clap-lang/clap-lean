import Mathlib.FieldTheory.Finite.Basic -- field operations

import Clap.Wheels
import Clap.Circuit
import Clap.Simulation

namespace Clap

/-
  This file introduces our "target language" `Cs` for Constraint System.
  Cs is a strict subset of Circuit and so is its evaluation function.
  A Circuit can be compiled to a Cs using `to_cs`, which introduces
  extra inputs (`lam`) to receive all the values that could be
  computed by the Circuit but can only be checked by a Cs.

  Soundness.
  In order to show that a Cs is not more accepting that its original
  Circuit, i.e. that it won't accept more inputs, we show that there
  is a right-weak bisimulation `wrBisim` between them.
  In particular, while a Circuit evaluates to any of the `denotation`
  values, a Cs might be stuck waiting for an extra input. Therefore
  the Cs is allowed to receive any value as extra input while the
  Circuit "waits" for the Cs to catch up, so long as they end up two
  denotations that bisimulate as well.

  A circuit can also be compiled to a Wg for Witness Generator using
  the `to_wg` function. A Wg computes the values needed by a Cs to
  check any computation that was done by the Circuit.

  Completeness
  A Cs and Wg can be composed using `wrap` to obtain a new Cs that
  does not require extra inputs compared to its original Circuit, as
  all extra inputs are immediately filled by the Wg.
  In order to show that Wg and Cs work correctly together, we show
  that, once wrapped, they are equivalent to the original Circuit.
-/


-- TODO we could remove this type and add an index to Circuit, which would save us from defining again the semantics of Cs
inductive Cs (p : ℕ) (var : Type) : Type where
  | nil
  | eq0 (_ : Exp p var) (_ : Cs p var)
  | lam (_ : var -> Cs p var)

variable {p : ℕ} {var : Type} [Fact (Nat.Prime p)]

def Cs.eval (c : Cs p (ZMod p)) : denotation (ZMod p) :=
  match c with
  | .nil => .u
  | .lam k => .l fun x => (k x).eval
  | .eq0 e c => if e.eval = 0 then c.eval else .n

def Cs' (p:Nat) : Type _ := (var:Type) -> Cs p var

def eval' (cs:Cs' p) : denotation (ZMod p) := (cs (ZMod p)).eval

@[reducible]
def Cs.curry (n:ℕ) (k:Vector var n -> Cs p var) : Cs p var :=
  match n with
  | 0 => k #v[]
  | n+1 => .lam (fun x:var => Cs.curry n (fun l => k (l.push x) ))

def assert_bit_e (rest: Cs p var) (b:var) : Cs p var :=
  .eq0 (.v b * (.c 1 - .v b)) rest

def assert_bits_e {w:ℕ} (bs:Vector var w) (rest: Cs p var) : Cs p var :=
  Vector.foldl assert_bit_e rest bs

def bits2num_e {w} (bits:Vector var w) : Exp p var :=
  Vector.foldl (fun acc b => .v b + .c 2 * acc) (.c 0) bits

def Circuit.toCs (c : Circuit p var) : Cs p var :=
  match c with
  | .nil =>
      .nil
  | .eq0 e c =>
      .eq0 e c.toCs
  | .lam k =>
      .lam fun x => (k x).toCs
  | .share e k =>
      .lam fun o => .eq0 (e - .v o) (k o).toCs
  | .is_zero e k =>
    .lam fun inv =>
      .lam fun o =>
        .eq0 (.c 1 - .v inv * e - .v o)
          (.eq0 (.v o * e) (k o).toCs)
     -- e=0          o=1
     -- e≠0 inv=e^-1 o=0
  | .num2bits w e c =>
    Cs.curry w (fun bits =>
      letI rest := (c bits.toList).toCs
      letI rest := Cs.eq0 (bits2num_e bits - e) rest
      assert_bits_e bits rest)

def toCs' (c : Circuit' p) : Cs' p := fun var => (c var).toCs

inductive Wg (p : ℕ) : Type where
  | nil
  | cons (_ : ZMod p) (_ : Wg p)
  | input (_ : ZMod p → Wg p)

def Circuit.toWg (c : Circuitₑ p) : Wg p :=
  match c with
  | .nil => Wg.nil
  | .eq0 _ c => c.toWg
  | .lam k => Wg.input fun i => (k i).toWg
  | .share e k =>
    letI e := e.eval
    .cons e (k e).toWg
  | .is_zero e k =>
    letI e := e.eval
    let o : ZMod p := if e = 0 then 1 else 0
    .cons e⁻¹ (.cons o (k o).toWg)
  | .num2bits w e c =>
    letI bits := num2bits_pure w (Exp.eval e)
    List.foldl (fun acc b => .cons b acc) (c bits).toWg bits

def wrap (wg : Wg p) (cs : Cs p (ZMod p)) : Cs p (ZMod p) :=
  match wg,cs with
  |         .nil , .nil      => .nil
  |           wg , .eq0 e cs => .eq0 e (wrap wg cs)
  | Wg.input kwg , .lam k    => .lam fun x => wrap (kwg x) (k x)
  |   .cons x wg , .lam k    => wrap (wg : Wg p) (k x)
  |            _ , _         => .eq0 (.c 1) .nil -- needed because we don't have typed wg and cs

open Simulation

theorem soundness {c : Circuitₑ p} : wrBisim c.eval c.toCs.eval := by
  induction c with
  | nil =>
    simp [Circuit.eval,Circuit.toCs]
    constructor
  | lam k h =>
    simp [Circuit.eval,Circuit.toCs]
    constructor
    exact h
  | eq0 e c h =>
    simp [Circuit.eval,Cs.eval,Circuit.toCs]
    split
    apply h
    constructor
  | share e c h =>
    simp [Circuit.eval,Cs.eval,Circuit.toCs]
    apply wrBisim.right
    intro x
    simp [Exp.eval]
    split
    have hmy : x = Exp.eval e := by grind
    rw [<-hmy]
    apply h
    constructor
  | is_zero e c h =>
    apply wrBisim.right
    intro inv
    apply wrBisim.right
    intro o
    simp [Exp.eval,Circuit.eval,Cs.eval]
    split
    case is_zero.h.h.isTrue he0 =>
      split
      case isTrue hsub =>
        split
        case isTrue hmul =>
          simp [*] at *
          have hmy : o=1 := by grind
          rw [hmy]
          apply h
        case isFalse hmul => constructor
      case isFalse hsub => constructor
    case is_zero.h.h.isFalse he0 =>
      -- aesop
      split
      case isTrue hsub =>
        split
        case isTrue hmul =>
          aesop
        case isFalse hmul => constructor
      case isFalse hsub => constructor
  | num2bits w e c h =>
      sorry

theorem soundness' {c:Circuit' p} :
  wrBisim (Circuit.eval' c) (eval' (toCs' c)) := by
  apply soundness


def completeness [Fact (Nat.Prime p)] {c : Circuitₑ p} :
  c.eval = (wrap c.toWg c.toCs).eval := by
  induction c with
  | nil =>
    simp [Circuit.eval,Circuit.toCs,Circuit.toWg,wrap]
    constructor
  | lam k h =>
    simp [Circuit.eval,Cs.eval,Circuit.toCs,Circuit.toWg,wrap]
    funext
    apply h
  | eq0 e c h =>
    simp [Circuit.eval,Cs.eval,Circuit.toCs,Circuit.toWg,wrap]
    split
    exact h
    constructor
  | share e c h =>
    simp [Exp.eval,Circuit.eval,Cs.eval,Circuit.toCs,Circuit.toWg,wrap]
    apply h
  | is_zero e c h =>
    simp [Exp.eval,Circuit.eval,Cs.eval,Circuit.toCs,Circuit.toWg,wrap]
    split
    case is_zero.isTrue he0 =>
      simp
      split <;> apply h
    case is_zero.isFalse he0 =>
      split
      case isTrue he0' =>
        apply h
      case isFalse he0' =>
        simp [*] at *
  | num2bits e c h =>
    sorry
