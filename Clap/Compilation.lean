import Mathlib.FieldTheory.Finite.Basic -- field operations

import Clap.Circuit
import Clap.Simulation

/-
  This file introduces our "target language" `Cs` for Constraint System.
  Cs is a strict subset of Circuit and so is its evaluation function.
  A Circuit can be compiled to a Cs using `to_cs`, which introduces
  extra inputs (`lam`) to receive all the values that could be
  computed by the Circuit but can only be checked by a Cs.

  Soundness.
  In order to show that a Cs is not more accepting that its original
  Circuit, i.e. that it won't accept more inputs, we show that there
  is a right-weak bisimulation `rw_bisim` between them.
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

-- we could remove this type and add an index to Circuit, which would save us from defining again the semantics of Cs
inductive Cs (var:Type) : Type where
  | nil : Cs var
  | eq0 : Exp var -> Cs var -> Cs var
  | lam : (var -> Cs var) -> Cs var

def Cs' : Type _ := (var:Type) -> Cs var

def Cs.eval (c:Cs F) : denotation :=
  match c with
  | .nil => .u
  | .lam k => .l (fun x => eval (k x))
  | .eq0 e c =>
    if Exp.eval e = 0 then eval c else .n

def Cs.eval' (c:Cs') : denotation := eval (c F)

def to_cs {var:Type} (c:Circuit var) : Cs var :=
  match c with
  | .nil => .nil
  | .eq0 e c => .eq0 e (to_cs c)
  | .lam k => .lam (fun x => to_cs (k x))
  --
  | .share e k =>
      .lam (fun o =>
        .eq0 (e - .v o) (to_cs (k o)))
  | .is_zero e k =>
    .lam (fun inv =>
      .lam (fun o =>
        .eq0 (.c 1 - .v inv * e - .v o)
          (.eq0 (.v o * e) (to_cs (k o)))))
     -- e=0          o=1
     -- e≠0 inv=e^-1 o=0

def to_cs' (c:Circuit') : Cs' := fun var => to_cs (c var)

-- a list with continuations
inductive Wg : Type where
  | nil : Wg
  | cons : F -> Wg -> Wg
  | input : (F -> Wg) -> Wg

def to_wg (c:Circuit F) : Wg :=
  match c with
  | .nil => Wg.nil
  | .eq0 _ c => to_wg c
  | .lam k => Wg.input (fun i => to_wg (k i))
  | .share e k =>
    let e := Exp.eval e
    .cons e (to_wg (k e))
  | .is_zero e k =>
    let e := Exp.eval e
    let inv : F := e⁻¹
    let o : F := if e = 0 then 1 else 0
    .cons inv (.cons o (to_wg (k o)))

def to_wg' (c:Circuit') : Wg := to_wg (c F)

def wrap (wg:Wg) (cs:Cs F) : Cs F :=
  match wg,cs with
  | .nil,.nil => .nil
  | wg,.eq0 e cs => .eq0 e (wrap wg cs)
  | Wg.input kwg,.lam k => .lam (fun x => wrap (kwg x) (k x))
  | .cons x wg,.lam k => wrap (wg:Wg) (k x)
  | _,_ => .eq0 (.c 1) .nil -- needed because we don't have typed wg and cs

open Simulation

theorem soundness : ∀ (c:Circuit F),
  rw_bisim (Circuit.eval c) (Cs.eval (to_cs c)) := by
  intro c
  induction c with
  | nil =>
    simp [Circuit.eval,to_cs]
    constructor
  | lam k h =>
    simp [Circuit.eval,to_cs]
    constructor
    exact h
  | eq0 e c h =>
    simp [Circuit.eval,Cs.eval,to_cs]
    split
    apply h
    constructor
  | share e c h =>
    simp [Circuit.eval,Cs.eval,to_cs]
    apply rw_bisim.right
    intro x
    simp [Exp.eval]
    split
    have hmy : x = Exp.eval e := by grind
    rw [<-hmy]
    apply h
    constructor
  | is_zero e c h =>
    apply rw_bisim.right
    intro inv
    apply rw_bisim.right
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
      split
      case isTrue hsub =>
        split
        case isTrue hmul =>
          simp [*] at *
          rw [hmul]
          apply h
        case isFalse hmul => constructor
      case isFalse hsub => constructor

theorem soundness' : ∀ (c:Circuit'),
  rw_bisim (Circuit.eval' c) (Cs.eval' (to_cs' c)) := by
  intro c
  apply soundness

def completeness : ∀ (c:Circuit F),
  Circuit.eval c = Cs.eval (wrap (to_wg c) (to_cs c)) := by
  intro c
  induction c with
  | nil =>
    simp [Circuit.eval,to_cs,to_wg,wrap]
    constructor
  | lam k h =>
    simp [Circuit.eval,Cs.eval,to_cs,to_wg,wrap]
    funext
    apply h
  | eq0 e c h =>
    simp [Circuit.eval,Cs.eval,to_cs,to_wg,wrap]
    split
    exact h
    constructor
  | share e c h =>
    simp [Exp.eval,Circuit.eval,Cs.eval,to_cs,to_wg,wrap]
    apply h
  | is_zero e c h =>
    simp [Exp.eval,Circuit.eval,Cs.eval,to_cs,to_wg,wrap]
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
