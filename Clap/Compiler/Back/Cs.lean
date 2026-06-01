import Clap.Compiler.Back.Circuit
import Clap.Compiler.Back.Simulation

/-
  This file introduces our "target language" `Cs` for Constraint System.
  Cs is a strict subset of Circuit and so is its evaluation function.
  A Circuit can be compiled to a Cs using `to_cs`, which introduces
  extra inputs (`lam`) to receive all the values that could be
  computed by the Circuit but can only be checked by a Cs.
-/

namespace Clap

-- TODO we could remove this type and add an index to Circuit, which would save us from defining again the semantics of Cs
inductive Cs (p : ℕ) (var : Type) : Type where
  | nil
  | eq0 (_ : Exp p var) (_ : Cs p var)
  | lam (_ : var -> Cs p var)

abbrev Csₑ (p : ℕ) : Type := Cs p (ZMod p)
def Cs' (p : ℕ) : Type _ := (var : Type) -> Cs p var

variable {p : ℕ} {var : Type} [inst : Fact (Nat.Prime p)] [inst' : Fact (p > 2)]

open Clap.Circuit in
def Cs.repr [Repr var] [Clap.Circuit.Index var]
  (l : ℕ) (c : Cs p var) : Std.Format :=
  letI go (l : ℕ) (k : var → Cs p var) := repr (l+1) (k (index l))
  match c with
  | .nil => "nil"
  | .lam k => s!"λ{l} {go l k}"
  | .eq0 e c => s!"eq0 {_root_.repr e} {repr l c}"

instance [Repr var] [Clap.Circuit.Index var] : Repr (Cs p var) where
  reprPrec c _ := c.repr 0

instance [Repr var] [Clap.Circuit.Index var] : ToString (Cs p var) :=
  ⟨Std.Format.pretty ∘ Cs.repr 0⟩

def Cs.eval (c : Cs p (ZMod p)) : denotation (ZMod p) :=
  match c with
  | .nil => .u
  | .lam k => .l fun x => (k x).eval
  | .eq0 e c => if e.eval = 0 then c.eval else .n

def eval' (cs:Cs' p) : denotation (ZMod p) := (cs (ZMod p)).eval

@[reducible]
def Cs.curry (n : ℕ) (k : Vector var n -> Cs p var) : Cs p var :=
  match n with
  | 0 => k #v[]
  | n+1 => .lam (fun (x : var) => Cs.curry n (fun l => k ⟨⟨x :: l.toList⟩, by simp⟩ ))

omit inst in
omit inst' in
lemma rw_bisim_uncurry : ∀ (w : ℕ) (d : denotation (ZMod p)) (k : Vector (ZMod p) w -> Cs p (ZMod p)),
 (∀ args : Vector (ZMod p) w, Simulation.wrBisim d (k args).eval) ->
 Simulation.wrBisim d (Cs.curry _ k).eval := by
  intro w
  induction w
  case _ =>
    intros d k h
    simp [Cs.curry]
    apply h
  case _ ih =>
    intros d k h
    simp [Cs.curry]
    constructor
    intro x
    apply ih
    intro args
    apply h

end Clap
