import Clap.Circuit

import Clap.eDSLState.Wheels

namespace Clap

abbrev FixedExp (p : ℕ) := Clap.Exp p ℕ
abbrev FixedCircuit (p : ℕ) := Clap.Circuit p ℕ

def FixedExp.eval {p : ℕ} (varStore : ℕ → Option (ZMod p)) (x : FixedExp p) : Option (ZMod p) :=
  match x with
  | .c x => .some x
  | .v x => varStore x
  | .add l r => do (←eval varStore l) + (←eval varStore r)
  | .sub l r => do (←eval varStore l) - (←eval varStore r)
  | .mul l r => do (←eval varStore l) * (←eval varStore r)

@[simp, grind =]
lemma eval_const
  {p : ℕ}
  {k : ZMod p}
  {varStore : ℕ → Option (ZMod p)}
:
  FixedExp.eval varStore (Exp.c k) = .some k
:= by
  simp [FixedExp.eval]

@[simp, grind =]
lemma FixedExp.eval_add
  {p : ℕ}
  {varStore : ℕ → Option (ZMod p)}
  {a b : FixedExp p}
:
  FixedExp.eval varStore (a + b) =
  FixedExp.eval varStore (Exp.add a b)
:= by
  simp [HAdd.hAdd, Add.add]

@[simp, grind =]
lemma FixedExp.eval_sub
  {p : ℕ}
  {varStore : ℕ → Option (ZMod p)}
  {a b : FixedExp p}
:
  FixedExp.eval varStore (a - b) =
  FixedExp.eval varStore (Exp.sub a b)
:= by
  simp [HSub.hSub, Sub.sub]

@[simp, grind =]
lemma FixedExp.eval_mul
  {p : ℕ}
  {varStore : ℕ → Option (ZMod p)}
  {a b : FixedExp p}
:
  FixedExp.eval varStore (a * b) =
  FixedExp.eval varStore (Exp.mul a b)
:= by
  simp [HMul.hMul, Mul.mul]

end Clap
