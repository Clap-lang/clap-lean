import Clap.Circuit

import Clap.eDSLState.Varstore
import Clap.eDSLState.Wheels

namespace Clap

abbrev FixedExp (p : ℕ) := Clap.Exp p ℕ
abbrev FixedCircuit (p : ℕ) := Clap.Circuit p ℕ

def FixedExp.eval {p : ℕ} (varStore : VarStore p) (x : FixedExp p) : Option (ZMod p) :=
  match x with
  | .c x => .some x
  | .v x => varStore[x]?
  | .add l r => do (←eval varStore l) + (←eval varStore r)
  | .sub l r => do (←eval varStore l) - (←eval varStore r)
  | .mul l r => do (←eval varStore l) * (←eval varStore r)

notation "[" varStore "|" x "]" => FixedExp.eval varStore x

/--
NB:
  This is a poor man's monad-style thing that doesn't introduce abstraction layers.

  Another option is something that says `x =ΓvarStore y` but that would be too much clutter
  unless we use the symbol `Γ` consistently instead of `varStore`.
-/
notation "[" varStore "|" x " =Γ " y "]" => [varStore|x] = [varStore|y]

instance {p} : Membership (FixedExp p) (VarStore p) := ⟨fun Γ x ↦ [Γ|x].isSome⟩

namespace FixedExp

@[simp, grind =]
lemma eval_c
  {p : ℕ}
  {k : ZMod p}
  {varStore : VarStore p}
:
  [varStore|Exp.c k] = .some k
:= by
  simp [FixedExp.eval]

@[simp, grind .]
lemma eval_ofNat {p n : ℕ} {varStore : VarStore p} :
  [varStore|no_index (OfNat.ofNat n)] = .some n := by
  simp [FixedExp.eval]

@[simp, grind =]
lemma eval_v
  {p : ℕ}
  {varIdx : ℕ}
  {varStore : VarStore p}
:
  [varStore|Exp.v varIdx] = varStore[varIdx]?
:= by
  simp [FixedExp.eval]

@[simp, grind =]
lemma add_def
  {p : ℕ}
  {a b : FixedExp p}
:
  a + b =
  Exp.add a b
:= by
  simp [HAdd.hAdd, Add.add]

-- @[simp, grind =]
@[grind =]
lemma sub_def
  {p : ℕ}
  {a b : FixedExp p}
:
  a - b =
  Exp.sub a b
:= by
  simp [HSub.hSub, Sub.sub]

@[simp, grind =]
lemma mul_def
  {p : ℕ}
  {a b : FixedExp p}
:
  a * b =
  Exp.mul a b
:= by
  simp [HMul.hMul, Mul.mul]

@[simp, grind =]
lemma eval_add
  {p : ℕ}
  {varStore : VarStore p}
  {a b : FixedExp p}
:
  [varStore|Exp.add a b] =
  (do (←eval varStore a) + (←eval varStore b))
:= rfl

@[grind .]
lemma eval_none_add
  {p : ℕ}
  {varStore : VarStore p}
  {a b : FixedExp p}
  (h : [varStore|a] = .none)
:
  [varStore|Exp.add a b] =
  .none
:= by
  simp [FixedExp.eval, h]

@[grind .]
lemma eval_add_none
  {p : ℕ}
  {varStore : VarStore p}
  {a b : FixedExp p}
  (h : [varStore|b] = .none)
:
  [varStore|Exp.add a b] =
  .none
:= by
  simp [FixedExp.eval, h]

@[simp, grind =]
lemma eval_sub
  {p : ℕ}
  {varStore : VarStore p}
  {a b : FixedExp p}
:
  [varStore|Exp.sub a b] =
  (do (←eval varStore a) - (←eval varStore b))
:= rfl

@[grind .]
lemma eval_none_sub
  {p : ℕ}
  {varStore : VarStore p}
  {a b : FixedExp p}
  (h : [varStore|a] = .none)
:
  [varStore|Exp.sub a b] =
  .none
:= by
  simp [FixedExp.eval, h]

@[grind .]
lemma eval_sub_none
  {p : ℕ}
  {varStore : VarStore p}
  {a b : FixedExp p}
  (h : [varStore|b] = .none)
:
  [varStore|Exp.sub a b] =
  .none
:= by
  simp [FixedExp.eval, h]

@[simp, grind =]
lemma eval_mul
  {p : ℕ}
  {varStore : VarStore p}
  {a b : FixedExp p}
:
  [varStore|Exp.mul a b] =
  (do (←eval varStore a) * (←eval varStore b))
:= rfl

@[grind .]
lemma eval_none_mul
  {p : ℕ}
  {varStore : VarStore p}
  {a b : FixedExp p}
  (h : [varStore|a] = .none)
:
  [varStore|Exp.mul a b] =
  .none
:= by
  simp [FixedExp.eval, h]

@[grind .]
lemma eval_mul_none
  {p : ℕ}
  {varStore : VarStore p}
  {a b : FixedExp p}
  (h : [varStore|b] = .none)
:
  [varStore|Exp.mul a b] =
  .none
:= by
  simp [FixedExp.eval, h]

end FixedExp

end Clap
