import Clap.Circuit

import Clap.eDSLState.Varstore
import Clap.eDSLState.Wheels

namespace Clap

abbrev FixedExp (p : ℕ) := Clap.Exp p ℕ

def FixedExp.size {p : ℕ} (exp : FixedExp p) : ℕ :=
  match exp with
  | .v _ => 1
  | .c _ => 1
  | .add l r => size l + size r + 1
  | .mul l r => size l + size r + 1
  | .sub l r => size l + size r + 1

abbrev FixedCircuit (p : ℕ) := Clap.Circuit p ℕ

def FixedExp.eval {p : ℕ} (varStore : VarStore p) (x : FixedExp p) : Option (ZMod p) :=
  match x with
  | .c x => .some x
  | .v x => varStore[x]?
  | .add l r => do (←eval varStore l) + (←eval varStore r)
  | .sub l r => do (←eval varStore l) - (←eval varStore r)
  | .mul l r => do (←eval varStore l) * (←eval varStore r)

def FixedExp.eval' {p : ℕ} (varStore : VarStore p) (x : FixedExp p) : Option (ZMod p) :=
  (go varStore x).run' ∅
  where
    go (varStore : VarStore p)
       (x : FixedExp p) : StateM (Std.HashMap (FixedExp p) (Option (ZMod p))) (Option (ZMod p)) := do
    let cache ← get
    if h : cache.contains x
    then 
      return cache[x]
    else
      match x with
      | .c val =>
        let res := val
        modify fun σ ↦ σ.insert x res
        return res
      | .v x =>
        let res := varStore[x]?
        modify fun σ ↦ σ.insert x res 
        return res
      | .add l r => do
        let l' ← go varStore l
        modify fun σ ↦ σ.insert l l'
        let r' ← go varStore r
        modify fun σ ↦ σ.insert r r'
        return (·+·) <$> l' <*> r'
      | .sub l r => do
        let l' ← go varStore l
        modify fun σ ↦ σ.insert l l'
        let r' ← go varStore r
        modify fun σ ↦ σ.insert r r'
        return (·-·) <$> l' <*> r'
      | .mul l r => do
        let l' ← go varStore l
        modify fun σ ↦ σ.insert l l'
        let r' ← go varStore r
        modify fun σ ↦ σ.insert r r'
        return (·*·) <$> l' <*> r'


/-
10/10 the tail rec version is slower
-/

-- inductive ExpPart (p : ℕ) where
--   | addL (_ : FixedExp p)
--   | addR (_ : ZMod p)
--   | subL (_ : FixedExp p)
--   | subR (_ : ZMod p)
--   | mulL (_ : FixedExp p)
--   | mulR (_ : ZMod p)

-- partial def FixedExp.eval' {p : ℕ}
--     (varStore : VarStore p) (e : FixedExp p) : Option (ZMod p) :=
--   go [e] [] []
--   where go (todo : List (FixedExp p)) (left : List (ExpPart p)) (right : List (ZMod p)) : Option (ZMod p) :=
--     match todo with
--     | todo :: rest =>
--       match todo with
--       | .c x => go rest left (x :: right)
--       | .v x => match varStore[x]? with
--                 | .none => .none
--                 | .some v => go rest left (v :: right)
--       | .add l r => go (l :: rest) (.addL r :: left) right
--       | .sub l r => go (l :: rest) (.subL r :: left) right
--       | .mul l r => go (l :: rest) (.mulL r :: left) right
--     | [] => match left with
--       | [] =>
--           match right with
--           | [v] => .some v
--           | _ => .none
--       | .addL r :: ks =>
--           match right with
--           | lv :: vs => go (r :: []) (.addR lv :: ks) vs
--           | _ => .none
--       | .subL r :: ks =>
--           match right with
--           | lv :: vs => go (r :: []) (.subR lv :: ks) vs
--           | _ => .none
--       | .mulL r :: ks =>
--           match right with
--           | lv :: vs => go (r :: []) (.mulR lv :: ks) vs
--           | _ => .none
--       | .addR lv :: ks =>
--           match right with
--           | rv :: vs => go [] ks ((lv + rv) :: vs)
--           | _ => .none
--       | .subR lv :: ks =>
--           match right with
--           | rv :: vs => go [] ks ((lv - rv) :: vs)
--           | _ => .none
--       | .mulR lv :: ks =>
--           match right with
--           | rv :: vs => go [] ks ((lv * rv) :: vs)
--           | _ => none

-- @[csimp]
-- lemma optim : @FixedExp.eval' = @FixedExp.eval := by sorry

def VarStore.ofArray {p : ℕ} (elem : Array (ℕ × ZMod p)) : VarStore p :=
  Std.ExtTreeMap.ofArray elem (cmp := compare)

def mkBigExpr : FixedExp 57 :=
  go 1_000_00 (.c 4)
  where
    go (n : ℕ) (res : FixedExp 57) : FixedExp 57 :=
      match n with
      | 0 => res
      | n + 1 => go n (res.add (.v 0))

def sigma {p} (x : FixedExp p) : FixedExp p :=
  let x2 := x * x
  let x4 := x2 * x2
  x4 * x

def mkSigmaExpr (n : ℕ) : FixedExp 21888242871839275222246405745257275088696311157297823662689037894645226208583 :=
  Array.range n |>.foldl (init := .c 2) fun acc _ ↦ sigma acc

set_option profiler true
#eval FixedExp.eval (.ofArray #[(0, 4), (1, 2)]) (.c (4 : ZMod 57) + (.v 1) * (.v 0))
#eval FixedExp.eval (.ofArray #[(0, 2), (1, 2)]) mkBigExpr
#eval FixedExp.eval (.ofArray #[(0, 2), (1, 2)]) (mkSigmaExpr 5)
#eval FixedExp.eval' (.ofArray #[(0, 2), (1, 2)]) (mkSigmaExpr 5)
-- #eval FixedExp.eval' (.ofArray #[(0, 2), (1, 2)]) mkBigExpr
-- #eval FixedExp.eval' (.ofArray #[(0, 2), (1, 2)]) mkBigExpr
-- #eval FixedExp.eval' (.ofArray #[(0, 2), (1, 2)]) mkBigExpr
-- #eval FixedExp.eval (.ofArray #[(0, 2), (1, 2)]) mkBigExpr


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
