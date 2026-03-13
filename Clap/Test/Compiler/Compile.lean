import Clap.Spec
import Clap.Compiler.Basic
import Clap.Test.Wheels
import Lean.Meta.Sym.Simp.SimpM
import Lean.Meta.Tactic.Cbv.Opaque
import Lean.Meta.Tactic.Cbv.ControlFlow
import Lean.Meta.Tactic.Cbv.Util
import Lean.Meta.Tactic.Cbv.TheoremsLookup
import Lean.Meta.Tactic.Cbv.CbvEvalExt
import Lean.Meta.Sym
import Lean.Meta.Tactic.Refl

namespace Clap

namespace Test

namespace Compiler

open Lean Clap Meta Spec Compiler Lang ZMod Core

structure Compile.Point (p : ℕ) where
  x : ZMod p
  y : ZMod p
  z : ZMod p

structure Compile.Point' (p : ℕ) where
  x : ZMod p
  y : ZMod p
  z : ZMod p
  w : ZMod p

def Compile.ex₀ {p : ℕ} [Core p] (point₁ point₂ : Point p) (point₃ : Point' p) : Option Unit := do
  eq0 (point₁.x + point₃.w)
  eq0 (point₂.x + point₁.z)
  accept

/--
info: Compiled Compile.ex₀ into Compile.ex₀_circuit.
---
info: Wg for Compile.ex₀ is Compile.ex₀_wg_wrap.
-/
#guard_msgs(info, whitespace := lax) in
#compile Compile.ex₀ using Primes.babybear

/--
info: def Compile.ex₀_circuit : (var : Type) → Circuit Primes.babybear var :=
fun (var : Type) =>
  Circuit.lam fun (curried0_point₁_circuit : var) =>
    Circuit.lam fun (curried1_point₁_circuit : var) =>
      Circuit.lam fun (curried2_point₁_circuit : var) =>
        Circuit.lam fun (curried0_point₂_circuit : var) =>
          Circuit.lam fun (curried1_point₂_circuit : var) =>
            Circuit.lam fun (curried2_point₂_circuit : var) =>
              Circuit.lam fun (curried0_point₃_circuit : var) =>
                Circuit.lam fun (curried1_point₃_circuit : var) =>
                  Circuit.lam fun (curried2_point₃_circuit : var) =>
                    Circuit.lam fun (curried3_point₃_circuit : var) =>
                      Circuit.eq0 ((Exp.v curried0_point₁_circuit).add (Exp.v curried3_point₃_circuit))
                        ((fun (x : PUnit.{1}) =>
                            Circuit.eq0 ((Exp.v curried0_point₂_circuit).add (Exp.v curried2_point₁_circuit))
                              ((fun (x : PUnit.{1}) => Circuit.nil) ()))
                          ())
-/
#guard_msgs(info, whitespace := lax) in
set_option pp.funBinderTypes true in
#print Compile.ex₀_circuit

/--
info: def Compile.ex₀_wg_wrap : Wg Primes.babybear →
  Compile.Point Primes.babybear →
    Compile.Point Primes.babybear → Compile.Point' Primes.babybear → Array (ZMod Primes.babybear) :=
fun (wg : Wg Primes.babybear) (point₁ point₂ : Compile.Point Primes.babybear)
    (point₃ : Compile.Point' Primes.babybear) =>
  wg.run
    { toList := [point₁.x, point₁.y, point₁.z, point₂.x, point₂.y, point₂.z, point₃.x, point₃.y, point₃.z, point₃.w] }
-/
#guard_msgs(info, whitespace := lax) in
set_option pp.funBinderTypes true in
#print Compile.ex₀_wg_wrap


-- TODO should work with Core
-- def Compile.ex₁ {p : ℕ} [Core p] (x : Core.F p) : Option Unit := do
--   let x := Core.share x
--   let y := Core.const (1:ZMod p)
--   let z := Core.isZero y
--   let k <- Core.num2bits 2 (x + Core.convert z)
--   -- TODO expand k
--   Core.eq0 (Core.convert k[0]!)
--   Core.accept p

open Spec.Compiler

def Compile.ex₁ {p : ℕ} (x : ZMod p) : Option Unit := do
  let x := share x
  let y := (1:ZMod p)
  let z := is_zero y
  let _ <- num2bits 2 (x + z)
--  eq0 k[0]!
  accept

open Clap.Lang.ZMod

/--
info: Compiled Compile.ex₁ into Compile.ex₁_circuit.
---
info: Wg for Compile.ex₁ is Compile.ex₁_wg_wrap.
-/
#guard_msgs(info, whitespace := lax) in
#compile Compile.ex₁ using Primes.babybear

/--
info: def Compile.ex₁_circuit : (var : Type) → Circuit Primes.babybear var :=
fun (var : Type) =>
  Circuit.lam fun (x : var) =>
    Circuit.share (Exp.v x) fun (x : var) =>
      Circuit.is_zero (Exp.c 1) fun (z : var) =>
        Circuit.num2bits 2 ((Exp.v x).add (Exp.v z)) fun (vars : List var) => Circuit.nil
-/
#guard_msgs(info, whitespace := lax) in
set_option pp.funBinderTypes true in
#print Compile.ex₁_circuit


def Compile.adder {p : ℕ} [Fact (Nat.Prime p)] [Core p] (x y : F p) : Option (F p) := do
  eq0 x
  -- eq0 y
  let z := x + y
  eq0 z
  return z

def Compile.test {p : ℕ} [Fact (Nat.Prime p)] [Core p] (x y z : F p) : Option Unit := do
  let a ← adder x y
  let b ← adder y z
  eq0 (a - b)
  accept p

/--
info: Compiled Compile.test into Compile.test_circuit.
---
info: Wg for Compile.test is Compile.test_wg_wrap.
-/
#guard_msgs in
#compile Compile.test using Primes.babybear

attribute [local cbv_opaque] Clap.Lang.Core.eq0 Clap.Lang.Core.accept Bind.bind pure Clap.Spec.Compiler.eq0 Clap.Spec.Compiler.accept --Option.bind
attribute [local cbv_eval] pure_bind bind_pure bind_assoc Option.bind_some Option.some_bind --Option.bind_eq_bind

open Lean Meta Tactic Cbv in
def cbv (e : Expr) : MetaM Expr := do
  match ←cbvEntry e with
  | .rfl _ => return e
  | .step e _ _ => return e

def opaques := [``Eq, ``Core.eq0, ``Bind.bind, ``pure, ``HAdd.hAdd, ``HSub.hSub, ``HMul.hMul, ``OfNat.ofNat, ``Option.bind, ``Option.some, ``Clap.Spec.Compiler.eq0, ``Clap.Spec.Compiler.accept]

def isDefEqToConst (e : Expr) (name : Name) : MetaM Bool := do
  let c ← mkConstWithFreshMVarLevels name
  isDefEq e c


partial def applyCbv (e : Expr) : MetaM TransformStep := do
  -- logInfo m!"Visit:\n{e}"
  match e with
  | .app fn _ =>
    logInfo m!"fn: {fn}"
    if <- opaques.anyM fun name => do isDefEqToConst fn name
    then logInfo m!"App.Skipped: {fn}"
         return .continue
    else logInfo m!"App.CBV: {e}"
         return .done (←cbv e)
  | .letE name ty val body _ =>
      logInfo m!"Let.CBV {e}"
      let e ← withLetDecl name ty val fun fvar => do
        let body' ← Meta.transform (body.instantiate1 fvar) applyCbv
        mkLetFVars #[fvar] body'
--      let e ← cbv e
      logInfo m!"Let.CBV.result {e}"
      return .done e
  | .fvar fvarId =>
    -- if !(←inferType e).isApp then return .continue
    -- if ←(← inferType e).getAppFn.isAppOfUptoDefEq (.const ``ZMod [])
    -- then return .continue
    -- else
    return .done e
  | .lam name ty body bi =>
      logInfo m!"LAM: {e}"
      let e <- withLocalDecl name bi ty fun fvar => do
        let body' ← Meta.transform (body.instantiate1 fvar) applyCbv
        mkLambdaFVars #[fvar] body'
      return .done e
  | .proj typeName idx struct => return .continue
  | .forallE binderName binderType body binderInfo
  | .mvar mvarId
  | .const declName us
  | .lit _
  | .bvar deBruijnIndex
  | .sort u
  | .mdata data expr =>
    logInfo m!"rest {e}"
    return .done e

open Lean Meta Tactic Cbv in
def cbvAny (e : Expr) : MetaM Expr := do
  Meta.transform e (pre := applyCbv)

open MVarId in
def _root_.Lean.MVarId.cbvNext (goal : MVarId) : MetaM MVarId :=
  goal.transformTarget (f := cbvAny)

open Elab Tactic in
elab "cbv_next" : tactic => do
  liftMetaTactic' MVarId.cbvNext

-- set_option pp.notation false in
def produceEq0 {p} [Core p] (l : List (F p)) (h : l ≠ []) : Option Unit :=
  match l with
  | [hd] => do
    Core.eq0 hd
  | x₁ :: x₂ :: tl => do
    Core.eq0 x₁
    produceEq0 (x₂ :: tl) (by simp)

def Reduce.ex₀ {p} [Core p] (x y : F p) : Option Unit := do
  produceEq0 [x, x, y] (by simp)
  accept
/-
example {x y : ZMod Primes.babybear} : Reduce.ex₀ (p := Primes.babybear) x y = sorry := by
  cbv_next
  cbv_next
  cbv_next
  repeat first | rw [bind_assoc] | rw [bind_pure] | rw [pure_bind]

#check DSimp.Config

set_option pp.fieldNotation false in
--set_option pp.notation false in
example {x y z : ZMod Primes.babybear} : Compile.test (p := Primes.babybear) x y z = sorry := by

  -- -- works perfectly
  -- unfold Compile.test Compile.adder
  -- dsimp only
  -- repeat first | rw [bind_assoc] | rw [bind_pure] | rw [pure_bind]

  cbv_next
  repeat first | rw [bind_assoc] | rw [bind_pure] | rw [pure_bind]
  cbv_next
  repeat first | rw [bind_assoc] | rw [bind_pure] | rw [pure_bind]
  cbv_next
  repeat first | rw [bind_assoc] | rw [bind_pure] | rw [pure_bind]


--  dsimp -zeta -eta -beta -etaStruct -iota -proj only
-/
end Compiler

end Test

end Clap
