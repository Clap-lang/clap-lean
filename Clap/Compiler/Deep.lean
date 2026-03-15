import Lean

import Clap.Spec

open Lean Meta Elab

namespace Clap

/-
  - make proof
  - deal with j[0]!
  - how big a circuit can we take?
  - telescope
  - transform
  - negative tests
-/

partial def compileExp (p : Expr) (var : Expr) (e : Expr) : MetaM Expr := do
--  dbg_trace s!"compileExp\n{(<-ppExpr e)}"
  if let (``OfNat.ofNat,_) := e.getAppFnArgs then
    mkAppOptM ``Clap.Exp.c #[p,var,e]
  else if let .fvar _ := e then
    mkAppOptM ``Clap.Exp.v #[p,var,e]
  else if let (``HAdd.hAdd, ⟨_ :: _ :: _ :: _ :: l :: r :: _⟩) := e.getAppFnArgs then
    let l <- compileExp p var l
    let r <- compileExp p var r
    mkAppOptM ``Clap.Exp.add #[p,var,l,r]
  else if let (``HMul.hMul, ⟨_ :: _ :: _ :: _ :: l :: r :: _⟩) := e.getAppFnArgs then
    let l <- compileExp p var l
    let r <- compileExp p var r
    mkAppOptM ``Clap.Exp.mul #[p,var,l,r]
  else if let (``HSub.hSub, ⟨_ :: _ :: _ :: _ :: l :: r :: _⟩) := e.getAppFnArgs then
    let l <- compileExp p var l
    let r <- compileExp p var r
    mkAppOptM ``Clap.Exp.sub #[p,var,l,r]
  else throwError m!"compileExp: no match for {e}"

def typeZModp (p:Expr) : Expr := .app (mkConst ``ZMod) p
def typeCircuit (p var : Expr) : Expr := .app (.app (mkConst ``Clap.Circuit) p) var
def typeCircuit' (p : Expr) : Expr := .app (mkConst ``Clap.Circuit') p

def matchBinds (e:Expr) : Option (Expr × Expr) :=
  if let (``Bind.bind, ⟨_ :: _ :: _ :: _ :: e :: k :: _⟩) := e.getAppFnArgs then some (e,k)
  -- -- TODO this appeared after simp, can we keep only one of them?
  -- else if let (``Option.bind, ⟨_ :: _ :: e :: k :: _⟩) := e.getAppFnArgs then some (e,k)
  else none

partial def compile (p : Expr) (var : Expr) (e : Expr) : TermElabM Expr := do
  -- logInfo m!"compile\n{e}"
--  dbg_trace s!"compile\n{(<-ppExpr e)}"

  if let .lam name type body bi := e then
    if not (<- isDefEq type (typeZModp p))
    then throwError m!"compile.lam: argument not a ZMod p\n{type}"
--    dbg_trace s!"lam"
    let e <- withLocalDecl name bi var fun fvar => do
      let body := body.instantiate1 fvar
      let newBody ← compile p var body
      mkLambdaFVars #[fvar] newBody
    mkAppOptM ``Clap.Circuit.lam #[p,var,e]

  else if let (``Option.some, ⟨_ :: accept :: _⟩) := e.getAppFnArgs then
    if not (←isDefEq accept (.const ``Clap.Spec.Compiler.accept []))
    then throwError m!"compile.accept: not accept - {accept}"
--    dbg_trace s!"accept"
    mkAppOptM ``Clap.Circuit.nil #[p,var]

  else if let some (e,k) := matchBinds e then
    let .lam name type body _bi := k | throwError m!"compile.bind: not a lam"
    if let (`Clap.Spec.Compiler.eq0, ⟨_ :: e :: _⟩) := e.getAppFnArgs then
      let e : Expr <- compileExp p var e
      let k <- withLocalDecl name .default type fun u => do
        let body := body.instantiate1 u
        let body <- compile p var body
        mkLambdaFVars #[u] body
      let c := Expr.app k (mkConst ``Unit.unit)
      mkAppOptM ``Clap.Circuit.eq0 #[p,var,e,c]

    else if let (`Clap.Spec.Compiler.num2bits, ⟨_ :: w :: e :: _⟩) := e.getAppFnArgs then
        let e : Expr <- compileExp p var e
        let k <- withLocalDecl `vars .default (<- mkAppM ``List #[var]) fun fvar => do
          let body := body.instantiate1 fvar
          let body <- compile p var body
          mkLambdaFVars #[fvar] body
        mkAppM ``Clap.Circuit.num2bits #[w, e, k]
    else throwError m!"compile.bind: unknown bind\n{e.getAppFnArgs}"

  else if let .letE name _ e body _ := e then

    if let (`Clap.Spec.Compiler.is_zero, ⟨_ :: e :: _⟩) := e.getAppFnArgs then
--      dbg_trace s!"is_zero"
      let k <- withLocalDecl name .default var fun fvar => do
        let body := body.instantiate1 fvar
        let body ← compile p var body
        mkLambdaFVars #[fvar] body
      let e : Expr <- compileExp p var e
      mkAppOptM ``Clap.Circuit.is_zero #[p,var,e,k]

    else if let (`Clap.Spec.Compiler.share, ⟨_ :: e :: _⟩) := e.getAppFnArgs then
--      dbg_trace s!"share"
      let k <- withLocalDecl name .default var fun fvar => do
        let body := body.instantiate1 fvar
        let body ← compile p var body
        mkLambdaFVars #[fvar] body
      let e : Expr <- compileExp p var e
      mkAppOptM ``Clap.Circuit.share #[p,var,e,k]

    else throwError m!"compile.let: not supported\n{e}"

  else throwError m!"compile: not supported\n{e.getAppFnArgs} (missing accept?)"

partial def addVar (p : Expr) (body : Expr) : TermElabM Expr := do
  let e <- withLocalDecl `var .default (mkSort levelOne) fun var => do
    let body := body.instantiate1 var
    let body ← compile p var body
    mkLambdaFVars #[var] body
--  logInfo m!"addVar RETURN {(<-inferType e)}"
  return e

open Meta Elab Term Command in
def toDeep (p : Name) (c : Expr) : TermElabM Expr := do
  let e <- addVar (.const p []) c
  return e
