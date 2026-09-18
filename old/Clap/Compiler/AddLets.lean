import Lean

import Clap.Spec

open Lean Meta Elab

namespace Clap

partial def findInnermost (e : Expr) : Option Expr := do
  if e.isFVar then none
  else
    let (f, args) := e.getAppFnArgs
    if ``OfNat.ofNat = f then
      none
    else if [``Clap.Spec.Compiler.share,
             ``Clap.Spec.Compiler.isZero].contains f then
      findInnermost args[1]! <|>
      some e
    else if [``HAdd.hAdd,
             ``HMul.hMul,
             ``HSub.hSub].contains f then
      findInnermost args[4]! <|>
      findInnermost args[5]!
    else none

def findFirstExp (e : Expr) : Option Expr := do
  if let (``Clap.Spec.Compiler.eq0, ⟨_ :: e :: _⟩) := e.getAppFnArgs then some e
  else if let (``Clap.Spec.Compiler.num2bits, ⟨_ :: _ :: e :: _⟩) := e.getAppFnArgs then some e
  else none

def step (eBind : Expr) : MetaM TransformStep := do
  if let (``Bind.bind, ⟨_ :: _ :: _ :: _ :: e :: _ :: _⟩) := eBind.getAppFnArgs then
    if let some (toReplace : Expr) := findFirstExp e <&> findInnermost then
      let type ← inferType toReplace
      let k ← withLetDecl `x type toReplace fun x => do
        let body := eBind.replace fun sub =>
          if sub == toReplace then some x else none
        mkLetFVars #[x] body
      return .continue k
  return .continue

def addLets (e : Expr) : MetaM Expr := do
  Meta.transform e (skipConstInApp := true) (pre := step)

end Clap
