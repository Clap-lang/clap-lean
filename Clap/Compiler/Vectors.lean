import Clap.Compiler.Simp
import Clap.Compiler.Wheels
import Qq
import Mathlib.Tactic

import Lean

open Lean Meta Elab Qq

namespace Clap.Compiler

-- def getElemVectorOfIdx (coll : Expr) (len idx : Nat) : Sym.Simp.SimpM Expr := do
--   let idxQ : Q(Nat) := ToExpr.toExpr idx
--   let szQ : Q(Nat) := mkNatLit len
--   let getElemSansProof ← Meta.mkAppM ``GetElem.getElem #[coll, idxQ]
--   let proof ← Sym.Simp.liftTermElabM (
--                 Elab.Term.mkTacticMVar q($idxQ < $szQ) (←`(by get_elem_tactic)) .term
--               )
--   Sym.Simp.liftTermElabM Term.synthesizeSyntheticMVarsNoPostponing
--   instantiateMVars <| mkAppN getElemSansProof #[proof]

-- def inferVectorProof (vectorSansProof : Expr) : Sym.Simp.SimpM Expr := do
--   let .forallE _ argT _ _ ← inferType vectorSansProof | unreachable!
--   let proof ← Sym.Simp.liftTermElabM (Term.mkTacticMVar argT (←`(by simp)) .term)
--   Sym.Simp.liftTermElabM Term.synthesizeSyntheticMVarsNoPostponing
--   pure (Expr.app vectorSansProof proof) >>= instantiateMVars

def getElemVectorOfIdx (coll : Expr) (len idx : Nat) : Sym.Simp.SimpM Expr := do
  let idxQ : Q(Nat) := ToExpr.toExpr idx
  let szQ : Q(Nat) := mkNatLit len
  let getElemSansProof ← Meta.mkAppM ``GetElem.getElem #[coll, idxQ]
  return mkAppN getElemSansProof #[←mkSorry q($idxQ < $szQ) false]

def inferVectorProof (vectorSansProof : Expr) : Sym.Simp.SimpM Expr := do
  let .forallE _ argT _ _ ← inferType vectorSansProof | unreachable!
  -- logInfo m!"vectorSansProof: {vectorSansProof}\ntype: {←inferType vectorSansProof}"
  pure (Expr.app vectorSansProof (←mkSorry argT false)) -- >>= instantiateMVars

def mkVecLit (l : Expr) (sz : Expr) : Sym.Simp.SimpM Expr := do
  let array ← mkAppM ``List.toArray #[l]
  let t := (←inferType array).getAppArgs[0]!
  let u ← getDecLevel t
  let vectorSansProof := mkAppN (.const ``_root_.Vector.mk [u]) #[t, sz, array]
  let vector ← inferVectorProof vectorSansProof
  return vector

/--
TODO: Use mkVecLit
-/
def sequenceAsVecExpr (name : Expr) (t : Expr) (len : Nat) : Sym.Simp.SimpM Expr := do
  let e' ← mkVecLit
             (←mkListLit t (←List.range len |>.mapM (getElemVectorOfIdx name len)))
             (mkNatLit len)
  trace[Clap.Compile.simp.proc.sequenceAsVecExpr]
    m!"\n{name}[length = {len}][elemType = {t}]\n==>\n{e'}"
  Sym.shareCommonInc e'

-- def needsExploding (e : Expr) : SimpM Bool := do
--   let t ← inferType e
--   return t.isAppOf ``Vector

lemma abc {α} {vec : Vector α 2} : vec = #v[vec[0], vec[1]] := by
  rcases vec with ⟨⟨_ | ⟨_, _ | ⟨_, _ | ⟨_, tl⟩⟩⟩⟩, h⟩
  · cases h
  · cases h
  · rfl
  · cases h

lemma abc' : ∀ {α} {vec : Vector α 2}, vec = #v[vec[0], vec[1]] :=
  fun {α vec} ↦
    vec.casesOn fun arr h ↦
      arr.casesOn
        (motive := fun x ↦ ∀ (h : x.size = 2), Vector.mk x h = #v[(Vector.mk x h)[0], (Vector.mk x h)[1]])
        (
          fun l h ↦
            l.casesOn
              (motive := fun x =>
                ∀ (h : {toList := x : Array _}.size = 2),
                  Vector.mk { toList := x } h =
                  #v[(Vector.mk { toList := x } h)[0], (Vector.mk { toList := x } h)[1]])
              (fun h ↦ h.casesOn
                         (motive := fun a t ↦
                           2 = a →
                           h ≍ t →
                           Vector.mk { toList := [] } h =
                           #v[(Vector.mk { toList := [] } h)[0], (Vector.mk { toList := [] } h)[1]])
              (fun h_1 ↦ False.elim (noConfusion_of_Nat Nat.ctorIdx h_1)) rfl HEq.rfl)
              (
                fun head tail ↦
                  tail.casesOn
                    (motive := fun x ↦
                      ∀ (h : { toList := head :: x : Array _}.size = 2),
                        Vector.mk { toList := head :: x } h =
                        #v[(Vector.mk { toList := head :: x } h)[0], (Vector.mk { toList := head :: x } h)[1]])
                    (
                      fun h =>
                        h.casesOn
                          (motive := fun a t ↦
                            2 = a →
                            h ≍ t →
                            Vector.mk { toList := [head] } h =
                            #v[(Vector.mk { toList := [head] } h)[0], (Vector.mk { toList := [head] } h)[1]])
                          (fun h_1 ↦
                            Nat.elimOffset (0 + 1) [].length 1 h_1
                            fun x ↦ False.elim (noConfusion_of_Nat Nat.ctorIdx x))
                          rfl
                          HEq.rfl
                    )
                    (
                      fun head_1 tail h ↦
                        tail.casesOn (motive := fun x ↦
                          ∀ (h : { toList := head :: head_1 :: x : Array _ }.size = 2),
                            Vector.mk { toList := head :: head_1 :: x } h =
                              #v[(Vector.mk { toList := head :: head_1 :: x } h)[0],
                                (Vector.mk { toList := head :: head_1 :: x } h)[1]])
                          (fun h ↦ Eq.refl (Vector.mk { toList := [head, head_1] } h))
                          (fun head_2 tl h ↦
                            Eq.casesOn (motive := fun a t ↦
                              2 = a →
                                h ≍ t →
                                  Vector.mk { toList := head :: head_1 :: head_2 :: tl } h =
                                    #v[(Vector.mk { toList := head :: head_1 :: head_2 :: tl } h)[0],
                                      (Vector.mk { toList := head :: head_1 :: head_2 :: tl } h)[1]])
                              h
                              (fun h_1 ↦
                                Nat.elimOffset (0 + 1) (head_1 :: head_2 :: tl).length 1 h_1 fun x ↦
                                  Nat.elimOffset 0 (head_2 :: tl).length 1 x fun x ↦
                                    False.elim (noConfusion_of_Nat Nat.ctorIdx x))
                              rfl HEq.rfl)
                  h)
              )     
          h
        )
        h

/--
Use with `↓`.
-/
def dontExplodeVector : Sym.Simp.Simproc := fun e ↦ do
  let_expr GetElem.getElem _ _ _ _ _ coll _ _ := e | return .rfl
  unless coll.isFVar && (←inferType coll).isAppOf ``Vector do return .rfl
  trace[Clap.Compile.simp.kaboom] m!"Done:\n{e}"
  return .rfl (done := true)

/--
Use with ↑.

TODO: The proof is not `rfl`. One can prove all of these `by aesop (add cases [Vector, Array, List])`,
      but I'd rather not lift to `aesop` and build the proof by hand (viz. `abc'` above).
-/
def explodeVector : Sym.Simp.Simproc := fun e ↦ do
  let t ← inferType e
  let_expr Vector t sz := t | return .rfl
  unless e.isFVar do return .rfl
  let sz' ← Sym.simp sz
  match (sz'.getResultExpr sz).nat? with
  | .none => throwError m!"{sz} does not simplify to ground.\nExpr:\n{e}"
  | .some n => let explodedVec ← (sequenceAsVecExpr e t n).run'
               trace[Clap.Compile.simp.kaboom] m!"Exploding:\n{e}\n==>\n{explodedVec}"
               return .step explodedVec (←mkSorry (←mkEq e explodedVec) false)

def toVectorSequence? (e : Expr) : Sym.Simp.SimpM (Option Expr) := do
  unless e.isFVar do return .none
  let_expr Vector t sz := ←inferType e | return .none
  return .some (←sequenceAsVecExpr e t sz.nat?.get!)

/-
Ideally, we'd just use `explodeVector` and `dontExplodeVector`
but marking things `done` in the case of `GetElem ... (.fvar _)` is not quite what the doctor ordered.

Maybe some priority system like in `simp`... for now, we'll just have a `simproc` for each
of the operations.
-/

/-
TODO: Generalise.
-/

open Compiler.Simp

/--
TODO: Proof. Viz. `abc'`.
-/
def explodeVectorAppend : Sym.Simp.Simproc := fun e ↦ do
  let_expr HAppend.hAppend _ _ _ _ a b := e | return .rfl

  let a? ← toVectorSequence? a
  let b? ← toVectorSequence? b
  if a?.isNone && b?.isNone then return .rfl

  let append ← reducedAndSharedInc (← mkAppM ``HAppend.hAppend #[a?.getD a, b?.getD b])
  trace[Clap.Compile.simp.kaboom]
    m!"\n{e}\n==>\n{append}"
  return .step append (←mkSorry (←mkEq e append) false)

/--
TODO: Proof. Viz. `abc'`.
-/
def explodeVectorMap : Sym.Simp.Simproc := fun e ↦ do
  let_expr Vector.map _ _ _ f xs := e | return .rfl

  let xs ← toVectorSequence? xs
  match xs with
  | .none => return .rfl
  | .some xs => let map ← reducedAndSharedInc (←mkAppM ``Vector.map #[f, xs])
                trace[Clap.Compile.simp.kaboom]
                  m!"\n{e}\n==>\n{map}"
                return .step map (←mkSorry (←mkEq e map) false)

/--
TODO: Proof. Viz. `abc'`.
-/
def explodeVectorMapM : Sym.Simp.Simproc := fun e ↦ do
  let_expr Vector.mapM _ _ _ _ _ f xs := e | return .rfl
  let xs ← toVectorSequence? xs
  match xs with
  | .none => return .rfl
  | .some xs => let map ← reducedAndSharedInc (←mkAppM ``Vector.mapM #[f, xs])
                trace[Clap.Compile.simp.kaboom]
                  m!"\n{e}\n==>\n{map}"
                return .step map (←mkSorry (←mkEq e map) false)


-- /--
-- TODO: Thought experiment to explode on demand.

-- TODO: The proof is not `rfl`. One can prove all of these `by aesop (add cases [Vector, Array, List])`,
--       but I'd rather not lift to `aesop` and build the proof by hand (viz. `abc'` above).

-- TODO: Can we share state so that we know which lambda was processed?
-- -/
-- def explodeVector' : Sym.Simp.Simproc := fun e ↦ do
--   let Expr.lam name t body _ := e | return .rfl
--   let_expr Vector t sz := t | return .rfl
--   let sz' ← Sym.simp sz
--   match (sz'.getResultExpr sz).nat? with
--   | .none => throwError m!"{sz} does not simplify to ground"
--   | .some n =>
--     -- It's very tricky to get this right using `(.bvar 0)` in `body`. Would it be... faster?
--     -- Does remaking the lambda break sharing in `Sym`?
--     lambdaTelescopeOne! e fun arg body ↦ do
--       logInfo m!"This.\nbinder[{arg}] in: {body}\nt:{t}\nn:{n}\n"
--       let explodedVec ← (sequenceAsVecExpr arg t n).run' -- Ideally `(.bvar 0)`.
--       logInfo m!"exploded: {explodedVec}"
--       trace[Clap.Compile.simp.kaboom] m!"Exploding:\n{e}\n==>\n{explodedVec}"
--       let body ← Sym.replaceS body fun e _ ↦ do
--         if !Sym.isSameExpr e arg then return .none -- Does this even trigger?
--         return .some explodedVec
--         -- unless e matches .bvar 0 do return .none -- The enclosing binder.
--       return .step (←Sym.mkLambdaFVarsS #[arg] body) (←Sym.mkEqRefl e) -- Not this proof.

end Clap.Compiler
