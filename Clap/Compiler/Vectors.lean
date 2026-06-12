import Clap.Compiler.Simp
import Clap.Compiler.Wheels
import Qq
import Mathlib.Tactic

import Lean

open Lean Meta Elab Qq

namespace Clap.Compiler

def _root_.Lean.Meta.Sym.getLevelInType (e : Expr) : Sym.SymM Level := do
  let .succ u ← Sym.getLevel e | throwError m!"getLevelInType - Prop unsupported. Request:\n{e}"
  return u

def getElemVectorOfIdx (coll t sz : Expr) (idx : ℕ) : Sym.Simp.SimpM Expr := do
  let idx := mkNatLit idx
  let collT ← Sym.inferType coll
  let u ← Sym.getLevelInType collT
  let v ← Sym.getLevelInType q(ℕ)
  let w ← Sym.getLevelInType t

  -- `λ _x i ↦ i < sz`
  let valid :=
    Expr.lam `_x collT
      (Expr.lam `_i q(ℕ)
        (mkApp2 (.const ``Nat.lt []) (.bvar 0) sz) .default) .default

  -- `GetElem` instance
  let inst := mkApp2 (.const ``Vector.instGetElemNatLt [w]) t sz

  -- `coll[idx]'?proofIsValid`
  let getElemSansProof ←
    Sym.shareCommonInc <|
      mkAppN
        (.const ``GetElem.getElem [u, v, w])
        #[collT, q(ℕ), t, valid, inst, coll, idx]
    
  let proofIsValid := mkApp2 (.const ``Nat.lt []) idx sz

  Sym.shareCommonInc <| mkAppN getElemSansProof #[←mkSorry proofIsValid false]

def inferVectorProof (vectorSansProof : Expr) : Sym.Simp.SimpM Expr := do
  let .forallE _ argT _ _ ← Sym.inferType vectorSansProof | logError m!"inferVectorProof"; unreachable!
  Sym.shareCommonInc <| .app vectorSansProof (←mkSorry argT false)

def mkVecLit (t l len : Expr) : Sym.Simp.SimpM Expr := do
  let u ← Sym.getLevelInType t
  let array := mkAppN (.const ``Array.mk [u]) #[t, l]
  let vectorSansProof := mkAppN (.const ``_root_.Vector.mk [u]) #[t, len, array]
  let vector ← inferVectorProof vectorSansProof
  Sym.shareCommonInc vector -- TODO: Check if `...inc` is enough.
  
private def mkListLitAux (nil : Expr) (cons : Expr) : List Expr → Expr
  | []    => nil
  | x::xs => mkApp (mkApp cons x) (mkListLitAux nil cons xs)

open Lean Meta Sym in
def _root_.Lean.Meta.Sym.mkListLit (type : Expr) (xs : List Expr) : SymM Expr := do
  let u ← Sym.getLevelInType type
  let nil := mkApp (mkConst ``List.nil [u]) type
  match xs with
  | [] => return nil
  | _  =>
    let cons := mkApp (mkConst ``List.cons [u]) type
    return mkListLitAux nil cons xs

def sequenceAsVecExpr (name : Expr) (t sz : Expr) : Sym.Simp.SimpM Expr := do
  let lenSimped := (←Sym.simpWithGround sz).getResultExpr sz
  match lenSimped.nat? with
  | .none => 
    let error := s!"Not ground:\n{lenSimped}\nExpr:\n{name}"
    throwError m!"Cannot sequence a vector of unknown length.\n{error}"
  | .some lenSimpedNat =>
  if !Sym.isSameExpr lenSimped sz then
    trace[Clap.Compile.simp.proc.sequenceAsVecExpr]
      m!"Info: Constructing `Vector _ ({sz})` of ground length {lenSimped}. Request:\n{name}"
  let elems ← Sym.shareCommonInc (
                ←mkListLit t (←List.range lenSimpedNat |>.mapM (getElemVectorOfIdx name t sz))
              )
  let e' ← mkVecLit t elems sz
  -- trace[Clap.Compile.simp.proc.sequenceAsVecExpr]
  --   m!"[vec = {name}][length = {sz}][elemType = {t}]\n==>\n{e'}"
  return e'

-- lemma abc {α} {vec : Vector α 2} : vec = #v[vec[0], vec[1]] := by
--   rcases vec with ⟨⟨_ | ⟨_, _ | ⟨_, _ | ⟨_, tl⟩⟩⟩⟩, h⟩
--   · cases h
--   · cases h
--   · rfl
--   · cases h

-- lemma abc' : ∀ {α} {vec : Vector α 2}, vec = #v[vec[0], vec[1]] :=
--   fun {α vec} ↦
--     vec.casesOn fun arr h ↦
--       arr.casesOn
--         (motive := fun x ↦ ∀ (h : x.size = 2), Vector.mk x h = #v[(Vector.mk x h)[0], (Vector.mk x h)[1]])
--         (
--           fun l h ↦
--             l.casesOn
--               (motive := fun x =>
--                 ∀ (h : {toList := x : Array _}.size = 2),
--                   Vector.mk { toList := x } h =
--                   #v[(Vector.mk { toList := x } h)[0], (Vector.mk { toList := x } h)[1]])
--               (fun h ↦ h.casesOn
--                          (motive := fun a t ↦
--                            2 = a →
--                            h ≍ t →
--                            Vector.mk { toList := [] } h =
--                            #v[(Vector.mk { toList := [] } h)[0], (Vector.mk { toList := [] } h)[1]])
--               (fun h_1 ↦ False.elim (noConfusion_of_Nat Nat.ctorIdx h_1)) rfl HEq.rfl)
--               (
--                 fun head tail ↦
--                   tail.casesOn
--                     (motive := fun x ↦
--                       ∀ (h : { toList := head :: x : Array _}.size = 2),
--                         Vector.mk { toList := head :: x } h =
--                         #v[(Vector.mk { toList := head :: x } h)[0], (Vector.mk { toList := head :: x } h)[1]])
--                     (
--                       fun h =>
--                         h.casesOn
--                           (motive := fun a t ↦
--                             2 = a →
--                             h ≍ t →
--                             Vector.mk { toList := [head] } h =
--                             #v[(Vector.mk { toList := [head] } h)[0], (Vector.mk { toList := [head] } h)[1]])
--                           (fun h_1 ↦
--                             Nat.elimOffset (0 + 1) [].length 1 h_1
--                             fun x ↦ False.elim (noConfusion_of_Nat Nat.ctorIdx x))
--                           rfl
--                           HEq.rfl
--                     )
--                     (
--                       fun head_1 tail h ↦
--                         tail.casesOn (motive := fun x ↦
--                           ∀ (h : { toList := head :: head_1 :: x : Array _ }.size = 2),
--                             Vector.mk { toList := head :: head_1 :: x } h =
--                               #v[(Vector.mk { toList := head :: head_1 :: x } h)[0],
--                                 (Vector.mk { toList := head :: head_1 :: x } h)[1]])
--                           (fun h ↦ Eq.refl (Vector.mk { toList := [head, head_1] } h))
--                           (fun head_2 tl h ↦
--                             Eq.casesOn (motive := fun a t ↦
--                               2 = a →
--                                 h ≍ t →
--                                   Vector.mk { toList := head :: head_1 :: head_2 :: tl } h =
--                                     #v[(Vector.mk { toList := head :: head_1 :: head_2 :: tl } h)[0],
--                                       (Vector.mk { toList := head :: head_1 :: head_2 :: tl } h)[1]])
--                               h
--                               (fun h_1 ↦
--                                 Nat.elimOffset (0 + 1) (head_1 :: head_2 :: tl).length 1 h_1 fun x ↦
--                                   Nat.elimOffset 0 (head_2 :: tl).length 1 x fun x ↦
--                                     False.elim (noConfusion_of_Nat Nat.ctorIdx x))
--                               rfl HEq.rfl)
--                   h)
--               )     
--           h
--         )
--         h

/--
Use with `↓`.
-/
def dontExplodeVector : Sym.Simp.Simproc := fun e ↦ do
  let_expr GetElem.getElem _ _ _ _ _ coll _ _ := e | return .rfl
  unless coll.isFVar && (←inferType coll).isAppOf ``Vector do return .rfl
  -- trace[Clap.Compile.simp.proc.kaboom] m!"Marked done:\n{e}"
  return .rfl (done := true)

/--
Use with ↑.

TODO: The proof is not `rfl`. One can prove all of these `by aesop (add cases [Vector, Array, List])`,
      but I'd rather not lift to `aesop` and build the proof by hand (viz. `abc'` above).
-/
def explodeVector : Sym.Simp.Simproc := fun e ↦ do
  let t ← Sym.inferType e
  let_expr Vector t sz := t | return .rfl
  unless e.isFVar do return .rfl
  let sz' ← Sym.simpWithGround sz
  match (sz'.getResultExpr sz).nat? with
  | .none => throwError m!"{sz} does not simplify to ground.\nExpr:\n{e}"
  | .some _n => let explodedVec ← (sequenceAsVecExpr e t (sz'.getResultExpr sz)).run'
                trace[Clap.Compile.simp.proc.kaboom] m!"Exploding:\n{e}\n==>\n{explodedVec}"
                return .step explodedVec (←mkSorry (←mkEq e explodedVec) false)

def toVectorSequence? (e : Expr) : Sym.Simp.SimpM (Option (Expr × Expr × Expr)) := do
  unless e.isFVar do return .none
  let_expr Vector t sz := ←Sym.inferType e | return .none
  return .some ⟨←sequenceAsVecExpr e t sz, t, sz⟩

/-
Ideally, we'd just use `explodeVector` and `dontExplodeVector`
but marking things `done` in the case of `GetElem ... (.fvar _)` is not quite what the doctor ordered.

Maybe some priority system like in `simp`... for now, we'll just have a `simproc` for each
of the operations.
-/

/-
TODO: Generalise.
-/

-- open Compiler.Simp
-- #check Vector.instHAppendHAddNat
-- /--
-- TODO: Proof. Viz. `abc'`.
-- -/
-- def explodeVectorAppend : Sym.Simp.Simproc := fun e ↦ do
--   let_expr HAppend.hAppend α β γ _ a b := e | return .rfl

--   let a? ← toVectorSequence? a
--   let b? ← toVectorSequence? b
  
--   if a?.isNone && b?.isNone then return .rfl

--   let_expr Vector ta sza := ←Sym.inferType a | unreachable!
--   let_expr Vector _tb szb := ←Sym.inferType b | unreachable!
--   -- `ta` better equal `_tb`

--   let a := a?.map Prod.fst |>.getD a
--   let b := b?.map Prod.fst |>.getD b

--   let u ← Sym.getLevel α
--   let v ← Sym.getLevel β
--   let w ← Sym.getLevel γ

--   let inst := mkAppN (.const ``Vector.instHAppendHAddNat [←Sym.getLevel ta]) #[ta, sza, szb]

--   let append ←
--     Sym.shareCommonInc
--       (mkAppN (.const ``HAppend.hAppend [u, v, w]) #[α, β, γ, inst, a, b])

--   trace[Clap.Compile.simp.proc.kaboom]
--     m!"\n{e}\n==>\n{append}"

--   return .step append (←mkSorry (←mkEq e append) false)

-- /--
-- TODO: Proof. Viz. `abc'`.
-- -/
-- def explodeVectorMap : Sym.Simp.Simproc := fun e ↦ do
--   let_expr Vector.map _ _ _ f xs := e | return .rfl
--   -- logWarning m!"Exploding:\n{e}"

--   let xs ← toVectorSequence? xs
--   match xs with
--   | .none => return .rfl
--   | .some xs => let map ← reducedAndSharedInc (←mkAppM ``Vector.map #[f, xs])
--                 trace[Clap.Compile.simp.proc.kaboom]
--                   m!"\n{e}\n==>\n{map}"
--                 return .step map (←mkSorry (←mkEq e map) false)

-- /--
-- TODO: Proof. Viz. `abc'`.
-- -/
-- def explodeVectorMapIdx : Sym.Simp.Simproc := fun e ↦ do
--   let_expr Vector.mapIdx _ _ _ f xs := e | return .rfl
--   let xs ← toVectorSequence? xs
--   match xs with
--   | .none => return .rfl
--   | .some xs => let mapIdx ← Sym.shareCommonInc (←mkAppM ``Vector.mapIdx #[f, xs])
--                 trace[Clap.Compile.simp.proc.kaboom]
--                   m!"\n{e}\n==>\n{mapIdx}"
--                 return .step mapIdx (←mkSorry (←mkEq e mapIdx) false)

-- /--
-- TODO: Proof. Viz. `abc'`.
-- -/
-- def explodeVectorMapM : Sym.Simp.Simproc := fun e ↦ do
--   let_expr Vector.mapM _ _ _ _ _ f xs := e | return .rfl
--   let xs ← toVectorSequence? xs
--   match xs with
--   | .none => return .rfl
--   | .some xs => let map ← Sym.shareCommonInc (←mkAppM ``Vector.mapM #[f, xs])
--                 trace[Clap.Compile.simp.proc.kaboom]
--                   m!"\n{e}\n==>\n{map}"
--                 return .step map (←mkSorry (←mkEq e map) false)

-- /--
-- TODO: Proof. Viz. `abc'`.
-- -/
-- def explodeVectorZipWith : Sym.Simp.Simproc := fun e ↦ do
--   let_expr Vector.zipWith _ _ _ _ f a b := e | return .rfl

--   let a? ← toVectorSequence? a
--   let b? ← toVectorSequence? b
--   if a?.isNone && b?.isNone then return .rfl

--   let zipWith ← Sym.shareCommonInc (← mkAppM ``Vector.zipWith #[f, a?.getD a, b?.getD b])
--   trace[Clap.Compile.simp.proc.kaboom]
--     m!"\n{e}\n==>\n{zipWith}"
--   return .step zipWith (←mkSorry (←mkEq e zipWith) false)

-- /--
-- TODO: Proof. Viz. `abc'`.
-- -/
-- def explodeVectorDrop : Sym.Simp.Simproc := fun e ↦ do
--   let_expr Vector.drop _ _ xs k := e | return .rfl
--   let xs ← toVectorSequence? xs
--   match xs with
--   | .none => return .rfl
--   | .some xs => let drop ← reducedAndSharedInc (←mkAppM ``Vector.drop #[xs, k])
--                 trace[Clap.Compile.simp.proc.kaboom]
--                   m!"\n{e}\n==>\n{drop}"
--                 return .step drop (←mkSorry (←mkEq e drop) false)

-- /--
-- TODO: Proof. Viz. `abc'`.
-- -/
-- def explodeVectorTake : Sym.Simp.Simproc := fun e ↦ do
--   let_expr Vector.take _ _ xs k := e | return .rfl
--   let xs ← toVectorSequence? xs
--   match xs with
--   | .none => return .rfl
--   | .some xs => let take ← reducedAndSharedInc (←mkAppM ``Vector.take #[xs, k])
--                 trace[Clap.Compile.simp.proc.kaboom]
--                   m!"\n{e}\n==>\n{take}"
--                 return .step take (←mkSorry (←mkEq e take) false)
-- /--
-- TODO: Proof. Viz. `abc'`.
-- -/
-- def explodeVectorFoldr : Sym.Simp.Simproc := fun e ↦ do
--   let_expr Vector.foldr _ _ _ f init xs := e | return .rfl
--   let xs ← toVectorSequence? xs
--   match xs with
--   | .none => return .rfl
--   | .some xs => let foldr ← Sym.shareCommonInc (←mkAppM ``Vector.foldr #[f, init, xs])
--                 trace[Clap.Compile.simp.proc.kaboom]
--                   m!"\n{e}\n==>\n{foldr}"
--                 return .step foldr (←mkSorry (←mkEq e foldr) false)

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
--       trace[Clap.Compile.simp.proc.kaboom] m!"Exploding:\n{e}\n==>\n{explodedVec}"
--       let body ← Sym.replaceS body fun e _ ↦ do
--         if !Sym.isSameExpr e arg then return .none -- Does this even trigger?
--         return .some explodedVec
--         -- unless e matches .bvar 0 do return .none -- The enclosing binder.
--       return .step (←Sym.mkLambdaFVarsS #[arg] body) (←Sym.mkEqRefl e) -- Not this proof.

end Clap.Compiler
