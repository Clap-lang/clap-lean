import Lean

import Clap.Compiler.Vectors

open Lean Meta

def Lean.Expr.listLitIsEmpty (e : Expr) : Bool :=
  match_expr e with
  | List.cons _ _ _ => false
  | _ => true

def Lean.Expr.listLitHead (e : Expr) : Option Expr :=
  match_expr e with
  | List.cons _ hd _ => .some hd
  | _ => .none

def Lean.Expr.listLitTail (e : Expr) : Option Expr :=
  match_expr e with
  | List.cons _ _ tl => .some tl
  | _ => .none

/--
We're already doing O(n) work here anyway, maybe yield the length as well.
-/
partial def listElemsOfExpr (e : Expr) (res : Array Expr := #[]) : Option (Array Expr) :=
  match_expr e with
  | List.cons _ hd tl => listElemsOfExpr tl (res.push hd)
  | List.nil  _       => .some res
  | _                 => .none

def arrayElemsOfExpr (e : Expr) : Option (Array Expr) := do
  let_expr Array.mk _ l := e | .none
  listElemsOfExpr l

def vectorElemsOfMk (e : Expr) : Option (Array Expr × Expr × Expr) := do
  let_expr Vector.mk t sz arr _ := e | .none
  return (←arrayElemsOfExpr arr, t, sz)

/--
We're already doing O(n) work in `listElemsOfExpr` anyway, maybe yield the goodies as well.
-/
partial def elemsOfListExpr (e : Expr) (elems : Array Expr := #[]) (sz : Nat := 0) : Array Expr × Nat :=
  match_expr e with
  | List.cons _ hd tl => elemsOfListExpr tl (elems.push hd) sz.succ
  | _                 => (elems, sz) -- `List.nil` and `_`

namespace Clap.Compiler

inductive CollectionKind where | Vector | Array | List
  deriving Repr

structure CollectionType where
  t  : Expr
  k  : CollectionKind
  sz : Option Expr
  deriving Repr

namespace CollectionType

def cast (c : CollectionType) (t : CollectionKind) : Option CollectionType :=
  match t with
  | .Vector => if c.sz.isNone then .none else go c t
  | _       => go c t
  where go (c : CollectionType) (k : CollectionKind) : CollectionType := {c with k := k}

def setSize (c : CollectionType) (sz : Expr) : CollectionType :=
  {c with sz := .some sz}

def mkList (elem : Expr) := CollectionType.mk elem .List .none

def mkArray (elem : Expr) := CollectionType.mkList elem |>.cast .Array

def mkVec (elem : Expr) (sz : Expr) :=
  CollectionType.mkList elem |>.setSize sz |>.cast .Vector

end CollectionType

structure Collection where
  type     : CollectionType
  listExpr : Expr
  deriving Repr

namespace Collection

def setSize (coll : Collection) (sz : Expr) : Collection :=
  {coll with type := coll.type.setSize sz}

def elems (c : Collection) : Array Expr × Collection :=
  let (elems, sz) := elemsOfListExpr c.listExpr
  ⟨elems, c.setSize (toExpr sz)⟩

open Lean Meta Sym in
def toExpr (c : Collection) : Sym.Simp.SimpM Expr := do
  match c.type.k with
  | .List => return c.listExpr
  | .Array => shareCommonInc <| mkAppN (.const ``Array.mk [←Sym.getLevelInType c.type.t])
                                       #[c.type.t, c.listExpr]
  | .Vector => shareCommonInc (←mkVecLit c.type.t c.listExpr (←c.type.sz.getDM (unreachable!)))

def ofExpr (e : Expr) : Option Collection :=
  match_expr e with
  | Vector.mk t sz xs _ => do return ⟨←CollectionType.mkVec t sz, ←listExprOfArrayExpr xs⟩
  | Array.mk  t    _    => do return ⟨←CollectionType.mkArray t, ←listExprOfArrayExpr e⟩
  -- `List.toArray` should not be necessary, as reducible definitions must be reduced first
  | List.toArray t _    => do
    dbg_trace s!"`List.toArray` encountered; this is a bug"
    return ⟨←CollectionType.mkArray t, ←listExprOfArrayExpr e⟩
  | List.cons t    _  _ => do return ⟨←CollectionType.mkList t, e⟩
  | List.nil  t         => do return ⟨←CollectionType.mkList t, e⟩
  | _                   => .none
  where
    listExprOfArrayExpr (e : Expr) : Option Expr := do
      let_expr Array.mk _ l := e | .none
      .some l

def cast (coll : Collection) (t : CollectionKind) : Option Collection := do
  return {coll with type := ←coll.type.cast t}

def elemsOfExpr (e : Expr) : Option (Array Expr × Collection) :=
  Collection.elems <$> Collection.ofExpr e

end Collection

open Collection in
/--
TODO: Probably return the ground size?

Sequenced collection, e.g.:
- `List.cons a (List.cons b List.nil)` ==> `[a, b]`

Vectors are special, i.e.:
- `x : Vector τ sz` ==> `[x[0], x[1], ..., x[sz-1]`

We permit any free variable of type vector with size we can reduce to ground nat.
Unsized collections better enumerate their elements in the first place.
-/
def sequenced (e : Expr) : Sym.Simp.SimpM (Option (Array Expr × Collection)) := do
  match_expr e with
  | List.cons _ _ _   => return elemsOfExpr e
  | List.nil  _       => return elemsOfExpr e
  | Array.mk  _ _     => return elemsOfExpr e
  | Vector.mk _ _ _ _ => return elemsOfExpr e
  | _ =>
    if !e.isFVar then return .none
    let_expr Vector t sz := ←Sym.inferType e | return .none
    elemsOfExpr <$> sequenceAsVecExpr e t sz

end Clap.Compiler
