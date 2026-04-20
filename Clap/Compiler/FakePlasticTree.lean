namespace FakePlasticTree

inductive Exp where
  | leaf : Nat → Exp
  | node : Exp → Exp → Exp
deriving Repr, BEq, Inhabited, DecidableEq

def size (e:Exp) : Nat :=
  match e with
  | .leaf _ => 1
  | .node l r => size l + size r

def simp (e:Exp) : Exp :=
  match e with
  | .node _ _
  | .leaf 0 => e
  | .leaf n => .node (.leaf (n-1)) (.leaf (n-1))

namespace Rec

def visit (e:Exp) : Exp :=
  match e with
  | .node l r =>
     let l := visit l
     let r := visit r
     .node l r
  | .leaf _n => e

partial def compile (e:Exp) : Exp :=
  match e with
  | .node l r =>
     let l := compile l
     let r := compile r
     .node l r
  | .leaf _n =>
      let simped := simp e
      if simped != e then
        compile simped
      else e

end Rec

def ex : Exp := .node (.leaf 3) (.node (.leaf 1) (.leaf 1))

namespace TR

inductive Sided where | left : Exp → Sided | right : Exp → Sided
deriving Repr, Inhabited

mutual
  partial def go (todo : Exp) (stack : List Sided) : Exp :=
    match todo with
    | .leaf _ =>
      let simped := simp todo
      if simped != todo then
        go simped stack
      else
        rebuild todo stack
    | .node l r =>
      go l (.right r :: stack)

  partial def rebuild (done : Exp) (stack : List Sided) : Exp :=
    match stack with
    | [] => done
    | .right r :: rest => go r (.left done :: rest)
    | .left l :: rest => rebuild (.node l done) rest
end


end TR

namespace AssocRec

partial def compile (e:Exp) : Exp :=
  match e with
  | .node l r =>
      match compile l with
      | .node ll lr => .node ll (compile (.node lr r))
      | .leaf n => .node (.leaf n) (compile r)
  | .leaf _n => e

example : compile (
  Exp.node (Exp.node (Exp.leaf 1) (Exp.leaf 2)) (Exp.leaf 3))
  =
  Exp.node (Exp.leaf 1) (Exp.node (Exp.leaf 2) (Exp.leaf 3)) := by native_decide

end AssocRec

namespace AssocRecSimp

partial def compile (e:Exp) : Exp :=
  match e with
  | .node l r =>
      match compile l with
      | .node ll lr => .node ll (compile (.node lr r))
      | .leaf n => .node (.leaf n) (compile r)
  | .leaf _n =>
      let simped := simp e
      if simped != e then
        compile simped
      else e

-- #eval compile (Exp.node (Exp.node (Exp.leaf 2) (Exp.leaf 0)) (Exp.leaf 2))

end AssocRecSimp


partial def toListInverted (e : Exp) (done : List Exp) (todo : List Exp) : List Exp :=
  match e with
  | .leaf _ =>
    let simped := simp e
    if simped != e then
      toListInverted simped done todo
    else
      let done := (e::done)
      match todo with
      | [] => done
      | e::todo => toListInverted e done todo
  | .node l r => toListInverted l done (r :: todo)

-- #eval toListInverted ex [] []

end FakePlasticTree
