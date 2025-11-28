set_option autoImplicit false
set_option linter.unusedVariables true

namespace Unit

inductive Ll (α:Type) : Type where
  | nil : Ll α
  | cons : α -> (Unit -> Ll α) -> Ll α

example : Ll Nat :=
  .cons 0 (fun () => Ll.nil)

example : Ll Nat :=
  .cons 0 (fun () => .cons 1 (fun () => Ll.nil))

def to_list {α} (l:Ll α) : List α :=
  match l with
  | .nil => .nil
  | .cons n k => .cons n (to_list (k ()))

def of_list {α} (l:List α) : Ll α :=
  match l with
  | .nil => .nil
  | .cons n ll => .cons n (fun () => of_list ll)

end Unit

namespace Nat

inductive Ll (α:Type) : Type where
  | nil : Ll α
  | cons : α -> (α -> Ll α) -> Ll α

example : Ll Nat :=
  .cons 0 (fun x => .cons x (fun _ => .nil))

-- def to_list {α} (l:Ll α) : List α :=
--   match l with
--   | .nil => .nil
--   | .cons n k => .cons n (to_list (k ()))

def of_list {α} (l:List α) : Ll α :=
  match l with
  | .nil => .nil
  | .cons n l => .cons n (fun _x => of_list l)

example : of_list [1] = .cons 1 (fun _ => .nil) := by
  simp [of_list]

example : of_list [1] = ((fun (x:Nat) => .cons (0+x) (fun _ => .nil)) 1) := by
  simp [of_list]

end Nat

namespace Again

-- Head first list, Cont
def Hfl (α:Type) : Type := (Unit -> List α) -> List α

def cons {α} (x:α) : Hfl α :=
  fun k => x :: k ()

example : Hfl Nat := fun k =>
  cons 0 (fun () => cons 1 k)

def to_list {α} (l:Hfl α) : List α :=
  l (fun () => [])

def of_list {α} (l:List α) : Hfl α :=
  match l with
  | .nil => fun _k => []
  | .cons n l => fun k => n :: (of_list l) k

example : of_list [1] = fun _ => 1 :: [] := by
  simp [of_list]

end Again
