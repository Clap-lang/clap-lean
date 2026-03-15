-- not higer-order
inductive Exp (var : Type) where
  | v (_ : var)
  | c (_ : Nat)
  | add (_ _ : Exp var)
  | lam (_ : var → Exp var)
  | app (_ : Exp var) (_ : Exp var)

inductive denotation : Type where
  | n
  | c (_ : Nat)
  | l (_ : Nat → denotation)

instance : Repr denotation where
  reprPrec expr _ := go expr
  where go (e : denotation) : Std.Format :=
    match e with
    | .n => s!"n"
    | .c n => s!"{repr n}"
    | .l f => s!".l {go (f 42)}"

def eval : Exp Nat → denotation
  | .v v => .c v
  | .c n => .c n
  | .add l r =>
    match eval l, eval r with
--    | .c 0, .c r => .c r
    | .c l, .c r => .c (l + r)
    | _,_ => .n
  | .lam f => .l fun x => eval (f x)
  | .app f a =>
    match eval f with
    | .l f =>
      match eval a with
      | .c a => f a
      | _ => .n
    | _ => .n

#eval (eval (.app (.lam fun x => .add (.c 1) (.v x)) (.c 5)))

#eval (eval (.lam fun x => .add (.c 1) (.v x)))
