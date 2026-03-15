-- not higer-order
inductive Exp where
  | u
  | v (_ : String)
  | lam (_ : String) (_ : Exp)
  | app (_ : Exp) (_ : Exp)
  deriving Repr

abbrev Env := List (String × Exp)

def lookup (env : Env) (x : String) : Option Exp :=
  match env with
  | [] => none
  | (y, v) :: rest => if x == y then some v else lookup rest x

partial def eval (env : Env) (e : Exp) : Option (Exp × Env) :=
  match e with
  | .u => some (.u, env)
  | .v x => some ((lookup env x).getD e,env)
  | .lam x body => do
    let (body,env) ← eval env body
    some (.lam x body, env)
  | .app f arg => do
    let (arg,env) ← eval env arg
    match ← eval env f with
    | (.u,_) => none -- wrong type
    | (.lam x body, env) => eval ((x, arg) :: env) body
    | (f,env) => some (.app f arg,env)

#eval (eval [] (.app (.lam "x" (.v "x")) (.u)))

#eval (eval [] (.lam "x" (.app (.lam "y" (.v "y")) (.u))))
