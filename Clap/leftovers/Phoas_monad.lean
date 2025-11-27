import Mathlib.Control.Monad.Cont
import Clap.Circuit

set_option autoImplicit false
set_option linter.unusedVariables true

namespace Deno

def eq0 (e:F) : Option Unit :=
  if e = 0 then some () else none

def share (e:F) : F := e

def is_zero (e:F) : F := if e = 0 then 1 else 0

example (i:F) : Option Unit := do
  let zero := share 0
  eq0 (zero + i) ;
  eq0 (zero + i)

end Deno

namespace Phoas_monad

-- C the var instance, argument of continuation
abbrev C var a := Cont (Circuit var) a -- = (a -> Circuit var) -> Circuit var

def lam {var} : C var var := fun k =>
  Circuit.lam k

def eq0 {var} (e:Exp var) : C var Unit := fun k =>
  Circuit.eq0 e (k ())

def share {var} (e:Exp var) : C var var := fun k =>
  Circuit.share e k

def is_zero {var} (e:Exp var) : C var var := fun k =>
  Circuit.is_zero e k

example {var} : C var Unit := do
  let i <- lam
  let zero <- share (.c 0)
  eq0 (.v zero + .v i) ;
  eq0 (.v zero + .v i)

end Phoas_monad

namespace Notation

-- these are just sketched, probably wrong in many corner cases
scoped notation "let" x ":=" "input" "()" "in" body => Circuit.lam (fun x => body)
scoped notation "eq0" e => Circuit.eq0 e Circuit.nil
scoped notation "eq0" e ";" rest => Circuit.eq0 e rest
scoped notation "let" x ":=" "share" e "in" body => Circuit.share e (fun x => body)

example : Circuit' := fun _ =>
  let i := input () in
  let zero := share (.c 0) in
  eq0 (.v zero + .v i) ;
  eq0 (.v zero + .v i)

end Notation
