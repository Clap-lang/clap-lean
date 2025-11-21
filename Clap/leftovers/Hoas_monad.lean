import Mathlib.Control.Monad.Cont
import Clap.Hoas

set_option autoImplicit false
set_option linter.unusedVariables true

open Hoas

namespace Hoas_monad

abbrev C a := Cont Circuit a

def lam : C Exp := fun k =>
  Circuit.lam k

def eq0 (e:Exp) : C Unit := fun k =>
  Circuit.eq0 e (k ())

def share (e:Exp) : C Exp := fun k =>
  Circuit.share e k

def inv (e:Exp) : C Exp := fun k =>
  Circuit.inv e k

def is_zero (e:Exp) : C Exp := fun k =>
  Circuit.is_zero e k

def assert_bool (e:Exp) : C Unit := fun k =>
  Circuit.assert_bool e (k ())

def assert_limb (e:Exp) : C Unit := fun k =>
  Circuit.assert_limb e (k ())

example : C Unit := do
  let i <- lam
  eq0 i

end Hoas_monad
