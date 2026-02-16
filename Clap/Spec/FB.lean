import Clap.Spec
import Clap.Lang
import Clap.Spec.F

namespace Clap.Spec.FB

open Clap.Lang

variable {p : ℕ} [Core p]

open Core

def true : FB p := 1

def false : FB p := 0

instance : Inhabited (FB p) where
  default := false

def and (a b : FB p) : FB p := a * b

def or (a b : FB p) : FB p := a + b - a * b

def not (a : FB p) : FB p := 1 - a

def xor (a b : FB p) : FB p := a + b - 2 * a * b

def nand (a b : FB p) : FB p := 1 - (and a b)

def nor (a b : FB p) : FB p := a * b + 1 - a - b

instance : AndOp (FB p) := ⟨and⟩
instance : OrOp (FB p) := ⟨or⟩
instance : XorOp (FB p) := ⟨xor⟩
instance : Complement (FB p) := ⟨not⟩

def assert (a : FB p) : Option Unit := do
  eq0 (convert (not a))

def eq (a b : FB p) : Option (FB p) := do
  F.eq (convert a) (convert b)

def assertEq (a b : FB p) : Option Unit := do
  F.assertEq (convert a) (convert b)

def lessThanEq (a b : FB p) : Option (FB p) := do
  let na <- not a
  return or na b

end Clap.Spec.FB
