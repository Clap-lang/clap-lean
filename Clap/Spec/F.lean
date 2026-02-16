import Clap.Spec
import Clap.Lang

open Clap.Lang

variable {p : ℕ} [Core p]

open Core

instance : Inhabited (F p) where
  default := 42

def assertRange (w : ℕ) (e : F p) : Option Unit := do
  let _ ← num2bits w e ; ()

def F.assertEq (a b : F p) : Option Unit := do
  eq0 (a - b)

def F.eq (a b : F p) : Option (FB p) := do
  isZero (a - b)
