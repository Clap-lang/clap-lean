import Clap.Lang

open Clap Lang

variable {p : ℕ} [Fact (Nat.Prime p)] [Core p]

open Core

def mainCircuit (e : F p) : Option Unit := do
  eq0 e
  eq0 (p:=p) 0
  -- insert
  accept (p:=p)
