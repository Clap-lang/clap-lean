import Clap.Spec

open Clap.Spec.Compiler

abbrev p := Primes.babybear

def Clap.BenchCircuit.mainCircuit (e : ZMod p) : Option Unit := do
  eq0 e
  eq0 (p:=p) 0
  -- insert
  accept
