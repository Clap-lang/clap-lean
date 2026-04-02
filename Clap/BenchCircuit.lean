import Clap.Spec

open Clap.Spec.Compiler

abbrev p := Primes.babybear

def Clap.BenchCircuit.mainCircuit (e : ZMod p) : Option Unit :=
  bind (eq0 e) fun () ↦
  -- insert
  accept
