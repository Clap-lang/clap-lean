import Clap.eDSLState.Monad
import Clap.eDSLState.Convert.Specialised
import Clap.eDSLState.ConstraintSystem.toCs
import Clap.eDSLState.WitnessGenerator.toWg

namespace Clap

open Lang

def allocAThing {p} (numAlloc : ℕ) : HashConsM p (F p × ℕ) := do
  let x ← HashConsM.mkVar numAlloc
  return (x, numAlloc + 1)

def keyLessImpl {p} (e : ExprRef) : ClapM p Unit := do
  eq0 e



lemma crazyIvan {α : Type} {p : ℕ}
  {a : ClapM p α}
  {f : α → ClapM p Unit}
  {state : ClapMState p}
  {constraints : Prop}
  (h_a : ∀ numAlloc σ, a.getCircuit numAlloc σ = #[])
  (h_f : ConvertsM FUnit.conversion (f (a.getResult state.numAlloc state.σ)) (a.getState state) () constraints)
  :
  ((a >>= f).runAndEval state.numAlloc state.varStore state.σ).2.constraints ↔ constraints := by
  have := h_f.constraints
  simp [ClapM.runAndEval] at this ⊢
  rw [h_a]
  simp
  simp [ClapM.getState] at this
  set X := a.getResult state.numAlloc state.σ
  set numAlloc' := a.getNumAlloc state.numAlloc state.σ
  have ahrr : a.getVarStore state.varStore state.numAlloc state.σ = state.varStore := sorry
  rw [ahrr] at this
  rw [indepependent]
  

def keyLess {p} : ClapM p Unit := do
  let thingFromIt ← ClapM.alloc
  -- Not well formed, but: if keyLessImpl has convertsM and the function
  -- before it bumps numAlloc a certain amount and varstore is allocated up to that,
  -- then constraints ↔ spec
  keyLessImpl thingFromIt

structure theEnvisaged (p : ℕ) where
  StructExprRef : Type
  keyless : StructExprRef → ClapM p Unit
  numAlloc : ℕ
  allocate : HashConsM p StructExprRef

lemma abc (te : theEnvisaged p) (h : ConvertsM FUnit.conversion _)

def constraintsKeyless {p} (te : theEnvisaged (p := p)) : ConstraintSystem p :=
  let (inputs, σ) := te.allocate.run (HashConsSt.empty p)
  ((te.keyless inputs).getCircuit te.numAlloc σ).toCs (p := p) σ te.numAlloc

def witnessKeyless {p} (te : theEnvisaged (p := p)) : WitnessGenerator p :=
  let (inputs, σ) := te.allocate.run (HashConsSt.empty p)
  ((te.keyless inputs).getCircuit te.numAlloc σ).toWg (p := p) σ te.numAlloc

def constraints {p} (numAlloc : ℕ) (σ : HashConsSt p) :=
  (keyLess.getCircuit numAlloc σ).toCs (p := p)

def witness {p} (numAlloc : ℕ) (σ : HashConsSt p) :=
  (keyLess.getCircuit numAlloc σ).toWg (p := p)

end Clap
