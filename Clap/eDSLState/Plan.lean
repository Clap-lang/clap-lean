import Clap.eDSLState.Circuit

namespace Clap

-- Constraint System needs to be able to be compiled down to R1CS
-- Ideally we want a representation as close as possible to the R1CS file as possible, to minimise the amount that must be tested
-- The current R1CS model is largely in terms of bytes



structure CIRCUIT (p : ℕ) where
  public_inputs : Array (ZMod p)
  σ : HashConsSt p
  circuit : Circuit p
  wf : circuit.wellFormed (VarStore.ofArray (public_inputs.zipIdx.map Prod.swap)) σ 0

def CIRCUIT.run {p k : ℕ} (c : CIRCUIT p) : VarStore p := sorry

def Circuit.toWg {p : ℕ} (circuit : Circuit p) (σ : HashConsSt p) : VarStore p → VarStore p := sorry

def Circuit.toCs {p : ℕ} (circuit : Circuit p) (σ : HashConsSt p) : VarStore p → Bool := sorry

def VarStore.containsInputs
  {p : ℕ}
  (varStore : VarStore p)
  (numAlloc : ℕ)
: Prop :=
  ∀ i < numAlloc, varStore[i]?.isSome

def VarStore.onlyInputs
  {p : ℕ}
  (varStore : VarStore p)
  (numAlloc : ℕ)
: Prop :=
  ∀ i ≥ numAlloc, varStore[i]?.isNone

-- TODO circuit wellformed (width?)
-- NB we have `Circuit.wellFormed` already, eh...

def Gate.WF {p : ℕ} : Gate p → Prop
  | .eq0 .. | .share .. | .isZero .. => True
  | .num2bits w .. => 2 ^ w < p

def Circuit.WF {p : ℕ} (circuit : Circuit p) : Prop :=
  ∀ gate ∈ circuit, gate.WF

def isSatisfiable {p : ℕ} (cs : VarStore p → Bool) (inputs : VarStore p) : Prop :=
  (∃ varStore, cs varStore ∧ inputs ⊆ varStore)

theorem wellbehavedness
  {p : ℕ}
  {circuit : Circuit p}
  {varStore : VarStore p}
  {numAlloc : ℕ}
  {σ : HashConsSt p}
  (h_inputs : varStore.onlyInputs numAlloc)
:
  varStore ⊆ circuit.toWg σ varStore
:= by
  done

theorem completeness
  {p : ℕ}
  {circuit : Circuit p}
  {varStore : VarStore p}
  {numAlloc : ℕ}
  {σ : HashConsSt p}
  (h_varStore : varStore.containsInputs numAlloc ∧ varStore.onlyInputs numAlloc)
:
  isSatisfiable (circuit.toCs σ) varStore →
  circuit.toCs σ (circuit.toWg σ varStore)
:= by
  done

theorem soundness
  {p : ℕ}
  (circuit : Circuit p)
  (varStore : VarStore p)
  (numAlloc : ℕ)
  (σ : HashConsSt p)
:
  circuit.toCs σ (circuit.toWg σ varStore) ↔
  [varStore, σ, numAlloc|circuit]ₑ.constraints
:= by
  done

end Clap
