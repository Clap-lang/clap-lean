import Clap.Poseidon.Poseidon

def timeMs {α} (k : IO α) : IO (α × Float) := do
  let s ← IO.monoNanosNow
  IO.println s!"s: {s}"
  let a ← k
  let e ← IO.monoNanosNow
  IO.println s!"e: {e}"
  return (a, (e - s).toFloat / 1e6)

def main : IO Unit := do
  let s ← IO.monoNanosNow
  let ((res, σ), n) ← pure (Clap.Poseidon.poseidonBN254 #v[1, 2] |>.run 0)
  IO.println s!"{repr σ}"
  let e ← IO.monoNanosNow
  let s' ← IO.monoNanosNow
  let eval ← pure (Clap.Edsl.CircuitState.eval σ ∅ 0)
  let e' ← IO.monoNanosNow
  IO.println s!"Builder took: {(e - s).toFloat / 1e6}ms\nNum shares: {σ.size}"
  IO.println s!"Evaluation took: {(e' - s').toFloat / 1e6}ms"
  IO.println s!"{eval.numAlloc}"
  -- IO.print s!"{eval.numAlloc}"
  -- IO.print s!"{eval.numAlloc}"
  -- IO.print s!"{σ.size}"
  -- for i in List.range 2 do
  --   IO.print s!"{repr <| Γ}"
