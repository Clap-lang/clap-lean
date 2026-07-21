import Clap.Poseidon.Poseidon

def main : IO Unit := do
  let ((res, Γ), n) := Clap.Poseidon.poseidonBN254 #v[1, 2] |>.run 0
  IO.print s!"{repr <| Γ.size}"
