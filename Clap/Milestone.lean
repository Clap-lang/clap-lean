-- import Clap.Lang
-- import Clap.Compiler.Basic
-- import Clap.Cfold
-- import Clap.Compilation
-- import Clap.Quadratic

-- open Primes
-- open Clap Lang

-- /- We assume the existance of a p, prime. -/
-- variable {p : ℕ} [Fact (Nat.Prime p)]

-- structure MyCouple (p:ℕ) where
--   x : F (p:=p)
--   y : F (p:=p)

-- def test (c : MyCouple p) : Option Unit := do
--   let o ← share (c.x * 0)
--   eq0 o
--   accept

-- /--
-- info: Compiled test into test_circuit.
-- ---
-- info: Wg for test is test_wg_wrap.
-- -/
-- #guard_msgs in
-- #compile test using Primes.bn254

-- /-- info: test_circuit (var : Type) : Circuit bn254 var -/
-- #guard_msgs in
-- #check test_circuit

-- /-- info: test_wg_wrap (wg : Wg bn254) (c : MyCouple bn254) : Array (ZMod bn254) -/
-- #guard_msgs in
-- #check test_wg_wrap

-- /- We can optimize the circuit. -/
-- def test_circuit_opt := Clap.cfold' test_circuit

-- /-- info: "λ0 λ1 share (v0 * 0) eq0 v2 nil" -/
-- #guard_msgs in
-- #eval! s!"{test_circuit ℕ}"

-- /-- info: "λ0 λ1 share 0 eq0 v2 nil" -/
-- #guard_msgs in
-- #eval! s!"{test_circuit_opt ℕ}"

-- /- Compile the circuit to a cs. -/
-- def test_cs : Clap.Cs' bn254 := Clap.toCs' test_circuit_opt
-- /-- info: "λ0 λ1 λ2 eq0 (0 - v2) eq0 v2 nil" -/
-- #guard_msgs in
-- #eval! s!"{test_cs ℕ}"

-- /- Compile the circuit to a wg. -/
-- def test_wg_raw : Clap.Wg bn254 := Clap.toWg' test_circuit_opt
-- /-- info: "λ0 λ1 0 :: []" -/
-- #guard_msgs in
-- #eval! s!"{test_wg_raw}"

-- /- And use the wrapper to get nicer arguments. -/
-- def test_wg : MyCouple bn254 → Array (ZMod bn254) := test_wg_wrap test_wg_raw

-- def witness := test_wg {x := 42, y := 43}

-- def main (args : List String) : IO UInt32 := do
--   let basename := args[0]!
--   IO.println s!"snarkjs wtns check {basename}.r1cs {basename}.wtns"

--   let r1cs : R1CSv1 := Cs.toR1CS test_cs
--   serializeR1CS (basename ++ ".r1cs") r1cs

--   let wtns : Witness := Wg.toWtns bn254 witness
--   Witness.serializeWitness (basename ++ ".wtns") wtns

--   return 0
