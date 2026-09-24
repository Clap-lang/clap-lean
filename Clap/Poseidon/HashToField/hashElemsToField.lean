import Clap.Poseidon.Computes
import Clap.Lang.Core.F.mkF
import Clap.Lang.Gate.eq0

namespace Clap.HashToField

open Lang Poseidon Primes

-- Poseidon is opaque to these proofs, all they know of it is `Computes H`. Left reducible, it
-- also sends `step`'s defeq checks into the round-constant tables (a `whnf` timeout).
attribute [local irreducible] Clap.poseidonBN254

/-- (Merkle-)hash a vector of field elements with Poseidon. -/
def hashElemsToField {n : ℕ} (input : FVec bn254 n) : ClapM bn254 (F bn254) :=
  if n ≤ 16 then poseidonBN254 input
  else if n ≤ 32 then do
    let h1 ← poseidonBN254 (input.extract 0 16)
    let h2 ← poseidonBN254 (input.extract 16 32)
    poseidonBN254 #v[h1, h2]
  else if n ≤ 48 then do
    let h1 ← poseidonBN254 (input.extract 0 16)
    let h2 ← poseidonBN254 (input.extract 16 32)
    let h3 ← poseidonBN254 (input.extract 32 48)
    poseidonBN254 #v[h1, h2, h3]
  else if n ≤ 64 then do
    let h1 ← poseidonBN254 (input.extract 0 16)
    let h2 ← poseidonBN254 (input.extract 16 32)
    let h3 ← poseidonBN254 (input.extract 32 48)
    let h4 ← poseidonBN254 (input.extract 48 64)
    poseidonBN254 #v[h1, h2, h3, h4]
  else do
    eq0 (← mkF 1)
    mkF 0

/-- The ideal value of `hashElemsToField` over a hash family `H`. -/
def hashElemsToFieldSpec (H : HashFn) {n : ℕ} (v : Vector (ZMod bn254) n) : ZMod bn254 :=
  if n ≤ 16 then H v
  else if n ≤ 32 then H #v[H (v.extract 0 16), H (v.extract 16 32)]
  else if n ≤ 48 then H #v[H (v.extract 0 16), H (v.extract 16 32), H (v.extract 32 48)]
  else H #v[H (v.extract 0 16), H (v.extract 16 32), H (v.extract 32 48), H (v.extract 48 64)]

namespace hashElemsToField

lemma convertsM
  {H : HashFn}
  (h_H : Computes H)
  {n : ℕ}
  {state : ClapMState bn254}
  {input : FVec bn254 n}
  {vals : Vector (ZMod bn254) n}
  (h_input : Converts FVec.conversion state input vals)
  (h_pos : 0 < n)
  (h_n : n ≤ 64)
:
  ConvertsM F.conversion (hashElemsToField input) state (hashElemsToFieldSpec H vals) True
:= by
  unfold hashElemsToField hashElemsToFieldSpec
  -- `h_n` discharges the `n ≤ 64` test, so Circom's `1 === 0` branch never arises
  split_ifs with h16 h32 h48
  · exact h_H h_pos h16 h_input
  · have c1 := h_H (by omega) (by omega) (FVec.converts_extract 0 16 h_input)
    step c1 as h1
    have c2 := h_H (by omega) (by omega) (FVec.converts_extract 16 32 h_input)
    step c2 as h2
    have h_leaves := FVec.converts_push (FVec.converts_push FVec.converts_empty h_h1) h_h2
    apply convertsM_of_convertsM (h_H (by decide) (by decide) h_leaves)
    . rfl
    . simp
  · have c1 := h_H (by omega) (by omega) (FVec.converts_extract 0 16 h_input)
    step c1 as h1
    have c2 := h_H (by omega) (by omega) (FVec.converts_extract 16 32 h_input)
    step c2 as h2
    have c3 := h_H (by omega) (by omega) (FVec.converts_extract 32 48 h_input)
    step c3 as h3
    have h_leaves := FVec.converts_push
      (FVec.converts_push (FVec.converts_push FVec.converts_empty h_h1) h_h2) h_h3
    apply convertsM_of_convertsM (h_H (by decide) (by decide) h_leaves)
    . rfl
    . simp
  · have c1 := h_H (by omega) (by omega) (FVec.converts_extract 0 16 h_input)
    step c1 as h1
    have c2 := h_H (by omega) (by omega) (FVec.converts_extract 16 32 h_input)
    step c2 as h2
    have c3 := h_H (by omega) (by omega) (FVec.converts_extract 32 48 h_input)
    step c3 as h3
    have c4 := h_H (by omega) (by omega) (FVec.converts_extract 48 64 h_input)
    step c4 as h4
    have h_leaves := FVec.converts_push (FVec.converts_push
      (FVec.converts_push (FVec.converts_push FVec.converts_empty h_h1) h_h2) h_h3) h_h4
    apply convertsM_of_convertsM (h_H (by decide) (by decide) h_leaves)
    . rfl
    . simp

end hashElemsToField

end Clap.HashToField
