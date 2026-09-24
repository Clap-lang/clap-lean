import Clap.Lang.Core.Combinators.mapM
import Clap.Lang.Data.Packing.num2BigEndianBits

namespace Clap.Lang.Packing

variable {p : ℕ}

/-- Each byte's 8 bits, most significant first, concatenated in byte order -/
def bytes2BigEndianBits {n : ℕ} (bytes : FVec p n) : ClapM p (FArray p (n * 8)) :=
  Vector.flatten <$> bytes.mapM (num2BigEndianBits 8)

namespace bytes2BigEndianBits

lemma convertsM
  {n : ℕ}
  {state : ClapMState p}
  {bytes : FVec p n}
  {vals : Vector (ZMod p) n}
  (h_bytes : Converts FVec.conversion state bytes vals)
:
  ConvertsM FArray.conversion (bytes2BigEndianBits bytes) state
    (vals.map fun b ↦ ((num2bitsLsbPureV 8 b).map (· == 1)).reverse).flatten
    (∀ i : Fin n, vals[i].val < 2 ^ 8)
:= by
  unfold bytes2BigEndianBits
  have h := convertsM_mapM_constraints (fun i ↦ FVec.converts_getElem h_bytes i.isLt)
    (fun h_x ↦ num2BigEndianBits.convertsM (w := 8) h_x)
  exact convertsM_map h (FArray.converts_flatten h.result) Iff.rfl

end bytes2BigEndianBits

section examples

/-! The old model's vectors (`old/Clap/Packing.lean:78-92`), run through `Circuit.toWg` /
`Circuit.toCs` on public inputs. -/

private abbrev q : ℕ := 1031

local instance instFactPrimeBytes2BigEndianBitsQ : Fact (Nat.Prime q) := ⟨by norm_num⟩

private def check (n : ℕ) (expected : Vector Bool (n * 8)) : ClapM q Unit := do
  let xs ← (Vector.range n).mapM (fun i ↦ liftM (HashConsM.mkVar (p := q) i))
  let bits ← bytes2BigEndianBits xs
  let exp ← expected.mapM FB.ofBool
  FArray.assert_eq bits exp

private def sat {n : ℕ} (xs : Vector (ZMod q) n) (expected : Vector Bool (n * 8)) : Bool :=
  let c := check n expected
  let circ  := c.getCircuit n (HashConsSt.empty q)
  let cache := c.getHashConsState n (HashConsSt.empty q)
  (circ.toCs cache n).run ((circ.toWg cache n).run xs)

example : sat #v[] #v[] = true := by native_decide
example : sat #v[1] #v[false, false, false, false, false, false, false, true] = true := by
  native_decide
example : sat #v[255, 1]
    #v[true, true, true, true, true, true, true, true,
       false, false, false, false, false, false, false, true] = true := by
  native_decide
-- out of range: slot 5 fails (`256 ≥ 2^8`), and the circuit rejects
example : sat #v[256] (Vector.replicate 8 false) = false := by native_decide

end examples

end Clap.Lang.Packing
