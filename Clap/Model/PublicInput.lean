import Clap.Model.Monad
import Clap.Model.Convert.Specialised
import Clap.Model.Convert.PaddedVector

/-!
# Public input allocation

Allocators that turn a Lean-level value into circuit public inputs. Each `mkInputX` takes the
number of allocations made so far and returns the allocated representation together with the
new count; the matching `mkInputXWidth` is that count's increment, and `numAlloc_mkInputX`
ties the two together so widths can be computed without unfolding the allocator.

These are the building blocks for `AllocatedProgram.allocate`; see
`Clap/Model/AllocatedProgram.lean`. For the keyless circuit's allocators, see
`Clap/Keyless/Allocate.lean`.
-/

namespace Clap

open Lang

section mkInput

variable {p numAlloc : ℕ} {σ : HashConsSt p} {α : Type}

def mkInputF (numAlloc : ℕ) : HashConsM p (F p × ℕ) := do
  let x ← HashConsM.mkVar numAlloc
  return (x, numAlloc + 1)

@[simp, grind =]
def mkInputFWidth := 1

@[simp, grind =]
lemma numAlloc_mkInputF :
  (HashConsM.getResult (mkInputF numAlloc) σ).2 =
  numAlloc + mkInputFWidth := rfl

def mkInputF8 (numAlloc : ℕ) : HashConsM p (F8 p × ℕ) := do
  let x ← HashConsM.mkVar numAlloc
  return (x, numAlloc + 1)

@[simp, grind =]
def mkInputF8Width := 1

@[simp, grind =]
lemma numAlloc_mkInputF8 :
  (HashConsM.getResult (mkInputF8 numAlloc) σ).2 =
  numAlloc + mkInputF8Width := rfl

def mkInputFB {p} (numAlloc : ℕ) : HashConsM p (FB p × ℕ) := do
  let x ← HashConsM.mkVar numAlloc
  return (x, numAlloc + 1)

@[simp, grind =]
def mkInputFBWidth := 1

@[simp, grind =]
lemma numAlloc_mkInputFB :
  (HashConsM.getResult (mkInputFB numAlloc) σ).2 =
  numAlloc + mkInputFBWidth := rfl

def mkInputFString (numAlloc : ℕ) (maxLen : ℕ) : HashConsM p (FString p maxLen × ℕ) := do
  let (data, _numAllocs) ← Vector.unzip <$> ((Vector.range maxLen).map (·+numAlloc)).mapM mkInputF8
  let numAlloc := numAlloc + maxLen
  let (len, numAlloc) ← mkInputF8 numAlloc
  return (⟨data, len⟩, numAlloc)

@[simp, grind =]
def mkInputFStringWidth (maxLen : ℕ) := maxLen + 1

@[simp, grind =]
lemma numAlloc_mkInputFString {maxLen} :
  (HashConsM.getResult (p := p) (mkInputFString (p := p) numAlloc maxLen) σ).2 =
  numAlloc + mkInputFStringWidth maxLen := rfl

def mkInputFBPaddedVector (numAlloc : ℕ) (maxLen : ℕ) : HashConsM p (PaddedVector (FB p) p maxLen × ℕ) := do
  let (data, _numAllocs) ← Vector.unzip <$> ((Vector.range maxLen).map (·+numAlloc)).mapM mkInputFB
  let numAlloc := numAlloc + maxLen
  let (len, numAlloc) ← mkInputF8 numAlloc
  return (⟨data, len⟩, numAlloc)

@[simp, grind =]
def mkInputFBPaddedVectorWidth (maxLen : ℕ) := maxLen + 1

@[simp, grind =]
lemma numAlloc_mkInputFBPaddedVector {maxLen} :
  (HashConsM.getResult (p := p) (mkInputFBPaddedVector (p := p) numAlloc maxLen) σ).2 =
  numAlloc + mkInputFBPaddedVectorWidth maxLen := rfl

def mkInputVectorF (numAlloc k : ℕ) : HashConsM p (Vector (F p) k × ℕ) := do
  let (data, _numAllocs) ← Vector.unzip <$> ((Vector.range k).map (·+numAlloc)).mapM mkInputF
  return (data, numAlloc + k)

@[simp, grind =]
def mkInputVectorFWidth (k : ℕ) := k

@[simp, grind =]
lemma numAlloc_mkInputVectorF {k} :
  (HashConsM.getResult (p := p) (mkInputVectorF (p := p) numAlloc k) σ).2 =
  numAlloc + mkInputVectorFWidth k := rfl

end mkInput

section Lemmas

@[simp, grind .]
lemma isPrefixOf_mkInputF
  {p} {x}
  {σ : HashConsSt p}
:
  σ.exprs.isPrefixOf ((mkInputF x).getHashConsState σ).exprs
:= by
  unfold mkInputF
  simp

@[simp, grind =]
lemma deref_mkInputF
  {p} {x}
  {σ : HashConsSt p}
:
  *ₑ⦃((mkInputF x).getResult σ).1, (mkInputF x).getHashConsState σ⦄ =
  .some (.v x)
:= by
  simp [mkInputF]

@[simp, grind .]
lemma wellFormed_mkInputF
  {p} {x}
  {σ : HashConsSt p}
:
  ⦃((mkInputF x).getResult σ).1, (mkInputF x).getHashConsState σ⦄.wellFormed
:= by
  aesop (add safe (by grind))

end Lemmas

end Clap
