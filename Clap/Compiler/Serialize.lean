import Mathlib.Data.Nat.Cast.Order.Ring

/-!
# `.r1cs` (v1) and `.wtns` (v2) writers

The formats are iden3
-/

namespace Clap.Serialize

/-! ## Little-endian encoding -/

def pushU32 (out : ByteArray) (x : UInt32) : ByteArray :=
  out.push x.toUInt8 |>.push (x >>> 8).toUInt8 |>.push (x >>> 16).toUInt8
    |>.push (x >>> 24).toUInt8

def pushU64 (out : ByteArray) (x : UInt64) : ByteArray :=
  out.push x.toUInt8 |>.push (x >>> 8).toUInt8 |>.push (x >>> 16).toUInt8
    |>.push (x >>> 24).toUInt8 |>.push (x >>> 32).toUInt8 |>.push (x >>> 40).toUInt8
    |>.push (x >>> 48).toUInt8 |>.push (x >>> 56).toUInt8

/-- `n` as `limbs` little-endian 64-bit words. Bits from `64 * limbs` on are dropped -/
def pushField (out : ByteArray) (n : ℕ) : (limbs : ℕ) → ByteArray
  | 0 => out
  | limbs + 1 => pushField (pushU64 out n.toUInt64) (n >>> 64) limbs

#guard (pushU32 .empty 0x01020304).toList == [4, 3, 2, 1]
#guard (pushU64 .empty 257).toList == [1, 1, 0, 0, 0, 0, 0, 0]
#guard (pushField .empty 0 1).toList == [0, 0, 0, 0, 0, 0, 0, 0]
#guard (pushField .empty (2 ^ 64 + 2) 2).toList == [2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
#guard (pushField .empty (2 ^ 64 - 1) 1).toList == List.replicate 8 255
#guard (pushField .empty 5 0).size == 0

/-- A file's magic string, version and section count. -/
def prologue (magic : String) (version nSections : UInt32) : ByteArray :=
  pushU32 (pushU32 magic.toUTF8 version) nSections

def sectionHeader (type : UInt32) (size : ℕ) : ByteArray :=
  pushU64 (pushU32 (.emptyWithCapacity 12) type) size.toUInt64

/-- The field element size, in bytes, for `prime`: the least multiple of 8 that holds every
residue. snarkjs computes it as `(⌊(bitLength - 1) / 64⌋ + 1) * 8`. -/
def fieldSizeFor (prime : ℕ) : ℕ := (Nat.log2 prime / 64 + 1) * 8

#guard fieldSizeFor 7 == 8
#guard fieldSizeFor (2 ^ 64 - 59) == 8
#guard fieldSizeFor (2 ^ 64 + 13) == 16
#guard fieldSizeFor 21888242871839275222246405745257275088548364400416034343698204186575808495617 == 32

def writeAtomically (path : System.FilePath) (f : IO.FS.Handle → IO Unit) : IO Unit := do
  let tmp := path.addExtension "tmp"
  try
    IO.FS.withFile tmp .write f
    IO.FS.rename tmp path
  catch e =>
    try IO.FS.removeFile tmp catch _ => pure ()
    throw e

/-- Constraint and witness bytes are emitted in chunks of about this size. -/
def chunkSize : ℕ := 1 <<< 16

/-- `#[f 0, …, f (n - 1)]`. `Array.map` runs core's generic monadic `mapM`, wich overflows-/
def arrayOfFn {α : Type} (n : ℕ) (f : ℕ → α) : Array α := go 0 (.emptyWithCapacity n)
where
  go (i : ℕ) (acc : Array α) : Array α :=
    if i < n then go (i + 1) (acc.push (f i)) else acc
  termination_by n - i

#guard arrayOfFn 4 (· * 10) == #[0, 10, 20, 30]
#guard arrayOfFn 0 id == #[]

/-! ## `.r1cs` -/

structure Header where
  fieldElemSize : UInt32
  prime : ℕ
  nWires : UInt32
  nPubOut : UInt32
  nPubIn : UInt32
  nPrvIn : UInt32
  nLabels : UInt64
  mConstraints : UInt32
  deriving Repr, BEq, Inhabited

/-- Section 1's payload size. -/
def Header.byteSize (h : Header) : ℕ := 4 + h.fieldElemSize.toNat + 4 * 4 + 8 + 4

def Header.bytes (h : Header) : ByteArray :=
  let out := pushU32 (.emptyWithCapacity h.byteSize) h.fieldElemSize
  let out := pushField out h.prime (h.fieldElemSize.toNat / 8)
  let out := pushU32 (pushU32 (pushU32 (pushU32 out h.nWires) h.nPubOut) h.nPubIn) h.nPrvIn
  pushU32 (pushU64 out h.nLabels) h.mConstraints

/-- `nA`, `nB` and `nC` repeat the sizes of the term arrays. Each term is a wire id and its coefficient. -/
structure Constraint where
  nA : UInt32
  nB : UInt32
  nC : UInt32
  termsA : Array (UInt32 × ℕ)
  termsB : Array (UInt32 × ℕ)
  termsC : Array (UInt32 × ℕ)
  deriving Repr, BEq, Inhabited

def Constraint.byteSize (fs : ℕ) (c : Constraint) : ℕ :=
  3 * 4 + (c.termsA.size + c.termsB.size + c.termsC.size) * (4 + fs)

/-- Each linear combination as its number of terms, then the terms. -/
def Constraint.pushBytes (fs : ℕ) (out : ByteArray) (c : Constraint) : ByteArray :=
  let lc (out : ByteArray) (terms : Array (UInt32 × ℕ)) : ByteArray :=
    terms.foldl (fun out (id, v) ↦ pushField (pushU32 out id) v (fs / 8))
      (pushU32 out terms.size.toUInt32)
  lc (lc (lc out c.termsA) c.termsB) c.termsC

abbrev Constraints := Array Constraint

abbrev WireToLabelMap := Array UInt64

structure R1CSv1 where
  header : Header
  constraints : Constraints
  wireToLabelMap : WireToLabelMap
  ultraPLONKCustomGateList : Unit
  ultraPLONKCustomGateApplication : Unit
  deriving Repr, BEq, Inhabited

namespace R1CSv1

/-- Section 2's payload size. -/
def constraintsByteSize (r : R1CSv1) : ℕ :=
  let fs := r.header.fieldElemSize.toNat
  r.constraints.foldl (fun size c ↦ size + c.byteSize fs) 0

/-- Check a linear combination. strictly increasing wire ids below `nWires`, coefficients in
`(0, prime)`. -/
def validateLC (nWires prime : ℕ) (row : ℕ) (name : String) (terms : Array (UInt32 × ℕ)) :
    Except String Unit := do
  let mut last : Option ℕ := none
  for (id, v) in terms do
    let where_ := s!"constraint {row}, {name}, wire {id}"
    unless id.toNat < nWires do throw s!"{where_}: no such wire (nWires = {nWires})"
    if let some l := last then
      unless l < id.toNat do
        throw s!"{where_}: wire ids must be strictly increasing (after wire {l})"
    unless 0 < v do throw s!"{where_}: zero coefficient"
    unless v < prime do throw s!"{where_}: coefficient {v} is not below the prime"
    last := some id.toNat

-- TODO
/-- Everything the format and snarkjs need and the writer does not enforce by construction. -/
def validate (r : R1CSv1) : Except String Unit := do
  let h := r.header
  let p := h.prime
  let fs := h.fieldElemSize.toNat
  unless 2 ≤ p do throw s!"prime {p} is below 2"
  unless fs == fieldSizeFor p do
    throw s!"field element size {fs} bytes; prime {p} needs {fieldSizeFor p} \
      (the least multiple of 8 that holds it)"
  let nWires := h.nWires.toNat
  unless h.nPubOut.toNat + h.nPubIn.toNat + h.nPrvIn.toNat < nWires do
    throw s!"{h.nPubOut} outputs, {h.nPubIn} public and {h.nPrvIn} private inputs do not fit \
      in {nWires} wires after ONE"
  unless h.mConstraints.toNat == r.constraints.size do
    throw s!"header says {h.mConstraints} constraints, there are {r.constraints.size}"
  unless r.wireToLabelMap.size == nWires do
    throw s!"the wire-to-label map has {r.wireToLabelMap.size} entries, not one per wire \
      ({nWires})"
  unless r.wireToLabelMap[0]? == some 0 do throw "wire 0 (ONE) must map to label 0"
  for h_l : i in [0:r.wireToLabelMap.size] do
    let l := r.wireToLabelMap[i]
    unless l < h.nLabels do throw s!"wire {i} maps to label {l}, but nLabels = {h.nLabels}"
  for (c, i) in r.constraints.zipIdx do
    unless c.nA.toNat == c.termsA.size && c.nB.toNat == c.termsB.size &&
        c.nC.toNat == c.termsC.size do
      throw s!"constraint {i}: counts ({c.nA}, {c.nB}, {c.nC}) differ from the terms \
        ({c.termsA.size}, {c.termsB.size}, {c.termsC.size})"
    validateLC nWires p i "A" c.termsA
    validateLC nWires p i "B" c.termsB
    validateLC nWires p i "C" c.termsC
  unless r.constraintsByteSize < UInt64.size do throw "the constraints section exceeds 2^64 bytes"

/-- The file's bytes in order in chunks -/
def encode {m : Type → Type} [Monad m] (r : R1CSv1) (emit : ByteArray → m Unit) : m Unit := do
  let fs := r.header.fieldElemSize.toNat
  emit (prologue "r1cs" 1 3)
  emit (sectionHeader 2 r.constraintsByteSize)
  let mut buf := ByteArray.emptyWithCapacity chunkSize
  for c in r.constraints do
    buf := c.pushBytes fs buf
    if buf.size ≥ chunkSize then
      emit buf
      buf := ByteArray.emptyWithCapacity chunkSize
  emit buf
  emit (sectionHeader 1 r.header.byteSize)
  emit r.header.bytes
  emit (sectionHeader 3 (8 * r.wireToLabelMap.size))
  emit (r.wireToLabelMap.foldl pushU64 (.emptyWithCapacity (8 * r.wireToLabelMap.size)))

/-- The file's bytes, or why `r` is invalid. -/
def toBytes (r : R1CSv1) : Except String ByteArray := do
  r.validate
  let ((), bytes) := (r.encode (m := StateM ByteArray) fun b ↦ modify (·.append b)).run .empty
  return bytes

end R1CSv1

def serializeR1CS (path : System.FilePath) (r1cs : R1CSv1) : IO Unit := do
  if let .error e := r1cs.validate then throw <| IO.userError s!"{path}: {e}"
  writeAtomically path fun h ↦ r1cs.encode h.write

/-- circom's `.sym` file, which `snarkjs r1cs print`. A `label,wire,component,name` line
for each of the `count` wires after ONE, `name i` naming wire `i + 1` (labels are the wire ids). -/
def serializeSym (path : System.FilePath) (count : ℕ) (name : ℕ → String) : IO Unit :=
  writeAtomically path fun h ↦ do
    for i in [0:count] do
      h.putStrLn s!"{i + 1},{i + 1},0,{name i}"

/-! ### Fixtures made by circom: byte for byte -/

private def bn254 : ℕ :=
  21888242871839275222246405745257275088548364400416034343698204186575808495617

private def header : Header where
  fieldElemSize := 32
  prime := bn254
  nWires := 4
  nPubOut := 1
  nPubIn := 0
  nPrvIn := 1
  nLabels := 4
  mConstraints := 2

private def constraints : Constraints :=
  #[
    { nA := 1
      nB := 1
      nC := 2
      termsA := #[(2, 1)]
      termsB := #[(3, 1)]
      termsC := #[(0, 1), (1, bn254 - 1)]
    },
    { nA := 1
      nB := 1
      nC := 0
      termsA := #[(2, 1)]
      termsB := #[(1, 1)]
      termsC := #[]
    },
  ]

private def isZero : R1CSv1 where
  header := header
  constraints := constraints
  wireToLabelMap := #[0, 1, 2, 3]
  ultraPLONKCustomGateApplication := ()
  ultraPLONKCustomGateList := ()

private def header₁ : Header where
  fieldElemSize := 32
  prime := bn254
  nWires := 4
  nPubOut := 1
  nPubIn := 0
  nPrvIn := 2
  nLabels := 4
  mConstraints := 1

private def ex₁ : R1CSv1 where
  header := header₁
  constraints := .singleton
    { nA := 1
      nB := 1
      nC := 1
      termsA := #[(2, bn254 - 1)]
      termsB := #[(3, 1)]
      termsC := #[(1, bn254 - 1)]
    }
  wireToLabelMap := #[0, 1, 2, 3]
  ultraPLONKCustomGateApplication := ()
  ultraPLONKCustomGateList := ()

private def sameBytes (bytes : Except String ByteArray) (fixture : System.FilePath) : IO Bool :=
  return bytes.toOption == some (← IO.FS.readBinFile fixture)

/-- info: true -/
#guard_msgs in
#eval sameBytes isZero.toBytes "Clap/Compiler/Serialize/isZero.r1cs"

/-- info: true -/
#guard_msgs in
#eval sameBytes ex₁.toBytes "Clap/Compiler/Serialize/mul.r1cs"

/-- The streaming writer, through a temporary file, gives the same bytes. -/
private def streamedBytes (r : R1CSv1) : IO ByteArray :=
  IO.FS.withTempFile fun _ path ↦ do
    serializeR1CS path r
    IO.FS.readBinFile path

/-- info: true -/
#guard_msgs in
#eval return (← streamedBytes isZero) == (← IO.FS.readBinFile "Clap/Compiler/Serialize/isZero.r1cs")

/-! ### Each invalid input is rejected -/

private def rejected (r : R1CSv1) : Bool := r.validate matches .error _

private def withRow (r : R1CSv1) (c : Constraint) : R1CSv1 := { r with constraints := #[c] }

#guard !rejected isZero && !rejected ex₁
-- a count field disagreeing with its terms (the old writer wrote `take nA`)
#guard rejected (withRow ex₁ { ex₁.constraints[0]! with nA := 2 })
#guard rejected (withRow ex₁ { ex₁.constraints[0]! with nC := 0 })
-- header constraint count, wire map size, ONE's label, labels beyond nLabels
#guard rejected { isZero with header.mConstraints := 1 }
#guard rejected { isZero with header.mConstraints := 3 }
#guard rejected { isZero with wireToLabelMap := #[0, 1, 2] }
#guard rejected { isZero with header.nLabels := 3, wireToLabelMap := #[0, 1, 2, 3] }
#guard rejected { isZero with wireToLabelMap := #[1, 0, 2, 3] }
-- coefficients: not below the prime (the old writer truncated them), zero
#guard rejected (withRow ex₁ { ex₁.constraints[0]! with termsB := #[(3, bn254)] })
#guard rejected (withRow ex₁ { ex₁.constraints[0]! with termsB := #[(3, 2 ^ 256)] })
#guard rejected (withRow ex₁ { ex₁.constraints[0]! with termsB := #[(3, 0)] })
-- wire ids: unsorted, repeated, out of range
#guard rejected (withRow ex₁ { ex₁.constraints[0]! with nC := 2, termsC := #[(1, 1), (0, 1)] })
#guard rejected (withRow ex₁ { ex₁.constraints[0]! with nC := 2, termsC := #[(1, 1), (1, 1)] })
#guard rejected (withRow ex₁ { ex₁.constraints[0]! with termsA := #[(4, 1)] })
#guard !rejected (withRow ex₁ { ex₁.constraints[0]! with nC := 2, termsC := #[(0, 1), (1, 1)] })
-- field size: not the least multiple of 8 for the prime, or too small for it
#guard rejected { isZero with header.fieldElemSize := 40 }
#guard rejected { isZero with header.fieldElemSize := 24 }
#guard rejected { isZero with header.prime := 1 }
-- input counts that do not fit after ONE
#guard rejected { isZero with header.nPrvIn := 3 }
#guard !rejected { isZero with header.nPrvIn := 2 }

/-! ## `.wtns` -/

structure Witness where
  n8 : UInt32
  prime : ℕ
  nVars : UInt32
  elements : Array ℕ
  deriving Repr, BEq, Inhabited

namespace Witness

def validate (w : Witness) : Except String Unit := do
  unless 2 ≤ w.prime do throw s!"prime {w.prime} is below 2"
  unless w.n8.toNat == fieldSizeFor w.prime do
    throw s!"field element size {w.n8} bytes; prime {w.prime} needs {fieldSizeFor w.prime}"
  unless w.elements.size == w.nVars.toNat do
    throw s!"header says {w.nVars} values, there are {w.elements.size}"
  for (v, i) in w.elements.zipIdx do
    unless v < w.prime do throw s!"witness value {i} is {v}, not below the prime"

/-- The file's bytes, in chunks. Call `validate` first. -/
def encode {m : Type → Type} [Monad m] (w : Witness) (emit : ByteArray → m Unit) : m Unit := do
  let limbs := w.n8.toNat / 8
  emit (prologue "wtns" 2 2)
  emit (sectionHeader 1 (4 + w.n8.toNat + 4))
  emit (pushU32 (pushField (pushU32 .empty w.n8) w.prime limbs) w.nVars)
  emit (sectionHeader 2 (w.n8.toNat * w.elements.size))
  let mut buf := ByteArray.emptyWithCapacity chunkSize
  for v in w.elements do
    buf := pushField buf v limbs
    if buf.size ≥ chunkSize then
      emit buf
      buf := ByteArray.emptyWithCapacity chunkSize
  emit buf

def toBytes (w : Witness) : Except String ByteArray := do
  w.validate
  let ((), bytes) := (w.encode (m := StateM ByteArray) fun b ↦ modify (·.append b)).run .empty
  return bytes

/-- Write `w` to `path`, streaming it. Throws, writing nothing, if it is invalid. -/
def serializeWitness (path : System.FilePath) (w : Witness) : IO Unit := do
  if let .error e := w.validate then throw <| IO.userError s!"{path}: {e}"
  writeAtomically path fun h ↦ w.encode h.write

private def wtns : Witness where
  n8 := 32
  prime := bn254
  nVars := 4
  elements := #[1, 6, 2, 3]

/-- info: true -/
#guard_msgs in
#eval sameBytes wtns.toBytes "Clap/Compiler/Serialize/mul.wtns"

#guard !(wtns.validate matches .error _)
-- fewer values than declared (the old writer wrote `take nVars`), a value not below the prime,
-- a field size that snarkjs would misread
#guard { wtns with nVars := 5 }.validate matches .error _
#guard { wtns with elements := #[1, 6, 2, bn254] }.validate matches .error _
#guard { wtns with n8 := 40 }.validate matches .error _

end Witness

end Clap.Serialize
