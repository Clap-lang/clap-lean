---
name: specifying-circuits
description: Rules for writing a CLAP circuit gadget in the ClapM monad and stating its ConvertsM specification.
when-to-use: You are adding a new gadget to Clap/Lang/, or writing down what an existing gadget is supposed to do.
---

# Specifying CLAP circuits

Read [clap-agent-guide.md](clap-agent-guide.md) first. Read
[proving-circuits.md](proving-circuits.md) **before** you write Lean — the definition and the
proof are designed together, and a gadget written without the proof in mind usually has to be
rewritten.

## Decide first: which shape is your gadget?

| Your gadget | Return type | Constraints slot | Skeleton |
|---|---|---|---|
| Computes a field value, asserts nothing | `ClapM p (F p)` | `True` | A |
| Computes a bit, asserts nothing | `ClapM p (FB p)` | `True` | A |
| Computes a bit vector, asserts nothing | `ClapM p (FArray p k)` | `True` | A |
| Asserts something, returns nothing | `ClapM p Unit` | the assertion, e.g. `a_val = b_val` | B |
| Computes *and* asserts | value type | the assertion | B |
| Iterates (`mapM` / `foldlM`) over a vector | `FArray`/`FList` | either | C |

Skeleton A is a straight-line composition. B additionally needs the two `↔` directions proved.
C additionally needs recursion-equation lemmas *before* the spec. C is roughly ten times the
work of A; if you can express your gadget without iteration, do.

## Rules for the definition

1. **One gadget per file.** Path mirrors the return type:
   `Clap/Lang/<F|FB|FArray|FList|FUnit>/<name>.lean`.
2. **Register it in two places**, both hand-maintained and alphabetised:
   [Clap/Lang/All.lean](../Clap/Lang/All.lean) and [Clap.lean](../Clap.lean). Forgetting either
   means your file is never built.
3. **`namespace Clap.Lang`**, then `variable {p : ℕ}`. (`Clap/Lang/Core/FB/and.lean` uses
   `Clap.Lang.FB`; either is acceptable, match the neighbours.)
4. **You almost certainly do not need `open HashConsM`.** `mkF`/`mkAdd`/`mkSub`/`mkMul` are
   `Clap.Lang.*` ([F/mkAdd.lean](../Clap/Lang/Core/F/mkAdd.lean) and siblings) and are already in
   scope inside `namespace Clap.Lang`. Only `BoundRef`, `mkConstant`, `mkVar` and the
   *homonymous* `HashConsM.mkAdd`/`mkSub`/`mkMul` need the `open` — and rule 5 says not to write
   those in a gadget anyway.
5. **Use the type aliases** `F p`, `FB p`, `FArray p k`, `FVec p k`, `FList p`,
   `FString p w`. Never write `ExprRef` in a gadget signature — besides the style, it is what
   makes `+ - *` mean the right thing (rule 7a).
6. **Add `[p.AtLeastTwo]` only if the proof needs it.** It is needed when boolean semantics are
   involved (`eq`, `singleOneArray`, everything going through `FB.converts_of_F_converts`); it
   is *not* on the arithmetic gadgets or `mkF`.
7. **Every arithmetic node is a bind, and the operator is the preferred spelling.**
   Write `←(a + b)`, `←(a - b)`, `←(a * b)`, not `←mkAdd a b`. There is no pure arithmetic on
   `F p` — see [porting-guide.md](porting-guide.md) if that surprises you.
   [F/conditionalSwap.lean:10-13](../Clap/Lang/Core/F/conditionalSwap.lean#L10-L13) is the model:

   ```lean
   def conditionalSwap (sel : FB p) (a b : F p) : ClapM p (F p) := do
     let diff ← a - b
     let scaled ← diff * sel
     mkAdd scaled b
   ```

   Two caveats. **(a)** The operator takes `p` **from its operands** — at least one must be
   written at `F p`/`FB p`/`BoundRef p`. The expected type does *not* supply it: with two bare
   `ExprRef` operands you get `Nat` addition on heap indices, silently where no monadic value is
   expected. Rule 5 already keeps you safe here; see
   [clap-model.md §Arithmetic notation](clap-model.md#arithmetic-notation) for the details and
   the escape hatch.
   **(b)** `mkAdd`/`mkSub`/`mkMul` have not gone away: they are *defined as* the operators and
   remain the names your **proof** cites, as `mkSub.convertsM` etc. Most gadgets in `Clap/Lang/`
   predate the change and still spell out `mk*` in their definitions; that is equivalent.
8. **Constants must be allocated**: `←mkF 1`, never a bare `1`.
9. **Compose from what exists.** Do not re-derive a gadget that is already in `Clap/Lang/`.

### Existing inventory — reuse these

| Gadget | File | Type | Ideal value | Constraints |
|---|---|---|---|---|
| `mkF a` | [F/mkF.lean](../Clap/Lang/Core/F/mkF.lean) | `ClapM p (F p)` | `a` | `True` |
| `mkAdd a b` — write `←(a + b)` | [F/mkAdd.lean](../Clap/Lang/Core/F/mkAdd.lean) | `ClapM p (F p)` | `a_val + b_val` | `True` |
| `mkSub a b` — write `←(a - b)` | [F/mkSub.lean](../Clap/Lang/Core/F/mkSub.lean) | `ClapM p (F p)` | `a_val - b_val` | `True` |
| `mkMul a b` — write `←(a * b)` | [F/mkMul.lean](../Clap/Lang/Core/F/mkMul.lean) | `ClapM p (F p)` | `a_val * b_val` | `True` |
| `ofUInt8 u` | [F/ofUInt8.lean](../Clap/Lang/Core/F/ofUInt8.lean) | `ClapM p (F p)` | `(u.toNat : ZMod p)` | `True` |
| `ofChar c` | [F/ofChar.lean](../Clap/Lang/Core/F/ofChar.lean) | `ClapM p (F p)` | `(c.toUInt8.toNat : ZMod p)` | `True` |
| `conditionalSwap sel a b` | [F/conditionalSwap.lean](../Clap/Lang/Core/F/conditionalSwap.lean) | `ClapM p (F p)` | `if sel_val then a_val else b_val` | `True` |
| `dotProduct a b` | [F/dotProduct.lean](../Clap/Lang/Core/F/dotProduct.lean) | `ClapM p (F p)` | `(a_vals.zip b_vals).foldl (fun acc xy ↦ acc + xy.1 * xy.2) 0` | `True` |
| `isZero a` | [FB/isZero.lean](../Clap/Lang/Gate/isZero.lean) | `ClapM p (FB p)` | `a_val == 0` | `True` |
| `not a` | [FB/not.lean](../Clap/Lang/Core/FB/not.lean) | `ClapM p (FB p)` | `!a_val` | `True` |
| `FB.and a b` | [FB/and.lean](../Clap/Lang/Core/FB/and.lean) | `ClapM p (FB p)` | `a_val && b_val` | `True` |
| `FB.or a b` | [FB/or.lean](../Clap/Lang/Core/FB/or.lean) | `ClapM p (FB p)` | `a_val \|\| b_val` | `True` |
| `FB.xor a b` | [FB/xor.lean](../Clap/Lang/Core/FB/xor.lean) | `ClapM p (FB p)` | `a_val ^^ b_val` | `True` |
| `FB.ofBool b` | [FB/ofBool.lean](../Clap/Lang/Core/FB/ofBool.lean) | `ClapM p (FB p)` | `b` | `True` |
| `eq a b` | [FB/eq.lean](../Clap/Lang/Core/FB/eq.lean) | `ClapM p (FB p)` | `a_val == b_val` | `True` |
| `FB.eq a b` (Bool-typed) | [FB/eqBool.lean](../Clap/Lang/Core/FB/eqBool.lean) | `ClapM p (FB p)` | `a_val == b_val` | `True` |
| `eq0 a` | [FUnit/eq0.lean](../Clap/Lang/Gate/eq0.lean) | `ClapM p Unit` | `()` | `a_val = 0` |
| `assert_eq a b` | [FUnit/assert_eq.lean](../Clap/Lang/Core/FUnit/assert_eq.lean) | `ClapM p Unit` | `()` | `a_val = b_val` |
| `FB.assert_eq a b` (Bool-typed) | [FB/assert_eq.lean](../Clap/Lang/Core/FB/assert_eq.lean) | `ClapM p Unit` | `()` | `a_val = b_val` |
| `assert a` | [FB/assert.lean](../Clap/Lang/Core/FB/assert.lean) | `ClapM p Unit` | `()` | `a_val = true` |
| `FB.assertBool f` | [FB/assertBool.lean](../Clap/Lang/Core/FB/assertBool.lean) | `ClapM p Unit` | `()` | `f_val = 0 ∨ f_val = 1` |
| `FB.conditionallyAssert a c` | [FB/conditionallyAssert.lean](../Clap/Lang/Core/FB/conditionallyAssert.lean) | `ClapM p Unit` | `()` | `a_val = true → c_val = true` |
| `guardedEq0 g c` | [FUnit/guardedEq0.lean](../Clap/Lang/Core/FUnit/guardedEq0.lean) | `ClapM p Unit` | `()` | `g_val = true → c_val = 0` |
| `guardedAssertEq g a b` | [FUnit/guardedAssertEq.lean](../Clap/Lang/Core/FUnit/guardedAssertEq.lean) | `ClapM p Unit` | `()` | `g_val = true → a_val = b_val` |
| `FArray.sum vals` | [FArray/sum.lean](../Clap/Lang/Data/FArray/sum.lean) | `ClapM p (F p)` | `(vals.map (if · then 1 else 0)).sum` | `True` |
| `FArray.sum' init vals` | [FArray/sum.lean](../Clap/Lang/Data/FArray/sum.lean) | `ClapM p (F p)` | as above | `True` |
| `oneHotRaw len idx` | [FArray/OneHotRaw.lean](../Clap/Lang/Data/FArray/OneHotRaw.lean) | `ClapM p (FArray p len)` | `Vector.ofFn (·.val == idx_val.val)` | `True` |
| `singleOneArray len idx` | [FArray/singleOneArray.lean](../Clap/Lang/Data/FArray/singleOneArray.lean) | `ClapM p (FArray p len)` | as above | `idx_val.val < len` |
| `FArray.default w` | [FArray/default.lean](../Clap/Lang/Data/FArray/default.lean) | `ClapM p (FArray p w)` | `Vector.replicate w false` | `True` |
| `FArray.ofBitVec bv` | [FArray/ofBitVec.lean](../Clap/Lang/Data/FArray/ofBitVec.lean) | `ClapM p (FArray p w)` | `Vector.ofFn (bv[·])` | `True` |
| `FArray.zeroExtend v w'` | [FArray/zeroExtend.lean](../Clap/Lang/Data/FArray/zeroExtend.lean) | `ClapM p (FArray p (w+w'))` | `vals ++ Vector.replicate w' false` | `True` |
| `FArray.eq a b` | [FArray/eq.lean](../Clap/Lang/Data/FArray/eq.lean) | `ClapM p (FB p)` | `decide (a_vals = b_vals)` | `True` |
| `FArray.assert_eq a b` | [FArray/assert_eq.lean](../Clap/Lang/Data/FArray/assert_eq.lean) | `ClapM p Unit` | `()` | `∀ i : Fin w, a_vals[i] = b_vals[i]` |
| `FArray.bits2num bits` | [FArray/bits2num.lean](../Clap/Lang/Data/FArray/bits2num.lean) | `ClapM p (F p)` | `FArray.toNum bits_val` | `True` |
| `FBV8.ofUInt8 u` | [FArray/Widths.lean](../Clap/Lang/Data/Widths.lean) | `ClapM p (FBV8 p)` | `Vector.ofFn (u.toBitVec[·])` | `True` |
| `F32.default` | [FArray/Widths.lean](../Clap/Lang/Data/Widths.lean) | `ClapM p (F32 p)` | `Vector.replicate 32 false` | `True` |
| `F32.ofUInt32 u` | [FArray/Widths.lean](../Clap/Lang/Data/Widths.lean) | `ClapM p (F32 p)` | `Vector.ofFn (u.toBitVec[·])` | `True` |
| `F32.ofFBV8 u8` | [FArray/Widths.lean](../Clap/Lang/Data/Widths.lean) | `ClapM p (F32 p)` | `vals ++ Vector.replicate 24 false` | `True` |
| `F32.assert_eq a b` | [FArray/Widths.lean](../Clap/Lang/Data/Widths.lean) | `ClapM p Unit` | `()` | `∀ i : Fin 32, a_vals[i] = b_vals[i]` |
| `FVec.eq a b` | [FVec/eq.lean](../Clap/Lang/Data/FVec/eq.lean) | `ClapM p (FB p)` | `decide (a_vals = b_vals)` | `True` |
| `FString.ofString s` | [FString/ofString.lean](../Clap/Lang/Data/FString/ofString.lean) | `ClapM p (FString p w)` | `s` | `True` |
| `FString.isPaddedOf a b` | [FString/isPaddedOf.lean](../Clap/Lang/Data/FString/isPaddedOf.lean) | `ClapM p (FB p)` | `decide (encodeV w a_val = encodeV w b) && (a_val.length == b.length)` | `True` |
| `num2bits w e` | [FArray/num2bits.lean](../Clap/Lang/Gate/num2bits.lean) | `ClapM p (FArray p w)` | `num2bitsLsbPureV w e_val` as bits | `e_val.val < 2 ^ w` — see the note below |
| `lessThan w a b` | [F/lessThan.lean](../Clap/Lang/Core/F/lessThan.lean) | `ClapM p (FB p)` | `a_val.val < b_val.val` | `True` |
| `lessEqThan`, `greaterThan`, `greaterEqThan` | [F/lessThan.lean](../Clap/Lang/Core/F/lessThan.lean) | `ClapM p (FB p)` | the obvious variants | `True` |
| `assert_range w e` | [FUnit/assert_range.lean](../Clap/Lang/Core/FUnit/assert_range.lean) | `ClapM p Unit` | `()` | `e_val.val < 2 ^ w` |
| `F8.eq`, `F8.lessThan`, `F8.greaterThan`, `F8.lessEqThan`, `F8.greaterEqThan` | [F8/F8.lean](../Clap/Lang/Data/F8/F8.lean) | `ClapM p (FB p)` | byte-width delegations to the above at `w = 8`, stated over `UInt8` | `True` |
| `FBitVec.binSum a b` | [FBitVec/binSum.lean](../Clap/Lang/Data/FBitVec/binSum.lean) | `ClapM p (FBitVec p (w+1))` | `toNum a_vals + toNum b_vals` as `w+1` bits | `True` |
| `F32.add a b` | [FArray/Widths.lean](../Clap/Lang/Data/Widths.lean) | `ClapM p (F32 p)` | the above, `take 32` — i.e. wrapping 32-bit addition | `True` |
| `FBV8.ofF`, `F32.ofF`, `F64.ofF` | [FArray/Widths.lean](../Clap/Lang/Data/Widths.lean) | `ClapM p (FArray p w)` | `num2bits` at `w = 8`/`32`/`64` | `x_val.val < 2 ^ w` |
| `F8.isWhitespace c` | [F8/isWhitespace.lean](../Clap/Lang/Data/F8/isWhitespace.lean) | `ClapM p (FB p)` | `c_val` is space, tab, CR or LF | `True` |
| `arraySelector len s e` | [FArray/arraySelector.lean](../Clap/Lang/Data/FArray/arraySelector.lean) | `ClapM p (FArray p len)` | 1s on `[startIdx, endIdx)` | index bounds |
| `singleEndArray len idx` | [FArray/singleEndArray.lean](../Clap/Lang/Data/FArray/singleEndArray.lean) | `ClapM p (FArray p len)` | 1s from `idx` on | `idx_val.val < len` |
| `FArray.xor a b` | [FArray/xor.lean](../Clap/Lang/Data/FArray/xor.lean) | `ClapM p (FArray p k)` | pointwise `xor` | `True` |
| `FArray.xorScan a` | [FArray/xorScan.lean](../Clap/Lang/Data/FArray/xorScan.lean) | `ClapM p (FArray p k)` | running `xor` prefix scan | `True` |
| `FBitVec.eq a b` | [FBitVec/eq.lean](../Clap/Lang/Data/FBitVec/eq.lean) | `ClapM p (FB p)` | `a_val == b_val` | `True` |
| `FBitVec.assert_eq a b` | [FBitVec/assert_eq.lean](../Clap/Lang/Data/FBitVec/assert_eq.lean) | `ClapM p Unit` | `()` | `a_val = b_val` |
| `Packing.assertIsBytes a` | [Packing/assertIsBytes.lean](../Clap/Lang/Data/Packing/assertIsBytes.lean) | `ClapM p Unit` | `()` | `∀ i, a_vals[i].val < 2 ^ 8` |
| `Packing.assertIs64BitLimbs a` | [Packing/assertIs64BitLimbs.lean](../Clap/Lang/Data/Packing/assertIs64BitLimbs.lean) | `ClapM p Unit` | `()` | `∀ i, a_vals[i].val < 2 ^ 64` |
| `Packing.bigEndianBits2Num bits` | [Packing/bigEndianBits2Num.lean](../Clap/Lang/Data/Packing/bigEndianBits2Num.lean) | `ClapM p (F p)` | `FArray.toNum bits_val.reverse` | `True` |
| `Packing.num2BigEndianBits w e` | [Packing/num2BigEndianBits.lean](../Clap/Lang/Data/Packing/num2BigEndianBits.lean) | `ClapM p (FArray p w)` | `num2bits`, reversed | `e_val.val < 2 ^ w` |
| `Packing.bytes2BigEndianBits bytes` | [Packing/bytes2BigEndianBits.lean](../Clap/Lang/Data/Packing/bytes2BigEndianBits.lean) | `ClapM p (FArray p (n*8))` | each byte's bits MSB first, flattened | `∀ i, vals[i].val < 2 ^ 8` |
| `Packing.chunksToFieldElem b chunks` | [Packing/chunksToFieldElem.lean](../Clap/Lang/Data/Packing/chunksToFieldElem.lean) | `ClapM p (F p)` | `Packing.chunksToNum b vals` (little-endian, base `2^b`) | `True` |
| `Packing.chunksToFieldElems cps b chunks` | [Packing/chunksToFieldElems.lean](../Clap/Lang/Data/Packing/chunksToFieldElems.lean) | `ClapM p (FVec p w)` | `(toChunks cps vals).map (chunksToNum b)` | `True` |
| `Packing.bigEndianBitsToScalars bps bits` | [Packing/bigEndianBitsToScalars.lean](../Clap/Lang/Data/Packing/bigEndianBitsToScalars.lean) | `ClapM p (FVec p w)` | each `bps`-bit chunk read big-endian | `True` |
| `HashToField.hashElemsToField input` | [HashToField/hashElemsToField.lean](../Clap/Poseidon/HashToField/hashElemsToField.lean) | `ClapM bn254 (F bn254)` | `hashElemsToFieldSpec H vals` — Poseidon, or a 16-ary tree up to 64 | `True`, given `Poseidon.Computes H`, `0 < n ≤ 64` |
| `HashToField.hashBytesToField input` | [HashToField/hashBytesToField.lean](../Clap/Poseidon/HashToField/hashBytesToField.lean) | `ClapM bn254 (F bn254)` | `hashBytesToFieldSpec H data_vals len_val` | `∀ i, data_vals[i].val < 2 ^ 8`, given `Poseidon.Computes H`, `numBytes ≤ 1953` |
| `HashToField.hash64BitLimbsToField input` | [HashToField/hash64BitLimbsToField.lean](../Clap/Poseidon/HashToField/hash64BitLimbsToField.lean) | `ClapM bn254 (F bn254)` | `hash64BitLimbsToFieldSpec H limbs_vals len_val` | `True`, given `Poseidon.Computes H`, `numLimbs ≤ 45` |

Three things the table cannot show:

- **`FVec.eq`, `FArray.eq` and `FBitVec.eq` are the same circuit.** `FVec p k`, `FArray p k`
  and `FBitVec p k` are all `Vector _ k` over the same cell type; they differ only in the
  conversion cited — `FVec.conversion` (`Vector (ZMod p) w`), `FArray.conversion`
  (`Vector Bool w`) — and, for `FBitVec`, in stating vector equality where `FArray` states the
  pointwise form. `FBitVec.eq` / `assert_eq` are thin delegations to the `FArray` ones. Before
  adding a gadget, check all three namespaces.
- **`PaddedVector` is polymorphic in its element type.** `PaddedVector α p w` is
  `data : Vector α w` plus `len : F p`; `FString p w = PaddedVector (F p) p w`, and the keyless
  inputs use `PaddedVector (FB p) p w` for per-character flags.
- **`FArray/Widths.lean` also defines `abbrev F64 p := FArray p 64`**, whose only gadget is
  `F64.ofF`. Most `FBV8`/`F32` entries are thin delegations — `F32.ofFBV8` is
  `FArray.zeroExtend u8 24` and its `convertsM` is a bare term, which is the pattern to copy.
- **There is no width-generic `FBitVec.ofF`.** The old model's `FBitVec.ofF w e` was defined as
  `num2bits w e` with the same argument order, so porting it would add a pure alias. Use
  `num2bits` directly; only the width-specialised `FBV8.ofF` / `F32.ofF` / `F64.ofF` exist, for
  symmetry with `ofUInt8` / `ofUInt32`.
- **`isPaddedOf` has a second spec**, `isPaddedOf.convertsM_string`, whose ideal value is the
  cleaner `decide (a_val = b)`. It costs the explicit injectivity hypotheses `256 < p`,
  `w < p`, `s.length < w`, because injectivity of the encoding is not part of `Converts`.

For iterating gadgets, do not hand-roll the induction — see
[§Iterating gadgets need rewrite lemmas *first*](#iterating-gadgets-need-rewrite-lemmas-first)
for `convertsM_foldlM`, `convertsM_foldlM_constraints`, `convertsM_ofFnM`, `convertsM_mapM` and
`convertsM_mapM_constraints`.

Not yet wrapped: **`share`** and **`fpmul`**. Both are fully implemented *gates* — they are in
[eDSL.lean](../Clap/Model/eDSL.lean) with the complete `wellFormed_*` / `eval_edsl_*` /
`getResult_*` / `getVarStore_*` / `getCircuit_*` family, and both have `ConstraintSystem/` and
`WitnessGenerator/` modules. What neither has is a `Clap/Lang/` wrapper carrying a `convertsM`,
and that is what your gadget needs; write it first. `num2bits` used to be on this list and is
the bottleneck for every comparison, range check, packing and hashing gadget; it is now
wrapped, along with the whole comparison family built on it.

### `num2bits` range-checks, in the model as in the circuit

`num2bits.convertsM`'s constraints slot is `e_val.val < 2 ^ w`. The evaluation semantics
`stepNum2bits` ([CircuitEvalSt.lean:416](../Clap/Model/CircuitEvalSt.lean#L416)) asserts it
alongside allocatedness, and it is exactly the condition under which the lowering in
[ConstraintSystem/num2bits.lean](../Clap/Model/ConstraintSystem/num2bits.lean) — booleanity plus
`bits2num(bits) - expr` — is satisfiable, for every prime: when `2^w ≤ p` boolean bits recompose
to `e` only in range, and when `2^w > p` every field element is in range. So there is no
hypothesis relating `w` and `p`. (Until 2026-09-23 the semantics truncated instead, and this
slot was `True`.)

A gadget that decomposes a value it knows to fit discharges the condition and keeps slot 5
`True`: `lessThan` from its bounds on `a` and `b`, `binSum` because two `w`-bit values always sum
below `2^(w+1)`. A range check such as `assert_range` surfaces it as its own slot 5. The smoke
tests at the bottom of [FUnit/assert_range.lean](../Clap/Lang/Core/FUnit/assert_range.lean)
cross-check the model against the lowering.

For public inputs — giving a circuit a top-level input rather than taking `Converts`
hypotheses — see [public-inputs.md](public-inputs.md).

## The specification

Every gadget gets **exactly one** aggregate lemma. It is named `convertsM`, it lives in a
namespace matching the definition's name, and it has this shape:

```lean
namespace <name>

lemma convertsM
  [p.AtLeastTwo]                                            -- only if needed
  {state : ClapMState p}
  {<args>} {<arg>_val …}
  (h_<arg> : Converts <C>.conversion state <arg> <arg>_val)  -- one per circuit-valued input
  (h_<side> : …)                                             -- pure side conditions, e.g. len < p
:
  ConvertsM <C>.conversion (<name> <args>) state <ideal value> <constraints>
:= by
  …

end <name>
```

### Slot 4 — the ideal value

A pure Lean value in `conversion.IdealT`: `ZMod p` for `F`, `Bool` for `FB`, `Vector Bool k`
for `FArray`, `List Bool` for `FList`, `()` for `FUnit`. It is what the gadget *computes*,
written in ordinary mathematics with no circuit vocabulary at all.

Real examples: `a_val + b_val`, `a_val == b_val`, `!a_val`, `a_val && b_val`,
`(vals.map (λ x => if x then (1 : ZMod p) else 0)).sum`,
`Vector.ofFn (λ x => x.val == idx_val.val)`.

### Slot 5 — the constraints

The `Prop` under which the circuit is satisfiable. This is the interesting half of the spec.

- **`True`** if and only if the gadget emits no assertion that can fail. `mkAdd`, `isZero`,
  `not`, `and`, `eq`, `oneHotRaw` are all `True`.
- **A real predicate** otherwise: `eq0` → `a_val = 0`, `assert_eq` → `a_val = b_val`,
  `assert` → `a_val = true`, `singleOneArray` → `idx_val.val < len`.

Writing `True` for a gadget that does assert something is the most damaging mistake available
here: the lemma will be false, and you will discover it only when the `↔` refuses to close.

Anything the old model expressed by returning `none` belongs in this slot. A doc comment saying
"only satisfiable when `0 ≤ idx < len`" is not a specification; `idx_val.val < len` in slot 5
is.

### Side conditions

Bounds that are facts about the *parameters* rather than the values go in as ordinary
hypotheses, not into slot 5. `oneHotRaw` and `singleOneArray` both take `(h_len : len < p)`.
Anything the old model wrote as `assert!` becomes a hypothesis of this kind.

## Naming rules

| Thing | Name |
|---|---|
| The aggregate lemma | `convertsM` — always, no exceptions |
| Input hypotheses | `h_<argname>` |
| The three `ConvertsM` field lemmas | `wellFormed`, `converts`, `constraints` |
| A raw-`HashConsM` fact under a `ClapM` wrapper | `hashConsM_converts` / `hashConsM_convertsM` |
| Accumulator-generalised variant | prime: `FArray.sum'` |
| Index-generalised variant | `_aux`: `oneHotRaw_aux` |
| `List` mirror of a `Vector` gadget | prime: `oneHotRaw'` |
| Recursion equations | `<name>_zero`, `<name>_succ` |
| Vector↔List transfer | `toList_map_<x>_eq_<y>`, `getResult_<x>`, `getCircuit_<x>`, … |

**NEVER** name a lemma `_spec`, `_sound`, `_complete` or `_correct`. Those names do not exist in
this model and using them signals you have misunderstood `ConvertsM.constraints`.

## Two ways to assemble `convertsM`

For a composite gadget, prove it tactically (see [proving-circuits.md](proving-circuits.md)).
For a primitive that emits a gate, split it into the three field lemmas and assemble with a
structure instance — this is the pattern in
[FUnit/eq0.lean](../Clap/Lang/Gate/eq0.lean) and [FB/isZero.lean](../Clap/Lang/Gate/isZero.lean):

```lean
lemma convertsM
  [p.AtLeastTwo] {state} {a : F p} {a_val : ZMod p}
  (h_a : Converts F.conversion state a a_val)
:
  ConvertsM FUnit.conversion (eq0 a) state () (a_val = 0)
where
  result := converts
  wellFormed := wellFormed h_a
  constraints := constraints h_a
```

When the constraint condition is `True` and your `constraints` lemma proves the bare
proposition rather than the `↔`, wrap it: `constraints := iff_true_intro (constraints h_a)`
(as `isZero` does).

## Iterating gadgets need rewrite lemmas *first*

If the body is a `mapM` or `foldlM`, write these before attempting the spec — the proof cannot
proceed without them.

1. An `_aux` definition generalised over the starting index, or a `'` variant generalised over
   the accumulator.
2. `@[simp, grind =]` recursion equations `<name>_zero` and `<name>_succ`. The idiom, from
   [OneHotRaw.lean:22-46](../Clap/Lang/Data/FArray/OneHotRaw.lean#L22-L46), is `conv_lhs => unfold
   <name>`, rewrite with the container's `range'_succ` / `mapM_cons` / `mapM_append` lemma,
   then `rw [←<name>.eq_def]`.
3. If the proof will be easier over lists (it usually is — `List` has far more Mathlib support
   than `Vector` and no length index to fight), a `List`-valued mirror, the bridging
   `Vector.toList <$> vec = list` lemma, and the four transfer lemmas for
   `getResult` / `getCircuit` / `getHashConsState` / `getNumAlloc`. All of these are one-liners
   once the bridge exists:
   ```lean
   @[simp, grind _=_]
   lemma getCircuit_oneHotRaw_aux :
     (oneHotRaw_aux (p := p) start len idx).getCircuit numAlloc σ =
     (oneHotRaw'_aux start len idx).getCircuit numAlloc σ := by
     rw [←toList_map_oneHotRaw_aux_eq_oneHotRaw'_aux, ClapM.getCircuit_map]
   ```

Some of this scaffolding is now unnecessary. [Clap/Lang/Core/Combinators/](../Clap/Lang/Core/Combinators/)
has reusable `ConvertsM` lemmas for the two common iteration shapes, both generic in the
*element* conversion, so one lemma serves bit vectors (`FB.conversion`), field vectors
(`F.conversion`) and zipped pairs of vectors (`FPair.conversion`, via `FVec.converts_zip`):

| Lemma | For |
|---|---|
| `convertsM_foldlM` | `Vector.foldlM` whose step asserts nothing |
| `convertsM_foldlM_constraints` | `Vector.foldlM` whose step asserts; the fold's constraint is `∀ i, …` |
| `convertsM_ofFnM` | `Vector.ofFnM`, building a vector position by position — each position's action must hold in *every* state, so constants only |
| `convertsM_mapM` | `Vector.mapM` of a field-valued gadget over a vector of inputs; the result is an `FVec` |
| `convertsM_mapM_constraints` | `Vector.mapM` of a gadget with any result conversion `C_out`, whose step may assert; the result is a `C_out.vector k` and the constraint is `∀ i, …` |

Reach for those before hand-rolling an induction. `dotProduct`, `FArray.bits2num`,
`FArray.eq`, `FArray.assert_eq`, `FVec.eq`, `FString.ofString` and the `Packing` gadgets are
all built on them. `OneHotRaw.lean` predates them and still carries its own ~120 lines;
`FArray/sum.lean` likewise. There is still no `forIn` combinator. A `mapM` whose step returns a
vector goes through `convertsM_mapM_constraints`, whose result conversion is `Conversion.vector`
([Convert/Vector.lean](../Clap/Model/Convert/Vector.lean)); `FArray.converts_flatten` then turns a
vector of bit vectors into one. `Packing.bytes2BigEndianBits` is built that way.

## Templates

### Skeleton A — straight-line, no assertion

Reproduces [FB/not.lean](../Clap/Lang/Core/FB/not.lean) almost exactly.

```lean
import Clap.Lang.F.mkF
import Clap.Lang.F.mkSub

namespace Clap.Lang

variable {p : ℕ}

def <NAME> (a : FB p) : ClapM p (FB p) := do
  let one ← mkF 1
  one - a          -- the operator; `p` comes from the operands (`one : F p`, `a : FB p`)

namespace <NAME>

lemma convertsM
  [p.AtLeastTwo]
  {state : ClapMState p}
  {a : FB p}
  {a_val : Bool}
  (h_a : Converts FB.conversion state a a_val)
:
  ConvertsM FB.conversion (<NAME> a) state (!a_val) True
:= by
  unfold <NAME>
  step mkF.convertsM as one
  have h_a_f := F.converts_of_FB_converts h_a
  -- note the asymmetry: the definition wrote `one - a`, the proof names `mkSub.convertsM`
  have h_sub := FB.convertsM_of_F_convertsM (mkSub.convertsM h_one h_a_f)
  apply convertsM_of_convertsM (h_sub _)
  . grind                      -- value equality
  . trivial                    -- constraints ↔
  . cases a_val <;> simp       -- the `val.val < 2` side condition of convertsM_of_F_convertsM

end Clap.Lang.<NAME>
```

### Skeleton B — asserts something, ends in `return`

Follows [FArray/singleOneArray.lean](../Clap/Lang/Data/FArray/singleOneArray.lean).

```lean
namespace Clap.Lang

variable {p : ℕ}

section <NAME>

/-- <what it computes>. Only satisfiable when <condition>. -/
def <NAME> [p.AtLeastTwo] (<args>) : ClapM p <T> := do
  let out ← <sub-gadget> …
  let s ← <sub-gadget> out
  assert_eq s (←mkF 1)
  return out

namespace <NAME>

lemma convertsM
  [p.AtLeastTwo]
  {state} {<args>} {<arg>_val}
  (h_<arg> : Converts <C>.conversion state <arg> <arg>_val)
  (h_side : <side condition>)
:
  ConvertsM <C>.conversion (<NAME> <args>) state <IDEAL> <CONSTRAINTS>
:= by
  unfold <NAME>
  step <sub>.convertsM h_<arg> h_side as out
  step <sub>.convertsM h_out as s
  step mkF.convertsM as one
  step assert_eq.convertsM h_s h_one as assert_eq
  apply convertsM_pure
  . exact h_out            -- the returned value converts
  . <soundness>            -- emitted constraint ⟹ <CONSTRAINTS>
  . <completeness>         -- <CONSTRAINTS> ⟹ emitted constraint

end <NAME>
end <NAME>

end Clap.Lang
```

### Skeleton C — a gate primitive from scratch

Follows [FUnit/eq0.lean](../Clap/Lang/Gate/eq0.lean).

```lean
import Clap.Model.Convert.Specialised

namespace Clap.Lang

variable {p : ℕ}

namespace <NAME>

lemma wellFormed {e! : ExprRef} {state} {value : ZMod p}
  (h : Converts F.conversion state e! value)
: (<NAME> e!).wellFormed state.numAlloc state.varStore state.σ
:= by
  obtain ⟨h_varSet, h_wellFormed, h_result⟩ := h
  simp at *
  apply wellFormed_<NAME>        -- from Clap/Model/eDSL.lean
  . grind
  . have : [state.varStore|⦃e!, state.σ⦄].isSome = true := by grind
    grind
  . grind

lemma converts … : Converts <C>.conversion ((<NAME> a).getState state)
                                           ((<NAME> a).getResult state.numAlloc state.σ) <IDEAL> := …

lemma constraints (h_a : Converts F.conversion state a a_val)
: ((<NAME> a).runAndEval state.numAlloc state.varStore state.σ).2.constraints ↔ <CONSTRAINTS> := …

lemma convertsM … : ConvertsM <C>.conversion (<NAME> a) state <IDEAL> <CONSTRAINTS>
where
  result := converts h_a
  wellFormed := wellFormed h_a
  constraints := constraints h_a

end <NAME>

end Clap.Lang
```

## Checklist

- [ ] File is at `Clap/Lang/<Type>/<name>.lean`, in `namespace Clap.Lang`, with
      `variable {p : ℕ}`.
- [ ] Imported from `Clap/Lang/All.lean` **and** `Clap.lean`, alphabetically in both.
- [ ] Signature uses `F p` / `FB p` / `FArray p k` / `FList p`, not `ExprRef`.
- [ ] Every constant goes through `mkF`; every arithmetic node is a bind, spelled `←(a + b)`,
      `←(a - b)`, `←(a * b)`.
- [ ] Exactly one lemma named `convertsM`, in `namespace <name>`.
- [ ] One `h_<arg> : Converts …` hypothesis per circuit-valued input.
- [ ] Slot 5 is `True` **only** if the gadget cannot fail to be satisfied.
- [ ] Parameter bounds are hypotheses, not `assert!` and not part of slot 5.
- [ ] No `_spec` / `_sound` / `_complete` / `_correct` names anywhere.
- [ ] If iterating: `_zero` / `_succ` recursion equations exist and are `@[simp, grind =]`.
- [ ] `lake build` passes.
