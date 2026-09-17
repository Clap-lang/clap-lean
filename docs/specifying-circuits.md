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
3. **`namespace Clap.Lang`**, then `variable {p : ℕ}`. (`Clap/Lang/FB/and.lean` uses
   `Clap.Lang.FB`; either is acceptable, match the neighbours.)
4. **You almost certainly do not need `open HashConsM`.** `mkF`/`mkAdd`/`mkSub`/`mkMul` are
   `Clap.Lang.*` ([F/mkAdd.lean](../Clap/Lang/F/mkAdd.lean) and siblings) and are already in
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
   [F/conditionalSwap.lean:10-13](../Clap/Lang/F/conditionalSwap.lean#L10-L13) is the model:

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
| `mkF a` | [F/mkF.lean](../Clap/Lang/F/mkF.lean) | `ClapM p (F p)` | `a` | `True` |
| `mkAdd a b` — write `←(a + b)` | [F/mkAdd.lean](../Clap/Lang/F/mkAdd.lean) | `ClapM p (F p)` | `a_val + b_val` | `True` |
| `mkSub a b` — write `←(a - b)` | [F/mkSub.lean](../Clap/Lang/F/mkSub.lean) | `ClapM p (F p)` | `a_val - b_val` | `True` |
| `mkMul a b` — write `←(a * b)` | [F/mkMul.lean](../Clap/Lang/F/mkMul.lean) | `ClapM p (F p)` | `a_val * b_val` | `True` |
| `ofUInt8 u` | [F/ofUInt8.lean](../Clap/Lang/F/ofUInt8.lean) | `ClapM p (F p)` | `(u.toNat : ZMod p)` | `True` |
| `ofChar c` | [F/ofChar.lean](../Clap/Lang/F/ofChar.lean) | `ClapM p (F p)` | `(c.toUInt8.toNat : ZMod p)` | `True` |
| `conditionalSwap sel a b` | [F/conditionalSwap.lean](../Clap/Lang/F/conditionalSwap.lean) | `ClapM p (F p)` | `if sel_val then a_val else b_val` | `True` |
| `dotProduct a b` | [F/dotProduct.lean](../Clap/Lang/F/dotProduct.lean) | `ClapM p (F p)` | `(a_vals.zip b_vals).foldl (fun acc xy ↦ acc + xy.1 * xy.2) 0` | `True` |
| `isZero a` | [FB/isZero.lean](../Clap/Lang/FB/isZero.lean) | `ClapM p (FB p)` | `a_val == 0` | `True` |
| `not a` | [FB/not.lean](../Clap/Lang/FB/not.lean) | `ClapM p (FB p)` | `!a_val` | `True` |
| `FB.and a b` | [FB/and.lean](../Clap/Lang/FB/and.lean) | `ClapM p (FB p)` | `a_val && b_val` | `True` |
| `FB.or a b` | [FB/or.lean](../Clap/Lang/FB/or.lean) | `ClapM p (FB p)` | `a_val \|\| b_val` | `True` |
| `FB.xor a b` | [FB/xor.lean](../Clap/Lang/FB/xor.lean) | `ClapM p (FB p)` | `a_val ^^ b_val` | `True` |
| `FB.ofBool b` | [FB/ofBool.lean](../Clap/Lang/FB/ofBool.lean) | `ClapM p (FB p)` | `b` | `True` |
| `eq a b` | [FB/eq.lean](../Clap/Lang/FB/eq.lean) | `ClapM p (FB p)` | `a_val == b_val` | `True` |
| `FB.eq a b` (Bool-typed) | [FB/eqBool.lean](../Clap/Lang/FB/eqBool.lean) | `ClapM p (FB p)` | `a_val == b_val` | `True` |
| `eq0 a` | [FUnit/eq0.lean](../Clap/Lang/FUnit/eq0.lean) | `ClapM p Unit` | `()` | `a_val = 0` |
| `assert_eq a b` | [FUnit/assert_eq.lean](../Clap/Lang/FUnit/assert_eq.lean) | `ClapM p Unit` | `()` | `a_val = b_val` |
| `FB.assert_eq a b` (Bool-typed) | [FB/assert_eq.lean](../Clap/Lang/FB/assert_eq.lean) | `ClapM p Unit` | `()` | `a_val = b_val` |
| `assert a` | [FB/assert.lean](../Clap/Lang/FB/assert.lean) | `ClapM p Unit` | `()` | `a_val = true` |
| `FB.assertBool f` | [FB/assertBool.lean](../Clap/Lang/FB/assertBool.lean) | `ClapM p Unit` | `()` | `f_val = 0 ∨ f_val = 1` |
| `FB.conditionallyAssert a c` | [FB/conditionallyAssert.lean](../Clap/Lang/FB/conditionallyAssert.lean) | `ClapM p Unit` | `()` | `a_val = true → c_val = true` |
| `guardedEq0 g c` | [FUnit/guardedEq0.lean](../Clap/Lang/FUnit/guardedEq0.lean) | `ClapM p Unit` | `()` | `g_val = true → c_val = 0` |
| `guardedAssertEq g a b` | [FUnit/guardedAssertEq.lean](../Clap/Lang/FUnit/guardedAssertEq.lean) | `ClapM p Unit` | `()` | `g_val = true → a_val = b_val` |
| `FArray.sum vals` | [FArray/sum.lean](../Clap/Lang/FArray/sum.lean) | `ClapM p (F p)` | `(vals.map (if · then 1 else 0)).sum` | `True` |
| `FArray.sum' init vals` | [FArray/sum.lean](../Clap/Lang/FArray/sum.lean) | `ClapM p (F p)` | as above | `True` |
| `oneHotRaw len idx` | [FArray/OneHotRaw.lean](../Clap/Lang/FArray/OneHotRaw.lean) | `ClapM p (FArray p len)` | `Vector.ofFn (·.val == idx_val.val)` | `True` |
| `singleOneArray len idx` | [FArray/singleOneArray.lean](../Clap/Lang/FArray/singleOneArray.lean) | `ClapM p (FArray p len)` | as above | `idx_val.val < len` |
| `FArray.default w` | [FArray/default.lean](../Clap/Lang/FArray/default.lean) | `ClapM p (FArray p w)` | `Vector.replicate w false` | `True` |
| `FArray.ofBitVec bv` | [FArray/ofBitVec.lean](../Clap/Lang/FArray/ofBitVec.lean) | `ClapM p (FArray p w)` | `Vector.ofFn (bv[·])` | `True` |
| `FArray.zeroExtend v w'` | [FArray/zeroExtend.lean](../Clap/Lang/FArray/zeroExtend.lean) | `ClapM p (FArray p (w+w'))` | `vals ++ Vector.replicate w' false` | `True` |
| `FArray.eq a b` | [FArray/eq.lean](../Clap/Lang/FArray/eq.lean) | `ClapM p (FB p)` | `decide (a_vals = b_vals)` | `True` |
| `FArray.assert_eq a b` | [FArray/assert_eq.lean](../Clap/Lang/FArray/assert_eq.lean) | `ClapM p Unit` | `()` | `∀ i : Fin w, a_vals[i] = b_vals[i]` |
| `FArray.bits2num bits` | [FArray/bits2num.lean](../Clap/Lang/FArray/bits2num.lean) | `ClapM p (F p)` | `FArray.toNum bits_val` | `True` |
| `FBV8.ofUInt8 u` | [FArray/Widths.lean](../Clap/Lang/FArray/Widths.lean) | `ClapM p (FBV8 p)` | `Vector.ofFn (u.toBitVec[·])` | `True` |
| `F32.default` | [FArray/Widths.lean](../Clap/Lang/FArray/Widths.lean) | `ClapM p (F32 p)` | `Vector.replicate 32 false` | `True` |
| `F32.ofUInt32 u` | [FArray/Widths.lean](../Clap/Lang/FArray/Widths.lean) | `ClapM p (F32 p)` | `Vector.ofFn (u.toBitVec[·])` | `True` |
| `F32.ofFBV8 u8` | [FArray/Widths.lean](../Clap/Lang/FArray/Widths.lean) | `ClapM p (F32 p)` | `vals ++ Vector.replicate 24 false` | `True` |
| `F32.assert_eq a b` | [FArray/Widths.lean](../Clap/Lang/FArray/Widths.lean) | `ClapM p Unit` | `()` | `∀ i : Fin 32, a_vals[i] = b_vals[i]` |
| `FVec.eq a b` | [FVec/eq.lean](../Clap/Lang/FVec/eq.lean) | `ClapM p (FB p)` | `decide (a_vals = b_vals)` | `True` |
| `FString.ofString s` | [FString/ofString.lean](../Clap/Lang/FString/ofString.lean) | `ClapM p (FString p w)` | `s` | `True` |
| `FString.isPaddedOf a b` | [FString/isPaddedOf.lean](../Clap/Lang/FString/isPaddedOf.lean) | `ClapM p (FB p)` | `decide (encodeV w a_val = encodeV w b) && (a_val.length == b.length)` | `True` |
| `num2bits w e` | [FArray/num2bits.lean](../Clap/Lang/FArray/num2bits.lean) | `ClapM p (FArray p w)` | `num2bitsLsbPureV w e_val` as bits | `True` — see the warning below |
| `lessThan w a b` | [F/lessThan.lean](../Clap/Lang/F/lessThan.lean) | `ClapM p (FB p)` | `a_val.val < b_val.val` | `True` |
| `lessEqThan`, `greaterThan`, `greaterEqThan` | [F/lessThan.lean](../Clap/Lang/F/lessThan.lean) | `ClapM p (FB p)` | the obvious variants | `True` |
| `assert_range w e` | [FUnit/assert_range.lean](../Clap/Lang/FUnit/assert_range.lean) | `ClapM p Unit` | `()` | `True` — see the warning below |
| `F8.eq`, `F8.lessThan`, `F8.greaterThan`, `F8.lessEqThan`, `F8.greaterEqThan` | [F8/F8.lean](../Clap/Lang/F8/F8.lean) | `ClapM p (FB p)` | byte-width delegations to the above at `w = 8`, stated over `UInt8` | `True` |
| `FBitVec.binSum a b` | [FBitVec/binSum.lean](../Clap/Lang/FBitVec/binSum.lean) | `ClapM p (FBitVec p (w+1))` | low `w+1` bits of `toNum a_vals + toNum b_vals` | `True` |
| `F32.add a b` | [FArray/Widths.lean](../Clap/Lang/FArray/Widths.lean) | `ClapM p (F32 p)` | the above, `take 32` — i.e. wrapping 32-bit addition | `True` |
| `FBV8.ofF`, `F32.ofF`, `F64.ofF` | [FArray/Widths.lean](../Clap/Lang/FArray/Widths.lean) | `ClapM p (FArray p w)` | `num2bits` at `w = 8`/`32`/`64` | `True` |
| `F8.isWhitespace c` | [F8/isWhitespace.lean](../Clap/Lang/F8/isWhitespace.lean) | `ClapM p (FB p)` | `c_val` is space, tab, CR or LF | `True` |
| `arraySelector len s e` | [FArray/arraySelector.lean](../Clap/Lang/FArray/arraySelector.lean) | `ClapM p (FArray p len)` | 1s on `[startIdx, endIdx)` | index bounds |
| `singleEndArray len idx` | [FArray/singleEndArray.lean](../Clap/Lang/FArray/singleEndArray.lean) | `ClapM p (FArray p len)` | 1s from `idx` on | `idx_val.val < len` |
| `FArray.xor a b` | [FArray/xor.lean](../Clap/Lang/FArray/xor.lean) | `ClapM p (FArray p k)` | pointwise `xor` | `True` |
| `FArray.xorScan a` | [FArray/xorScan.lean](../Clap/Lang/FArray/xorScan.lean) | `ClapM p (FArray p k)` | running `xor` prefix scan | `True` |
| `FBitVec.eq a b` | [FBitVec/eq.lean](../Clap/Lang/FBitVec/eq.lean) | `ClapM p (FB p)` | `a_val == b_val` | `True` |
| `FBitVec.assert_eq a b` | [FBitVec/assert_eq.lean](../Clap/Lang/FBitVec/assert_eq.lean) | `ClapM p Unit` | `()` | `a_val = b_val` |

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
for `convertsM_foldlM`, `convertsM_foldlM_constraints` and `convertsM_ofFnM`.

Not yet wrapped: **`share`** and **`fpmul`**. Both are fully implemented *gates* — they are in
[eDSL.lean](../Clap/eDSLState/eDSL.lean) with the complete `wellFormed_*` / `eval_edsl_*` /
`getResult_*` / `getVarStore_*` / `getCircuit_*` family, and both have `ConstraintSystem/` and
`WitnessGenerator/` modules. What neither has is a `Clap/Lang/` wrapper carrying a `convertsM`,
and that is what your gadget needs; write it first. `num2bits` used to be on this list and is
the bottleneck for every comparison, range check, packing and hashing gadget; it is now
wrapped, along with the whole comparison family built on it.

### ⚠ `num2bits` asserts nothing in the model, but range-checks in the circuit

`num2bits.convertsM`'s constraints slot is `True`. That is not an oversight in the lemma: the
evaluation semantics `stepNum2bits`
([CircuitEvalSt.lean:412](../Clap/eDSLState/CircuitEvalSt.lean#L412)) stores the *truncated*
low `w` bits of its input and `constraints_stepNum2bits` contributes only allocatedness. So in
the model `num2bits` is a total, truncating decomposition.

The compiled circuit is stronger. The lowering in
[ConstraintSystem/num2bits.lean](../Clap/eDSLState/ConstraintSystem/num2bits.lean) emits
`bits2num(bits) - expr` alongside the booleanity constraints, and is unsatisfiable when
`e ≥ 2^w`. The smoke tests at the bottom of
[FUnit/assert_range.lean](../Clap/Lang/FUnit/assert_range.lean) demonstrate this: a one-gate
`assert_range 4` accepts `5` and `15` and rejects `16`, `20` and `31`.

Two consequences. `assert_range`'s slot 5 is `True` even though the old model's `num2bits`
returned `none` out of range — the condition has nowhere honest to live until the semantics
change. And `binSum` / `F32.add` get `True` and *wrapping* arithmetic for free, which is what
the old model's own `(2^32 - 1) + 1 = 0` vector already said.

Closing the gap means strengthening `stepNum2bits` to carry the range condition and reproving
`num2bits.constraints` as `e_val.val < 2 ^ w`; `lessThan.convertsM` and everything built on it
would then have to discharge it. That is a change to the core semantics, not to a gadget.

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
[FUnit/eq0.lean](../Clap/Lang/FUnit/eq0.lean) and [FB/isZero.lean](../Clap/Lang/FB/isZero.lean):

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
   [OneHotRaw.lean:22-46](../Clap/Lang/FArray/OneHotRaw.lean#L22-L46), is `conv_lhs => unfold
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

Some of this scaffolding is now unnecessary. [Clap/Lang/Combinators/](../Clap/Lang/Combinators/)
has reusable `ConvertsM` lemmas for the two common iteration shapes, both generic in the
*element* conversion, so one lemma serves bit vectors (`FB.conversion`), field vectors
(`F.conversion`) and zipped pairs of vectors (`FPair.conversion`, via `FVec.converts_zip`):

| Lemma | For |
|---|---|
| `convertsM_foldlM` | `Vector.foldlM` whose step asserts nothing |
| `convertsM_foldlM_constraints` | `Vector.foldlM` whose step asserts; the fold's constraint is `∀ i, …` |
| `convertsM_ofFnM` | `Vector.ofFnM`, building a vector position by position |

Reach for those before hand-rolling an induction. `dotProduct`, `FArray.bits2num`,
`FArray.eq`, `FArray.assert_eq`, `FVec.eq` and `FString.ofString` are all built on them.
`OneHotRaw.lean` predates them and still carries its own ~120 lines; `FArray/sum.lean` likewise.
There is still no `forIn` combinator, and no `mapM` one beyond `ofFnM`.

## Templates

### Skeleton A — straight-line, no assertion

Reproduces [FB/not.lean](../Clap/Lang/FB/not.lean) almost exactly.

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

Follows [FArray/singleOneArray.lean](../Clap/Lang/FArray/singleOneArray.lean).

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

Follows [FUnit/eq0.lean](../Clap/Lang/FUnit/eq0.lean).

```lean
import Clap.eDSLState.Convert.Specialised

namespace Clap.Lang

variable {p : ℕ}

namespace <NAME>

lemma wellFormed {e! : ExprRef} {state} {value : ZMod p}
  (h : Converts F.conversion state e! value)
: (<NAME> e!).wellFormed state.numAlloc state.varStore state.σ
:= by
  obtain ⟨h_varSet, h_wellFormed, h_result⟩ := h
  simp at *
  apply wellFormed_<NAME>        -- from Clap/eDSLState/eDSL.lean
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
