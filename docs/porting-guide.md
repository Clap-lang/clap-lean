---
name: porting-guide
description: Rules for porting a CLAP gadget from the old Option/ZMod model to the new ClapM/ConvertsM model, with a worked before-and-after and an inventory of what remains.
when-to-use: You are moving a gadget out of Clap/Array.lean, Clap/Lang.lean, Clap/Packing.lean, Sha2, JWT, RSA, Poseidon, or any other file behind the "Goodbye, sweet prince" comment.
---

# Porting from the old model

Read [clap-agent-guide.md](clap-agent-guide.md), then
[specifying-circuits.md](specifying-circuits.md) and [proving-circuits.md](proving-circuits.md).
This file only covers what is *different* about a port versus writing a gadget fresh.

## State of play

Everything old is on disk and out of the build, behind a comment block at
[Clap.lean:40](../Clap.lean#L40) headed *"Goodbye, sweet prince."* Porting means **rewriting
into `Clap/Lang/`**, never editing an old file into shape.

**The `Clap/Lang.lean` trap.** The *file* `Clap/Lang.lean` (~1100 lines) is the OLD gadget
library. The *directory* `Clap/Lang/` is the new one. They share a name and nothing else. If
you find yourself reading `abbrev F p := ZMod p`, you are in the old file.

Several old files are themselves 85–90% line-commented already — `Clap/JWT.lean` (1100 of 1245
lines), `Clap/FString.lean`, `Clap/Keyless.lean`, `Clap/HashToField.lean`,
`Clap/Sha2/Keyless.lean`, `Clap/Poseidon/Poseidon.lean`. They are reference source, not working
code.

## The two shifts that cause every other difference

### 1. `F p` was a value; now it is a reference

```lean
abbrev F p := ZMod p          -- OLD: literally a field element
abbrev F (p : ℕ) := HashConsM.BoundRef p   -- NEW: an index into the expression heap
```

Old code wrote `x * (y - z) + z`, `a + b - 2*a*b`, `(a - b) * sel + b` as ordinary Lean
arithmetic — free, pure, with all of Mathlib's `CommRing (ZMod p)` available. New code must
allocate every node: `←mkMul`, `←mkSub`, `←mkAdd`.

Consequences you will hit immediately:

- **Every pure helper becomes monadic, and so does every caller.** `F.dotProduct`,
  `F.conditionalSwap`, `FB.and/or/not/xor`, `Packing.chunksToFieldElem`, `Sha2.Circuit.ch`,
  `rotR`, `shiftRight` all change type.
- **The operator instances change meaning.** Old `FB.and` was `HAnd (FB p) (FB p) (FB p)` — a
  value. New `+ - *` return `ClapM p (F p)`. Old `a &&& b &&& c` becomes three explicit binds.
  Old `FB.conditionallyAssert` is `eq0 (antecedent &&& FB.not consequent)` — one line, three
  operations, now three binds.
- **Literals need allocation.** `F.assert_eq s 1` becomes `assert_eq s (←mkF 1)`. `RSA.lean`
  has ~10 hard-coded 64-bit constants; Poseidon has ~20 000. Plan a bulk allocation helper
  (`Clap/Poseidon/NewPoseidon.lean`'s `allocateVector` is the seed) and rely on hash-consing to
  de-duplicate repeats.
- **`Coe` instances cannot survive.** Old `Coe Char (F p)`, `Coe UInt8 (F p)`,
  `Coe UInt32 (F32 p)`, `OfNat (F32 p) n`, `Inhabited (F p) := 42` all target a pure type. A
  coercion cannot produce a monadic action.

### 2. `Option` was failure; there is no failure now

Old `none` meant, indiscriminately: an out-of-range input, a violated assertion, a structurally
malformed call — **and it short-circuited**, so later gadgets never ran and never emitted
constraints.

`ClapM` cannot fail. Every action runs, every gate is emitted. Unsatisfiability is a `Prop` in
the fifth slot of `ConvertsM`. Therefore:

- **Old `foo x = none`** ⇝ new `constraints ↔ False`, or more usefully, a slot-5 condition that
  excludes that input.
- **Old `foo x = some v`** ⇝ new `result` gives `v` **and** the slot-5 condition holds.
- **Short-circuiting is gone.** Any old gadget that relied on "a failing prefix protects a
  later partial operation" must hoist that precondition into slot 5 or into an explicit
  hypothesis. `RSA_..._Verify` after `fpPow65537Mod`, and `FString.isPaddedOf.aux` on
  mismatched lengths, both do this.
- **Structural failure is not constraint failure.** Old `fpMul` returned `none` when
  `a.length ≠ k`. That is a type-level condition: express it with `Vector ExprRef k` (as
  `Gate.fpmul` already does), not as a runtime check.

## Translation table

| Old | New |
|---|---|
| `def g … : Option (F p)` | `def g … : ClapM p (F p)` |
| `Option`'s `do`; `none` = reject | `ClapM`'s `do`; rejection lives in `ConvertsM`'s slot 5 |
| `F p = ZMod p`, a value | `F p = BoundRef p`, a reference; the value is the spec's slot 4 |
| `a + b`, `a * b` (pure) | `←(a + b)`, `←(a * b)` |
| `(1 : F p)` | `←mkF 1` |
| `FB.and a b` (pure, `&&&`) | `←FB.and a b` |
| `FB.not a` (pure) | `←not a` |
| `FB.or`, `FB.xor` (pure, `\|\|\|`, `^^^`) | not yet ported — write them as `ClapM p (FB p)` |
| `F.assert_eq a b` | `assert_eq a b` |
| `F.eq a b` | `eq a b` |
| `isZero e` | `isZero e` |
| `FB.assert a` | `assert a` |
| `Vector (FB p) len` | `FArray p len` |
| `List (FB p)` | `FList p` |
| `Vector.mapM` / `foldlM` over `Option` | the same over `ClapM`, **plus** `_zero`/`_succ` rewrite lemmas |
| `assert! w ≤ minBits p` | an explicit hypothesis `(h_w : …)` on `convertsM` |
| `v[i]!` with `Inhabited (F p) := 42` | `v[i]` with a `Fin` index or a proof obligation |
| `partial def` | structural recursion, or `Fin.foldl` |
| `[Fact (Primes.fits p 8)]` | `[p.AtLeastTwo]` plus explicit bounds like `(h_len : len < p)`; use `[Fact (Nat.Prime p)]` only where the maths genuinely needs a field — see [FB/assertBool.lean](../Clap/Lang/FB/assertBool.lean), whose soundness is `mul_eq_zero` |
| `example : g … = some v := by native_decide` | the content of slots 4 and 5 of `lemma convertsM` |
| doc comment "only satisfiable when `0 ≤ idx < len`" | slot 5: `idx_val.val < len` |

## Worked example: `singleOneArray`

The one gadget that exists in both models. Old,
[Clap/Array.lean:11-19](../Clap/Array.lean#L11-L19):

```lean
private def oneHotRaw (len : ℕ) (idx : F p) : Option (Vector (FB p) len) :=
  (Vector.range len).mapM (fun (i:ℕ) ↦ F.eq idx i)

/-- Returns a one-hot bit mask of length `len` with a 1 at index `idx` and 0s elsewhere.
    Only satisfiable when `0 ≤ idx < len`. -/
def singleOneArray (len : ℕ) (idx : F p) : Option (Vector (FB p) len) := do
  let out ← oneHotRaw len idx
  let s : F p := out.foldl (fun acc b ↦ acc + b) 0   -- pure fold, no monad
  F.assert_eq s 1                                    -- bare literal
  return out
```

verified by nine `native_decide` examples:

```lean
example : FArray.singleOneArray (p := p) 4 0 = some #v[1,0,0,0] := by native_decide
example : FArray.singleOneArray (p := p) 4 3 = some #v[0,0,0,1] := by native_decide
example : FArray.singleOneArray (p := p) 4 4 = none := by native_decide
```

New, [Clap/Lang/FArray/singleOneArray.lean](../Clap/Lang/FArray/singleOneArray.lean):

```lean
def singleOneArray [p.AtLeastTwo] (len : ℕ) (idx : F p) : ClapM p (FArray p len) := do
  let out ← oneHotRaw len idx
  let s : F p ← out.sum          -- monadic fold
  assert_eq s (←mkF 1)           -- literal allocated
  return out

lemma convertsM
  [p.AtLeastTwo] {len : ℕ} {idx : F p} {state} {idx_val : ZMod p}
  (h_idx : Converts F.conversion state idx idx_val)
  (h_len : len < p)                                            -- ← was implicit
:
  ConvertsM FArray.conversion (singleOneArray len idx) state
    (Vector.ofFn (λ x => x.val == idx_val.val))                -- ← was the `= some #v[…]` tests
    (idx_val.val < len)                                        -- ← was the `= none` tests
```

Read the last two lines carefully: **the old `native_decide` corpus is exactly the content of
the new specification.** The `= some #v[…]` cases are instances of slot 4; the `= none` cases
are the negation of slot 5. When porting, mine the old tests for the spec — they are the best
available oracle for what the gadget was supposed to do.

Note also that `oneHotRaw` needed 120 lines of scaffolding it did not need before: an `_aux`
generalised over the start index, a `List` mirror, `_zero`/`_succ` recursion equations, and
four `get*` transfer lemmas. Budget for that on any iterating gadget.

## Porting checklist

1. Read the old definition **and its `native_decide` tests**; the tests are the spec.
2. Extract every doc-comment precondition and every `assert!` into either slot 5 (if it is a
   condition on *values*) or an explicit hypothesis (if it is a condition on *parameters*).
3. Rewrite the body: monadic arithmetic, `mkF` for constants, `←` on every helper that is now
   monadic.
4. Replace `v[i]!` with a bounded index. The old `Inhabited (F p) := 42` made out-of-bounds
   reads silently produce the constant `42`; in the new model that silently allocates a bogus
   expression. `Sha2.Basic.schedule`'s `acc[i - 16]!` inside a `partial def` is the worst case.
5. Split any `mapM`/`foldlM` into an `_aux` definition and prove its `_zero`/`_succ` equations
   before touching the spec.
6. State `convertsM`, then prove it. See [proving-circuits.md](proving-circuits.md).
7. Register the file in `Clap/Lang/All.lean` and `Clap.lean`.
8. Carry the old test vectors over as comments. There is no way to re-run them.

## Blockers — do not start these yet

**Missing primitives.** These gates exist but have no `Clap/Lang/` wrapper and no `convertsM`:

- **`num2bits`** — `Gate.num2bits` exists, `Circuit.toCs` handles it,
  `eDSLState/ConstraintSystem/num2bits.lean` has the lowering. **Every** comparison, range
  check, packing, base64 and SHA gadget bottoms out here. Port this first; it unblocks the most.
- **`share`** — needed for degree reduction (`Sha2.Circuit.maj`/`xor3`,
  `Base64Len.base64UrlDecodedLength`).
- **`fpmul`** — `Gate.fpmul` exists but `Circuit.toCs`'s branch is `sorry`,
  `ConstraintSystem/fpMul.lean`'s `check_lt_impl` is a stub, and `num_constraints .fpmul = 42`
  is a placeholder. RSA is blocked on it.

**No back end.** `ConstraintSystem.lean` and `WitnessGenerator.lean` are not imported and do
not compile, and R1CS serialisation (`Clap/Quadratic.lean` + `R1Serialize/`) has no new-model
counterpart. So there is no executable path and no smoke test: a `convertsM` proof is your only
evidence.

**No iteration combinators.** There is no reusable `mapM`/`foldlM`/`forIn` `ConvertsM` lemma
library. Old code uses `for … in … do` inside `Option` freely. If you are the third person to
copy `OneHotRaw.lean`'s scaffolding, build the combinator instead of copying.

**Conversions that do not exist yet.** The five conversions
(`F`/`FB`/`FUnit`/`FArray`/`FList`) are all fixed-length and element-wise. Two old shapes do
not fit:

- `FString` / `PaddedVector` bundles `data : Vector (α p) w` with `len : F p`, and its natural
  `IdealT` is a variable-length `String` behind a fixed-length representation.
- `Sha2`'s `Hash = Vector t.U32 8` where each `U32` is itself `Vector (FB p) 32` — a *nested*
  conversion, which `FArray.conversion : Conversion p (Vector (FB p) k)` cannot express.

Design these conversions deliberately before porting anything that needs them.

## Suggested order

**Now** (all dependencies present in `Clap/Lang/`):

The whole old `FB` namespace is **done** — `or`, `xor`, `ofBool`, `assertBool`, `assert_eq`,
`conditionallyAssert` and the Bool-typed `eq` now live in `Clap/Lang/FB/` alongside the
original `and`, `assert`, `eq`, `isZero`, `not`. `FB.true` / `FB.false` were deliberately not
ported (they would shadow the `Bool` literals; use `ofBool`), and the `Spec.FB` layer is
superseded by `FB.conversion`. Use those files as the worked reference for this table's
remaining rows.

| Gadget | Old location | Note |
|---|---|---|
| `F.dotProduct` | `Clap/Lang.lean` | monadic `zipWith`+`foldl`; reuse `FArray.sum'` |
| `F.guardedEq0`, `F.guardedAssertEq` | `Clap/Lang.lean` | gated assertions |
| `F.conditionalSwap` | `Clap/Lang.lean` | mux `(a-b)*sel + b` |
| `singleEndArray` | `Clap/Array.lean` | one-hot asserting `s² = s` |
| `selectArrayValue` | `Clap/Array.lean` | `dotProduct` of `singleOneArray` with the array |
| `leftArraySelector`, `rightArraySelector` | `Clap/Array.lean` | need `Vector.scanl`/`scanr` analogues |
| `arraySelectorComplex` | `Clap/Array.lean` | after the two selectors |

**After `num2bits` lands**: `F.assert_range`, `F.lessThan` / `lessEqThan` / `greaterThan` /
`greaterEqThan`, `arraySelector`, `FBitVec.*`, `F8.lessThan`, `F32.*`, all of
`Clap/Packing.lean`, all of `Clap/Base64Len.lean`.

**After `fpmul` lands**: `Clap/RSA.lean`.

**After nested/variable-length conversions are designed**: `Clap/Sha2/*` (note
`Sha2/Basic.lean` is already monad-polymorphic over `[Monad m]` and typeclass-parameterised
over the word representation — it is the most portable old code in the repo),
`Clap/FString.lean`, `Clap/HashToField.lean`, `Clap/JWT.lean`, `Clap/Keyless.lean`.

**Retired, do not port**: `Clap/Circuit.lean` (PHOAS syntax), `Clap/Simulation.lean`,
`Clap/Compilation.lean`, `Clap/Compiler/*` (the `#compile` reifier), `Clap/Milestone.lean`.
`ClapM` builds the circuit by execution, so none of the reification machinery is needed. Note
that `Cfold` and `Dedup` are subsumed by hash-consing at construction time — but this is a
decision worth confirming with a maintainer rather than assuming, and `Dedup.dedup_sem_pre` was
`sorry` in the old model anyway.

**Reuse verbatim**: `Clap/BitVec.lean` (`num2bitsLsbPure(V)`, `bits2num(V)` and their lemmas),
`Clap/Primes.lean`, and most of `Clap/Wheels.lean` (`Vector.scanl`/`scanr`, `minBits`,
`limbsToNat`, `natToLimbs(V)`, `toChunks`, `ZMod.val_sum`). These are model-agnostic
mathematics. Note `Fact (Nat.Prime goldilocks)` and `Fact (Nat.Prime bn254)` are `sorry`'d in
`Clap/Primes.lean`; anything requiring primality inherits that.

## Traps

- **Two byte encodings coexisted.** `F8 p = ZMod p` (a byte as one field element) and
  `FBV8 p = Vector (FB p) 8` (a byte as eight bit-cells). Sha2 used the latter, JWT/Keyless the
  former, and the old code carried a comment warning that typeclass resolution mixes them up.
  With `F p = BoundRef p` this gets *worse*: `F p`, `FB p`, `F8 p` are now all the same
  underlying type, and the intended invariant lives only in whichever `Conversion` you cite at
  proof time. Consider real `structure` wrappers before porting `Sha2` or `Packing`.
- **Dependent casts now sit inside binds.** `F32.add`'s `min 32 (32+1) = 32`,
  `Base64Len`'s `(w*4/3)*6 = w*8`, `Sha2`'s `32 - n + n = 32`. The new model already fights
  this (`Vector.cast (show 1 + len = len + 1 by grind)` in `OneHotRaw`, `converts_cast` in
  `Convert/Base.lean`), but every cast now has `ClapM.getResult`/`getState` to be pushed
  through. Build the commuting lemmas early rather than per-gadget.
- **The old `Spec` namespace convention is dead.** Old code put spec functions in
  `Clap.Lang.Spec.X` shadowing the gadget namespace `Clap.Lang.X`, forcing `Lang.FB.assert` vs
  `assert` disambiguation inside proofs. The new model puts the spec in `ConvertsM`'s arguments
  instead. Do not reintroduce it.
- **`#compile` gave you argument serialisation for free.** It flattened user `structure`
  arguments into vectors and fixed the public-input ordering. `KeylessInput` has ~8 nested
  structures. In the new model you must write an explicit `Conversion` and a manual flattening
  convention, and re-establish the input-order contract by hand.

## Checklist

- [ ] You rewrote into `Clap/Lang/`; you did not edit an old file.
- [ ] You read the old `native_decide` tests and used them to derive slots 4 and 5.
- [ ] Every doc-comment precondition and every `assert!` is now either slot 5 or an explicit
      hypothesis — none was dropped.
- [ ] No `v[i]!` survives; indices are bounded.
- [ ] No `partial def` survives.
- [ ] Old test vectors are carried over as comments, with a note that they cannot be re-run.
- [ ] The gadget passes the [specifying-circuits.md](specifying-circuits.md) and
      [proving-circuits.md](proving-circuits.md) checklists too.
- [ ] You did not depend on `num2bits`, `share` or `fpmul` without first porting the wrapper.
