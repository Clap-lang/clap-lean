---
name: porting-guide
description: Rules for porting a CLAP gadget from the old Option/ZMod model to the new ClapM/ConvertsM model, with a worked before-and-after and an inventory of what remains.
when-to-use: You are moving a gadget out of the old/ tree — old/Clap/Array.lean, old/Clap/Lang.lean, old/Clap/Packing.lean, Sha2, JWT, RSA, or any other file there.
---

# Porting from the old model

Read [clap-agent-guide.md](clap-agent-guide.md), then
[specifying-circuits.md](specifying-circuits.md) and [proving-circuits.md](proving-circuits.md).
This file only covers what is *different* about a port versus writing a gadget fresh.

## State of play

Everything old lives in [`old/`](../old/), outside every Lake target, and is never compiled.
Porting means **rewriting into `Clap/Lang/`**, never editing a file in `old/` into shape.
Read [`old/README.md`](../old/README.md) for what is where.

The old model's *model-agnostic* maths survived the split and is live under
[`Clap/Util/`](../Clap/Util/): `BitVec.lean` (reached from `Clap/Model/CircuitEvalSt.lean`,
because the `num2bits` gate's semantics `stepNum2bits` is specified against `num2bitsLsbPureV`),
`Wheels.lean` and `Primes.lean` beneath it. Editing those changes the live build.

Several files in `old/` are themselves 85–90% line-commented already — `old/Clap/JWT.lean`
(1100 of 1245 lines), `old/Clap/FString.lean`, `old/Clap/Keyless.lean`,
`old/Clap/HashToField.lean`, `old/Clap/Sha2/Keyless.lean`, `old/Clap/Poseidon/Poseidon.lean`.
They are reference source, not working code.

## The two shifts that cause every other difference

### 1. `F p` was a value; now it is a reference

```lean
abbrev F p := ZMod p          -- OLD: literally a field element
abbrev F (p : ℕ) := HashConsM.BoundRef p   -- NEW: an index into the expression heap
```

Old code wrote `x * (y - z) + z`, `a + b - 2*a*b`, `(a - b) * sel + b` as ordinary Lean
arithmetic — free, pure, with all of Mathlib's `CommRing (ZMod p)` available. New code must
allocate every node, one bind each: `←(a * b)`, `←(a - b)`, `←(a + b)`. (`mkMul`, `mkSub`,
`mkAdd` are the same three operations under a name — they are *defined as* the operators — and
they are what the proofs cite, as `mkMul.convertsM` etc.)

Consequences you will hit immediately:

- **Every pure helper becomes monadic, and so does every caller.** `F.dotProduct`,
  `F.conditionalSwap`, `FB.and/or/not/xor`, `Packing.chunksToFieldElem`, `Sha2.Circuit.ch`,
  `rotR`, `shiftRight` all change type.
- **The operator instances change meaning, but they are still there.** `+ - *` did not go away:
  they became monadic, returning `ClapM p (F p)` instead of a value, so each one is a bind. Old
  `FB.and` was `HAnd (FB p) (FB p) (FB p)` — a value; `a &&& b &&& c` becomes three explicit
  binds. One new snag: `p` is a phantom parameter of `BoundRef`, and the operator takes it from
  its **operands** — so keep your signatures on the `F p`/`FB p` aliases. Two bare `ExprRef`
  operands silently get `Nat` addition instead, because `ExprRef` is `ℕ`, and the expected type
  will not correct it. See
  [clap-model.md §Arithmetic notation](clap-model.md#arithmetic-notation).
  Old `FB.conditionallyAssert` is `eq0 (antecedent &&& FB.not consequent)` — one line, three
  operations, now three binds.
- **Literals need allocation.** `F.assert_eq s 1` becomes `assert_eq s (←mkF 1)`. `RSA.lean`
  has ~10 hard-coded 64-bit constants; Poseidon has ~20 000. Plan a bulk allocation helper
  (`Clap/Poseidon/Poseidon.lean`'s `allocateVector` is the seed) and rely on hash-consing to
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
| `a + b`, `a - b`, `a * b` (pure) | `←(a + b)`, `←(a - b)`, `←(a * b)` — needs `p` inferable; equivalently `←mkAdd a b` etc. |
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
| `[Fact (Primes.fits p 8)]` | `[p.AtLeastTwo]` plus explicit bounds like `(h_len : len < p)`; use `[Fact (Nat.Prime p)]` only where the maths genuinely needs a field — see [FB/assertBool.lean](../Clap/Lang/Core/FB/assertBool.lean), whose soundness is `mul_eq_zero` |
| `example : g … = some v := by native_decide` | the content of slots 4 and 5 of `lemma convertsM` |
| doc comment "only satisfiable when `0 ≤ idx < len`" | slot 5: `idx_val.val < len` |

## Worked example: `singleOneArray`

The one gadget that exists in both models. Old,
[old/Clap/Array.lean:11-19](../old/Clap/Array.lean#L11-L19):

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

New, [Clap/Lang/Data/FArray/singleOneArray.lean](../Clap/Lang/Data/FArray/singleOneArray.lean):

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
7. Register the file in `Clap/Lang/All.lean` — the only index; `Clap.lean` imports that. Put it
   in the right layer: `Gate/` for a gate wrapper, `Core/` for scalars/booleans/assertions,
   `Data/` for containers.
8. Re-run the old test vectors. They *are* executable now — see §Smoke tests below. Carry over
   as comments only the ones you genuinely cannot run, and say why.

## Blockers — do not start these yet

**Missing primitives.** All five gates now have a lowering *and* a witness generator, under
`Model/ConstraintSystem/` and `Model/WitnessGenerator/`. What a gate can still be
missing is a `Clap/Lang/` wrapper with a `convertsM`:

- **`num2bits`** — **done.** [FArray/num2bits.lean](../Clap/Lang/Gate/num2bits.lean), and with
  it `F.lessThan` and the rest of the comparison family. This was the blocker that gated most
  of the backlog; it no longer is.
- **`share`** — still unwrapped. Needed for degree reduction (`Sha2.Circuit.maj`/`xor3`,
  `Base64Len.base64UrlDecodedLength`).
- **`fpmul`** — still unwrapped, and the deepest of the three. RSA is blocked on it.

Note what "unwrapped" means here: both `share` and `fpmul` are *implemented* gates. They sit in
[eDSL.lean](../Clap/Model/eDSL.lean) (lines 16 and 31) with the full `wellFormed_*` /
`eval_edsl_*` / `getResult_*` / `getVarStore_*` / `getCircuit_*` lemma family, and each has both
a `ConstraintSystem/` lowering and a `WitnessGenerator/` module. What is missing is only a
`Clap/Lang/` wrapper carrying a `convertsM` — grep finds neither name anywhere under
`Clap/Lang/`. So the work is writing that wrapper, not implementing a gate.

**The back end works.** `Circuit.toCs` lives in
[ConstraintSystem/toCs.lean](../Clap/Model/ConstraintSystem/toCs.lean) as
`_root_.Clap.Circuit.toCs (circuit) (σ) (numInputs)`, with real branches for all five gates and
a genuine `num_constraints` per gate. `Circuit.toWg` is its counterpart in
[WitnessGenerator/toWg.lean](../Clap/Model/WitnessGenerator/toWg.lean).
[Test/Backend.lean](../Clap/Test/Backend.lean) runs both end to end and `#eval`s
`wellbehaved`/`complete`/`sound`. So a `native_decide` smoke test is available, and
[Poseidon.lean](../Clap/Poseidon/Poseidon.lean) uses one to pin two circomlib hash
vectors.

One caveat: R1CS serialisation still has no new-model counterpart. `R1Serialize/R1CS.lean` (the
snarkjs `.r1cs`/`.wtns` writer) is model-agnostic and still a live Lake target, but its only
consumers — `old/Clap/Quadratic.lean` and `old/Clap/Milestone.lean` — are in `old/`.

**Public inputs are solved.** See [public-inputs.md](public-inputs.md): `AllocatedProgram`, the
`mkInput*` allocator family in
[PublicInput.lean](../Clap/Model/PublicInput.lean), and a worked end-to-end theorem. This is
what the old `#compile` reifier used to give you for free.

**Iteration combinators — partly solved.** [Clap/Lang/Core/Combinators/](../Clap/Lang/Core/Combinators/)
now has `convertsM_foldlM`, `convertsM_foldlM_constraints` and `convertsM_ofFnM`, all generic in
the element conversion. Use them instead of copying `OneHotRaw.lean`'s ~120 lines. There is
still no `forIn` combinator, and old code uses `for … in … do` inside `Option` freely.

**Conversions.** The original five (`F`/`FB`/`FUnit`/`FArray`/`FList`) are all fixed-length and
element-wise. Four more now exist, three in
[Convert/Specialised.lean](../Clap/Model/Convert/Specialised.lean) and one in
`FString/Basic.lean`:

- `F8.conversion` — `IdealT := UInt8`, a byte held in one field element, with
  `F.converts_of_F8_converts` and `F8.converts_of_F_converts` (the latter needs
  `val.val < UInt8.size`) to move between it and `F`.

- `FVec.conversion` — `Vector (F p) k` with `IdealT := Vector (ZMod p) k`. `FArray`'s ideal type
  is `Vector Bool k`, so before this there was **no way to specify a vector of general field
  elements** at all. `FVec p k` and `FArray p k` are the same underlying type; which one you
  mean is only ever the conversion you cite, so cite it deliberately.
- `FPair.conversion` — `F p × F p`. Gives a fold over `a.zip b` an element conversion, which is
  what every two-vector gadget (`dotProduct`, `FArray.eq`, `FArray.assert_eq`) needs.
- `FString.conversion` in [FString/Basic.lean](../Clap/Model/Convert/PaddedVector.lean) — the
  variable-length one, `IdealT := String`: one field element per character, zero-padded to `w`,
  then the length. The old `Spec.FString.valid` is not a separate predicate any more; it *is*
  the statement that `Converts FString.conversion` holds. It is injective only for strings
  shorter than `w` with characters under 256, `256 < p` and `w < p`, so gadgets needing
  injectivity take those as explicit hypotheses — see `isPaddedOf.encode_eq_iff`.

`PaddedVector` is now polymorphic in its element type — `PaddedVector α p w` is
`data : Vector α w` plus `len : F p`, and `FString p w = PaddedVector (F p) p w`. The keyless
inputs also use `PaddedVector (FB p) p w` for per-character flags.

Still missing: `Sha2`'s `Hash = Vector t.U32 8`, where each `U32` is itself `Vector (FB p) 32` —
a *nested* conversion, which `FArray.conversion : Conversion p (Vector (FB p) k)` cannot
express. Design it deliberately before porting anything that needs it.

## Suggested order

**Now** (all dependencies present in `Clap/Lang/`):

The whole old `FB` namespace is **done** — `or`, `xor`, `ofBool`, `assertBool`, `assert_eq`,
`conditionallyAssert` and the Bool-typed `eq` now live in `Clap/Lang/Core/FB/` alongside the
original `and`, `assert`, `eq`, `isZero`, `not`. `FB.true` / `FB.false` were deliberately not
ported (they would shadow the `Bool` literals; use `ofBool`), and the `Spec.FB` layer is
superseded by `FB.conversion`. Use those files as the worked reference for this table's
remaining rows.

The rest of the old `old/Clap/Lang.lean` is **done** too: `dotProduct`, `conditionalSwap`,
`guardedEq0`, `guardedAssertEq`, `ofUInt8`, `ofChar`,
`FArray.{default, ofBitVec, zeroExtend, bits2num, assert_eq, eq}` (the old `FBitVec.*`),
`FVec.eq`, the `F32`/`FBV8`/`F64` wrappers in `FArray/Widths.lean`, and
`FString.{ofString, isPaddedOf}`. The old `Spec.*` layer is gone throughout, superseded by the
conversions. `Inhabited (F p) := 42`, `FB.true`/`FB.false` and the `Coe`/`OfNat` instances were
deliberately not ported.

**`num2bits` and everything it gated are also done**, which is the big change since this guide
was first written: `num2bits`, `lessThan` / `lessEqThan` / `greaterThan` /
`greaterEqThan`, `F8.eq` / `lessThan` / `greaterThan` / `lessEqThan` / `greaterEqThan`,
`F8.isWhitespace`, `arraySelector`, `singleEndArray`, `FArray.xor`, `FArray.xorScan`, and
`FBitVec.eq` / `assert_eq`.

**`old/Clap/Lang.lean` is now fully accounted for.** The last round added `assert_range`,
`FBitVec.binSum`, `F32.add` and the `FBV8`/`F32`/`F64` `ofF` wrappers, and gave the comparison
family and the `F8` specialisations the `convertsM` lemmas they had been missing. Three things
were deliberately *not* ported, and should not be added back:

- **`FBitVec.ofF`** — was `num2bits w e` with the same argument order, so it is a pure alias.
  Use `num2bits`. Only the width-specialised `FBV8.ofF` / `F32.ofF` / `F64.ofF` exist.
- **`FByteArray`** (`old/Clap/Lang.lean:1050`) — its namespace is empty, and the type itself is
  `Vector (FBV8 p) w`, i.e. `Vector (Vector (FB p) 8) w`. That is the *nested* conversion
  `FArray.conversion` cannot express (see Conversions above). Design the conversion first.
- **The `Spec.*` decode layer** — `toBV`, `toUInt8`, `toUInt32`, `toChar`, `toString`, `valid`
  and the `left_inv` / `right_inv` round-trips. Superseded by the conversions, as everywhere
  else. Note the *arithmetic* underneath them is not lost: `Clap.bits2num_bound`,
  `Clap.num2bitsLsbPure_of_bits2num_eq` and `Clap.bits2num_of_num2bitsLsbPure_eq` are live in
  `Clap/Util/BitVec.lean` and should be reused rather than re-derived.

One warning carried over from that round: **`num2bits` asserts nothing in the `ConvertsM`
semantics, but does range-check in the compiled circuit.** See the ⚠ section in
[specifying-circuits.md](specifying-circuits.md); it is why `assert_range`'s slot 5 is `True`
and why `binSum` / `F32.add` are honestly `True`-constrained and wrapping.

Note `FBitVec p k`, `FArray p k` and `FVec p k` are all `Vector _ k` over the same cell type;
`FBitVec.eq` and `FBitVec.assert_eq` are thin delegations to the `FArray` ones, differing only
in stating vector equality rather than the pointwise form. Do not add a third implementation of
a gadget that already exists under another of these three names — check all three first.

| Gadget | Old location | Note |
|---|---|---|
| `selectArrayValue` | `old/Clap/Array.lean` | `dotProduct` of `singleOneArray` with the array |
| `leftArraySelector`, `rightArraySelector` | `old/Clap/Array.lean` | need `Vector.scanl`/`scanr` analogues; `FArray/xorScan.lean` is the closest existing pattern |
| `arraySelectorComplex` | `old/Clap/Array.lean` | after the two selectors |
| all of `old/Clap/Packing.lean` | | on `num2bits` |
| all of `old/Clap/Base64Len.lean` | | on `num2bits`, and `share` for the degree reduction |

**After `share` is wrapped**: the degree-reducing parts of `old/Clap/Base64Len.lean`, and
`Sha2.Circuit.maj` / `xor3`.

**After `fpmul` lands**: `old/Clap/RSA.lean`.

**After the nested conversion is designed**: `old/Clap/Sha2/*` (note `Sha2/Basic.lean` is already
monad-polymorphic over `[Monad m]` and typeclass-parameterised over the word representation — it
is the most portable old code in the repo).

**Unblocked by `FString.conversion`, not yet done**: the separate, larger `old/Clap/FString.lean`
(only `old/Clap/Lang.lean`'s `FString` has been ported), `old/Clap/HashToField.lean`, `old/Clap/JWT.lean`,
`old/Clap/Keyless.lean`.

**Retired, do not port**: `old/Clap/Circuit.lean` (PHOAS syntax), `old/Clap/Simulation.lean`,
`old/Clap/Compilation.lean`, `old/Clap/Compiler/*` (the `#compile` reifier), `old/Clap/Milestone.lean`.
`ClapM` builds the circuit by execution, so none of the reification machinery is needed. Note
that `Cfold` and `Dedup` are subsumed by hash-consing at construction time — but this is a
decision worth confirming with a maintainer rather than assuming, and `Dedup.dedup_sem_pre` was
`sorry` in the old model anyway.

**Already live, do not re-port**: everything in [`Clap/Util/`](../Clap/Util/) —
`BitVec.lean` (`num2bitsLsbPure(V)`, `bits2num(V)` and their lemmas), `Primes.lean`, and
`Wheels.lean` (`Vector.scanl`/`scanr`, `minBits`, `limbsToNat`, `natToLimbs(V)`, `toChunks`,
`ZMod.val_sum`). These are model-agnostic
mathematics and they are in the live import closure already, via `CircuitEvalSt.lean` — import
and use them directly. This is the one place where rule 1 of the agent guide does not apply.

`Clap/Util/Lemmas.lean` holds the new model's own small additions, including `minBits'`, a
cleaner restatement of `Clap.minBits` that `arraySelector` uses.

Note `Fact (Nat.Prime goldilocks)` and `Fact (Nat.Prime bn254)` are `sorry`'d in
`Clap/Util/Primes.lean`; anything requiring primality inherits that.

## Traps

- **Two byte encodings coexisted.** `F8 p = ZMod p` (a byte as one field element) and
  `FBV8 p = Vector (FB p) 8` (a byte as eight bit-cells). Sha2 used the latter, JWT/Keyless the
  former, and the old code carried a comment warning that typeclass resolution mixes them up.
  With `F p = BoundRef p` this gets *worse*: `F p`, `FB p`, `F8 p` are now all the same
  underlying type, and the intended invariant lives only in whichever `Conversion` you cite at
  proof time. Consider real `structure` wrappers before porting `Sha2` or `Packing`.
- **Dependent casts now sit inside binds.** `F32.add`'s `min 32 (32+1) = 32`,
  `Base64Len`'s `(w*4/3)*6 = w*8`, `Sha2`'s `32 - n + n = 32`. This is less painful than it
  looks, and `F32.add` is the worked case: **put the cast in the spec value, not in the proof**,
  and discharge it with `FArray.converts_vector_cast`. Because the reshape sits under a
  `return`, `convertsM_pure` closes the goal at the `Converts` level and no
  `ClapM.getResult`/`getState` commuting lemma is needed at all. `FArray/xorScan.lean` is the
  pattern to copy; `OneHotRaw`'s heavier `Vector.mapM_cast` route is only needed when the cast
  is inside an *iteration*. `FArray.converts_take` was added for `F32.add` and is the one to
  extend if you need `drop` or `extract`.
- **The old `Spec` namespace convention is dead.** Old code put spec functions in
  `Clap.Lang.Spec.X` shadowing the gadget namespace `Clap.Lang.X`, forcing `Lang.FB.assert` vs
  `assert` disambiguation inside proofs. The new model puts the spec in `ConvertsM`'s arguments
  instead. Do not reintroduce it.
- **`#compile` gave you argument serialisation for free** — and the replacement is now built.
  It flattened user `structure` arguments into vectors and fixed the public-input ordering.
  `AllocatedProgram` plus the `mkInput*` allocators do that job explicitly; the whole keyless
  input, ~8 nested structures, is allocated in
  [Clap/Keyless/Allocate.lean](../Clap/Keyless/Allocate.lean). Read
  [public-inputs.md](public-inputs.md) before writing an allocator by hand. The contract that
  input `i` is circuit variable `i` is maintained by allocating in order and nothing else, so it
  is still yours to keep.

## Checklist

- [ ] You rewrote into `Clap/Lang/`; you did not edit a file in `old/`.
- [ ] You read the old `native_decide` tests and used them to derive slots 4 and 5.
- [ ] Every doc-comment precondition and every `assert!` is now either slot 5 or an explicit
      hypothesis — none was dropped.
- [ ] No `v[i]!` survives; indices are bounded.
- [ ] No `partial def` survives.
- [ ] Old test vectors are re-run as `native_decide` smoke tests where possible, and carried
      over as comments with a reason where not.
- [ ] The gadget passes the [specifying-circuits.md](specifying-circuits.md) and
      [proving-circuits.md](proving-circuits.md) checklists too.
- [ ] You did not depend on `num2bits`, `share` or `fpmul` without first porting the wrapper.
