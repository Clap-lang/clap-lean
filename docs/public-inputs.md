---
name: public-inputs
description: How a ClapM circuit gets public inputs, and how to state an end-to-end theorem about a whole program rather than a single gadget.
when-to-use: Giving a circuit public inputs, writing an allocator for an input type, or stating a top-level theorem relating a circuit's constraints to a Lean specification.
---

# Public inputs and whole programs

Everything in [specifying-circuits.md](specifying-circuits.md) and
[proving-circuits.md](proving-circuits.md) is about one gadget: a `ClapM` action, and a
`convertsM` lemma relating it to a Lean value *given* `Converts` hypotheses about its
arguments. Those hypotheses have to come from somewhere. This file is about where.

A gadget's spec says "if these refs represent these values, then …". A *program*'s spec has
no such antecedent — it says "this circuit is satisfiable at this input vector iff the
specification holds of it". Getting from one to the other needs two things: a way to allocate
inputs as circuit variables, and a way to relate the resulting refs back to the positions of a
`Vector (ZMod p) n` that the prover supplies.

## `AllocatedProgram`

[AllocatedProgram.lean](../Clap/Model/AllocatedProgram.lean):

```lean
structure AllocatedProgram (p : ℕ) where
  InputT   : Type
  program  : InputT → ClapM p Unit
  numAlloc : ℕ
  allocate : HashConsM p InputT
```

- `InputT` is the Lean-level shape of the input — a record, a tuple, a vector.
- `allocate` builds a value of that shape out of freshly allocated circuit variables. It is a
  `HashConsM`, not a `ClapM`: allocating an input emits *no gates*, it only introduces
  expression nodes. Recall `HashConsM` lifts into `ClapM`, so `liftM allocate >>= program` is
  a valid composition.
- `numAlloc` is how many variables `allocate` consumes. It is stated separately rather than
  derived, so the rest of the file can talk about widths without unfolding the allocator.
- `program` is the circuit, ending in `Unit` — a program asserts, it does not return.

Two projections turn that into something you can state a theorem about:

```lean
def getCircuit     (prog : AllocatedProgram p) : Circuit × HashConsSt p
def getConstraints (prog : AllocatedProgram p) (inputs : Vector (ZMod p) prog.numAlloc) : Prop
```

`getCircuit` runs `allocate` against an empty `HashConsSt`, then builds the program's circuit
starting the variable counter at `prog.numAlloc` rather than `0` — that offset is the whole
point, it is what stops the program's own intermediate allocations from colliding with the
inputs. It returns the bootstrapped heap alongside the circuit.

`getConstraints` evaluates that circuit in a varstore built by pairing `inputs` with indices
`0 … numAlloc-1`. That map is the **input-order contract**: input `i` of the prover's vector is
circuit variable `i`. Nothing enforces it beyond `allocate` handing out indices in order, so an
allocator that allocates out of order silently permutes the public input.

## The allocators

[PublicInput.lean](../Clap/Model/PublicInput.lean). Each one takes the allocations made so
far and returns the representation plus the new count:

| Allocator | Allocates | Width |
|---|---|---|
| `mkInputF numAlloc` | `F p` | `mkInputFWidth = 1` |
| `mkInputFB numAlloc` | `FB p` | `mkInputFBWidth = 1` |
| `mkInputF8 numAlloc` | `F8 p` | `mkInputF8Width = 1` |
| `mkInputVectorF numAlloc k` | `Vector (F p) k` | `mkInputVectorFWidth k = k` |
| `mkInputFString numAlloc maxLen` | `FString p maxLen` | `mkInputFStringWidth maxLen = maxLen + 1` |
| `mkInputFBPaddedVector numAlloc maxLen` | `PaddedVector (FB p) p maxLen` | `mkInputFBPaddedVectorWidth maxLen = maxLen + 1` |

Each comes with `numAlloc_mkInputX : (mkInputX numAlloc …).getResult σ |>.2 = numAlloc + mkInputXWidth …`,
tagged `@[simp, grind =]`. That lemma is why you can compute a compound width without unfolding
anything: `simp` chains the `numAlloc_*` equations through a `do` block of allocations and
leaves you an arithmetic goal.

The `+ 1` on the padded types is the length field — `PaddedVector` is `data : Vector α w`
alongside `len : F p`, and the length is a public input like any other.

Write a new allocator for a new input type by following that shape: the allocator, a `Width`
definition, and the `numAlloc_` lemma, all three. Skipping the `Width` definition and inlining
the arithmetic is what makes the eventual width proof unmanageable.

## A worked compound allocator

[Clap/Keyless/Allocate.lean](../Clap/Keyless/Allocate.lean) does this at scale for the top-level
Keyless circuit, over the types in
[Clap/Keyless/Input.lean](../Clap/Keyless/Input.lean). The pattern is uniform —
thread `numAlloc` through a `do` block, one field at a time:

```lean
def mkInputRSAInput (numAlloc : ℕ) : HashConsM p (RSAInput p × ℕ) := do
  let (signature, numAlloc)     ← mkInputVectorF numAlloc RSA_NUM_LIMBS
  let (pubkeyModulus, numAlloc) ← mkInputVectorF numAlloc RSA_NUM_LIMBS
  return ({ signature := signature, pubkeyModulus := pubkeyModulus }, numAlloc)

@[simp, grind =] def mkInputRSAInputWidth := RSA_NUM_LIMBS + RSA_NUM_LIMBS

@[simp, grind =] lemma numAlloc_mkInputRSAInput :
  (HashConsM.getResult (p := p) (mkInputRSAInput (p := p) numAlloc) σ).2 =
  numAlloc + mkInputRSAInputWidth := rfl
```

`allocateKeyless : HashConsM p (FKeylessInput p)` and `allocateKeylessWidth : ℕ` are the top of
that stack — the `allocate` and `numAlloc` of a Keyless `AllocatedProgram`. Note that the width
lemmas are `rfl` where the shape allows and `by unfold …Width; simp only [←add_assoc]; rfl`
where the associativity does not line up; both are cheap, neither needs the allocator unfolded.

## The end-to-end theorem

The Poseidon example in [AllocatedProgram.lean](../Clap/Model/AllocatedProgram.lean) is the
template. The program:

```lean
def poseidonProgram (k : ℕ) : AllocatedProgram Primes.bn254 where
  InputT   := Vector (F Primes.bn254) k × F Primes.bn254
  program  := fun (input, hash) ↦ do
    let result ← poseidonBN254 input
    assert_eq result hash
  numAlloc := k + 1
  allocate := do
    let (vec, numAlloc)   ← mkInputVectorF 0 k
    let (f, _numAlloc)    ← mkInputF numAlloc
    return (vec, f)
```

It then proceeds in three steps, and it is worth seeing them as three *distinct* obligations
because they fail for different reasons:

1. **`PoseidonCircuitSpec`** — an ordinary gadget-style `convertsM` for `program`, with
   `Converts` hypotheses about the input refs. Nothing new: `step` through the body exactly as
   in [proving-circuits.md](proving-circuits.md).

2. **`poseidon.converts_input_vec`** — the bridge. This is the part with no analogue at gadget
   level: it proves that the refs `allocate` produced really do `Converts` to the positions of
   the prover's vector, in the varstore `getConstraints` builds. It is proved by unfolding down
   to `Expr.evalRec` and computing, leaning on `deref_poseidon_allocate_1` / `_2` (which say
   allocation `i` dereferences to `CacheExpr.v i`) and the `mkInputF` lemmas in
   [PublicInput.lean](../Clap/Model/PublicInput.lean).

3. **`odysseus`** — the statement you actually wanted:

```lean
theorem odysseus {k} {input : Vector (ZMod Primes.bn254) (k + 1)} :
  (poseidonProgram k).getConstraints input ↔
  letI inputInit := input.take k
  letI inputLast := input.back!
  poseidonSpec inputInit = inputLast
```

No `Converts` hypotheses, no refs, no monad — just "the circuit is satisfiable at this input
vector iff the spec holds". It is obtained by rewriting with `(PoseidonCircuitSpec _ _).constraints`
and discharging its hypotheses with step 2.

`poseidonSpec` is `opaque`, so `poseidon.convertsM` in that file is `sorry` and must stay that
way — it is the placeholder for "Poseidon's circuit matches Poseidon's Lean implementation",
which cannot be proved against an opaque constant. It is the only expected `sorry` in
`lake build Clap`. Everything structural around it is proved.

## Checklist

- [ ] `allocate` hands out indices in increasing order, with no gaps.
- [ ] `numAlloc` matches what `allocate` actually consumes — check it with the `numAlloc_*`
      lemmas, do not eyeball it.
- [ ] Every new allocator ships all three of: the allocator, its `Width`, its `numAlloc_` lemma.
- [ ] The program's `convertsM` is separated from the input-vector bridge. Do not try to prove
      the end-to-end theorem in one go.
