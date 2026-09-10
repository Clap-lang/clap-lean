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
4. **Add `open HashConsM`** if you use `mkAdd`/`mkSub`/`mkMul`/`mkConstant`/`BoundRef`
   unqualified.
5. **Use the type aliases** `F p`, `FB p`, `FArray p k`, `FList p`. Never write `ExprRef` in a
   gadget signature.
6. **Add `[p.AtLeastTwo]` only if the proof needs it.** It is needed when boolean semantics are
   involved (`eq`, `singleOneArray`, everything going through `FB.converts_of_F_converts`); it
   is *not* on `mkAdd`/`mkSub`/`mkMul`/`mkF`.
7. **Every arithmetic node is a bind.** `←(a + b)`, `←(a * b)`. There is no pure arithmetic on
   `F p` — see [porting-guide.md](porting-guide.md) if that surprises you.
8. **Constants must be allocated**: `←mkF 1`, never a bare `1`.
9. **Compose from what exists.** Do not re-derive a gadget that is already in `Clap/Lang/`.

### Existing inventory — reuse these

| Gadget | File | Type | Ideal value | Constraints |
|---|---|---|---|---|
| `mkF a` | [F/mkF.lean](../Clap/Lang/F/mkF.lean) | `ClapM p (F p)` | `a` | `True` |
| `mkAdd a b` | [F/mkAdd.lean](../Clap/Lang/F/mkAdd.lean) | `ClapM p (F p)` | `a_val + b_val` | `True` |
| `mkSub a b` | [F/mkSub.lean](../Clap/Lang/F/mkSub.lean) | `ClapM p (F p)` | `a_val - b_val` | `True` |
| `mkMul a b` | [F/mkMul.lean](../Clap/Lang/F/mkMul.lean) | `ClapM p (F p)` | `a_val * b_val` | `True` |
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
| `FArray.sum vals` | [FArray/sum.lean](../Clap/Lang/FArray/sum.lean) | `ClapM p (F p)` | `(vals.map (if · then 1 else 0)).sum` | `True` |
| `FArray.sum' init vals` | [FArray/sum.lean](../Clap/Lang/FArray/sum.lean) | `ClapM p (F p)` | as above | `True` |
| `oneHotRaw len idx` | [FArray/OneHotRaw.lean](../Clap/Lang/FArray/OneHotRaw.lean) | `ClapM p (FArray p len)` | `Vector.ofFn (·.val == idx_val.val)` | `True` |
| `singleOneArray len idx` | [FArray/singleOneArray.lean](../Clap/Lang/FArray/singleOneArray.lean) | `ClapM p (FArray p len)` | as above | `idx_val.val < len` |

Not yet wrapped, though the gate exists: **`share`**, **`num2bits`**, **`fpmul`**. If your
gadget needs one of these you must write its `Lang/` wrapper and `convertsM` first. `num2bits`
is the bottleneck for every comparison, range check, packing and hashing gadget — expect it to
be the first thing you need.

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

There is currently **no reusable `mapM`/`foldlM`/`forIn` `ConvertsM` combinator library**. Each
iterating gadget repeats this scaffolding — about 120 lines in `OneHotRaw.lean`. If you are
about to write the third one, build the combinator instead.

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
  mkSub one a

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
- [ ] Every constant goes through `mkF`; every arithmetic node is a bind.
- [ ] Exactly one lemma named `convertsM`, in `namespace <name>`.
- [ ] One `h_<arg> : Converts …` hypothesis per circuit-valued input.
- [ ] Slot 5 is `True` **only** if the gadget cannot fail to be satisfied.
- [ ] Parameter bounds are hypotheses, not `assert!` and not part of slot 5.
- [ ] No `_spec` / `_sound` / `_complete` / `_correct` names anywhere.
- [ ] If iterating: `_zero` / `_succ` recursion equations exist and are `@[simp, grind =]`.
- [ ] `lake build` passes.
