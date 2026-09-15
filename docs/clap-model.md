---
name: clap-model
description: Reference for the CLAP eDSLState circuit model - the expression heap, gates, the ClapM monad, the EvalSt semantics, and the Converts/ConvertsM refinement relation.
when-to-use: Look up a definition, a notation, or what a well-formedness condition actually says. Read the layer you need; you do not need to read the whole file.
---

# The CLAP model (`Clap/eDSLState/`)

Reference material. For *how to write* a gadget see [specifying-circuits.md](specifying-circuits.md);
for *how to prove* one see [proving-circuits.md](proving-circuits.md).

The model is four layers. Read bottom-up the first time; after that jump to the layer you need.

```
1. Expressions   CacheExpr / ExprRef / HashConsSt / HashConsM   -- a hash-consed arithmetic heap
2. Gates         Gate / Circuit                                  -- a flat list of constraint gates
3. The monad     ClapM p α                                       -- builds 1 and 2 by execution
4. Semantics     EvalSt / Circuit.eval                           -- witness + accumulated constraints
5. Refinement    Conversion / Converts / ConvertsM               -- what "this gadget is correct" means
```

---

## 1. Expressions: a hash-consed heap, not an inductive tree

[HashCons/CacheExpr.lean](../Clap/eDSLState/HashCons/CacheExpr.lean):

```lean
abbrev ExprRef := ℕ

inductive BinaryOp | add | sub | mul

inductive CacheExpr (p : ℕ)
  | c (_ : ZMod p)                                  -- constant
  | v (idx : ℕ)                                     -- variable, an index into the VarStore
  | binary_op (lhs rhs : ExprRef) (op : BinaryOp)   -- children are *references*, not subterms

@[grind =]
def CacheExpr.wellFormed {p : ℕ} (e : CacheExpr p) (idx : ExprRef) : Prop :=
  match e with
    | c _ | v _ => True
    | binary_op lhs rhs _ => lhs < idx ∧ rhs < idx
```

`CacheExpr` is flat and non-recursive. Sub-expressions are `ℕ` indices into a heap:

[HashCons/HashConsSt.lean](../Clap/eDSLState/HashCons/HashConsSt.lean):

```lean
@[grind]
structure HashConsSt (p : ℕ) where
  exprs : Array (CacheExpr p)
  wellFormed : ∀ i < exprs.size, exprs[i]?.any (·.wellFormed i)
```

The invariant is bundled into the structure: **every node references only strictly earlier
nodes**, so the heap is acyclic by construction and recursive evaluation terminates on `e.ref`.

The heap only ever grows by `push`. Consequently the single most common frame condition in the
whole development is **`σ.exprs.isPrefixOf σ'.exprs`**.

### The builder monad

[HashCons/HashConsM.lean](../Clap/eDSLState/HashCons/HashConsM.lean):

```lean
abbrev HashConsM (p : ℕ) := StateM (HashConsSt p)

def saveExpr (e : CacheExpr p) : HashConsM p ExprRef := do
  let state ← get
  if e ∈ state.exprs then
    return state.exprs.idxOf e            -- hash-consing: reuse the existing node
  else if h : e.wellFormed state.size then
    set (state.pushExpr e h); return state.size
  else pure 42                            -- unreachable given the structure invariant

abbrev BoundRef (_ : ℕ) : Type := ExprRef  -- a phantom-typed reference

def mkConstant (x : ZMod p) : HashConsM p (BoundRef p) := saveExpr (.c x)
def mkVar      (x : ℕ)      : HashConsM p (BoundRef p) := saveExpr (.v x)
def mkAdd (l r : BoundRef p) : HashConsM p (BoundRef p) := saveExpr (.binary_op l r .add)
def mkSub (l r : BoundRef p) : HashConsM p (BoundRef p) := saveExpr (.binary_op l r .sub)
def mkMul (l r : BoundRef p) : HashConsM p (BoundRef p) := saveExpr (.binary_op l r .mul)
```

Note the `pure 42` fallback: **`saveExpr` cannot fail**, so nothing downstream can either.
Hash-consing here is what constant folding and de-duplication were in the old model — it
happens at construction time, not as a proved rewrite pass.

### `Expr` = a ref bundled with its heap

[Expr.lean](../Clap/eDSLState/Expr.lean):

```lean
@[grind cases]
structure Expr (p : ℕ) where
  ref : ExprRef
  σ : HashConsSt p

notation "⦃" ref ", " σ "⦄" => Expr.mk ref σ      -- Expr.lean:16

@[grind =] def deref (e : Expr p) : Option (CacheExpr p) := e.σ.exprs[e.ref]?
prefix:max "*" => deref

/-- Dereference is valid. -/
def wellFormed (e : Expr p) : Prop := e.ref < e.σ.size

@[grind _=_] lemma wellFormed_iff_isSome : e.wellFormed ↔ (*e).isSome
@[grind →]   lemma wellFormed_frame
  (h₁ : e.wellFormed) (h₂ : e.σ.exprs.isPrefixOf e'.σ.exprs) (h₃ : e.ref = e'.ref) : e'.wellFormed
```

### Variable store

[Varstore.lean](../Clap/eDSLState/Varstore.lean):

```lean
abbrev VarStore (p : ℕ) := Std.ExtTreeMap ℕ (ZMod p) (cmp := compare)

@[grind =]
instance : HasSubset (VarStore p) where
  Subset Γ1 Γ2 := ∀ k : ℕ, Γ1[k]?.isSome → Γ1[k]? = Γ2[k]?
```

`ExtTreeMap` is extensional, so `Γ₁ = Γ₂` is provable by `ext`. `⊆` means "extends, agreeing on
everything already present".

---

## 2. Gates and circuits

[Gate.lean](../Clap/eDSLState/Gate.lean):

```lean
@[grind cases]
inductive Gate where
  | eq0      (e : ExprRef)
  | share    (e : ExprRef)
  | isZero   (e : ExprRef)
  | num2bits (w : ℕ) (e : ExprRef)
  | fpmul    (w k : ℕ) (a b p' : Vector ExprRef k)

def numAllocStep : Gate → ℕ            -- how many witness variables this gate allocates
  | .eq0 _ => 0 | .share _ => 1 | .isZero _ => 1
  | .num2bits w _ => w | .fpmul (k := k) .. => k

@[aesop safe cases, grind]
structure wellFormed (gate : Gate) (Γ : VarStore p) (σ : HashConsSt p) : Prop where
  refsValid : gate.refsValid σ.size                             -- refs are in range
  varsAllocated : gate.varsAllocated Γ σ                        -- every ref evaluates to some
```

`Gate` is *not* indexed by `p`; it holds only `ExprRef = ℕ`. The prime enters via `σ` and `Γ`.

[Circuit.lean](../Clap/eDSLState/Circuit.lean):

```lean
abbrev Circuit := Array Gate

@[aesop safe cases, grind]
structure Circuit.wellFormed (circuit : Circuit) (Γ) (σ) (numAlloc : ℕ) : Prop where
  refsValid : circuit.refsValid σ.size
  varsAllocated : circuit.varsAllocated Γ σ numAlloc
```

`Circuit.varsAllocated` is the "no use before definition" condition: at each gate index `i`,
evaluate the prefix `c.take i`, and require every ref the gate mentions to be evaluable in the
prefix's varStore and to touch only variables below the prefix's `numAlloc`.

---

## 3. The monad

[Monad.lean:11-15](../Clap/eDSLState/Monad.lean#L11-L15):

```lean
abbrev CircuitT (m : Type → Type) (α : Type) : Type := WriterT Circuit (StateT ℕ m) α
abbrev CircuitM (α : Type) : Type := CircuitT Id α
abbrev ClapM (p : ℕ) (α : Type) : Type := CircuitT (HashConsM p) α
```

Three effects, and no others: a **writer** of the gate list, a **state** `numAlloc` (the next
free witness index), and a **state** holding the expression heap. There is no failure effect
and no varStore inside the monad — the varStore is supplied later, at evaluation time.

The file documents the unfolding itself, with `rfl`:

```lean
example {resultT} :
  ClapM p resultT = (ℕ → (HashConsSt p) → ((resultT × Circuit) × ℕ) × (HashConsSt p)) := rfl
```

### The one allocation primitive

```lean
-- Allocates new variable and returns reference to it
def alloc {p : ℕ} : ClapM p ExprRef := do
  let varIdx ← getModify (·+1)
  HashConsM.mkVar (p := p) varIdx
```

### The projections — memorise these

Every lemma in the codebase is phrased in terms of them.

```lean
def getResult        (cmd : ClapM p α) (numAlloc : ℕ) (σ : HashConsSt p) : α
def getCircuit       (cmd : ClapM p α) (numAlloc : ℕ) (σ : HashConsSt p) : Circuit
def getNumAlloc      (cmd : ClapM p α) (numAlloc : ℕ) (σ : HashConsSt p) : ℕ
def getHashConsState (cmd : ClapM p α) (numAlloc : ℕ) (σ : HashConsSt p) : HashConsSt p
def getVarStore      (cmd : ClapM p α) (varStore : VarStore p) (numAlloc : ℕ) (σ : HashConsSt p)
  : VarStore p :=
  [varStore, cmd.getHashConsState numAlloc σ, numAlloc|cmd.getCircuit numAlloc σ]ₑ.varStore

def runAndEval (cmd : ClapM p α) (numAlloc : ℕ) (varStore : VarStore p) (σ : HashConsSt p)
  : α × EvalSt p
:= ⟨ cmd.getResult numAlloc σ,
     [varStore, (cmd.getHashConsState numAlloc σ), numAlloc | (cmd.getCircuit numAlloc σ)]ₑ ⟩
```

Each has `@[simp, grind =]` equations for `pure`, `bind`, `tell`, `<$>`, `liftM` and every eDSL
primitive, named `<accessor>_<construct>` — `getCircuit_bind`, `getVarStore_share`,
`getNumAlloc_pure`, and so on.

### Well-formedness of an action

[Monad.lean:348](../Clap/eDSLState/Monad.lean#L348):

```lean
@[grind =]
def ClapM.wellFormed (action) (numAlloc) (varStore) (σ) : Prop :=
  circuit_wellFormed action numAlloc varStore σ ∧
  numAlloc_wellFormed action numAlloc varStore σ ∧
  hashConsState_wellFormed action numAlloc σ
```

In words:

| conjunct | says |
|---|---|
| `circuit_wellFormed` | the emitted gates reference only allocated expressions and already-defined variables |
| `numAlloc_wellFormed` | the monad's counter agrees with what the semantics says the circuit allocates |
| `hashConsState_wellFormed` | the heap only grows (`σ.exprs.isPrefixOf …`) |

The compositional workhorse:

```lean
@[aesop safe, grind .]
lemma ClapM.bind_wellFormed
  (h_a : a.wellFormed numAlloc varStore σ)
  (h_f : (f (a.getResult numAlloc σ)).wellFormed
           (a.getNumAlloc numAlloc σ) (a.getVarStore varStore numAlloc σ)
           (a.getHashConsState numAlloc σ))
: (a >>= f).wellFormed numAlloc varStore σ
```

### The five eDSL gates

[eDSL.lean:11-33](../Clap/eDSLState/eDSL.lean#L11-L33). All `@[irreducible]` — **never unfold
them** (see rule 5 in [clap-agent-guide.md](clap-agent-guide.md)).

```lean
@[irreducible] def eq0      (e : ExprRef) : ClapM p Unit := do tell #[.eq0 e]
@[irreducible] def share    (e : ExprRef) : ClapM p ExprRef := do tell #[.share e]; ClapM.alloc
@[irreducible] def isZero   (e : ExprRef) : ClapM p ExprRef := do tell #[.isZero e]; ClapM.alloc
@[irreducible] def num2bits (width : ℕ) (e : ExprRef) : ClapM p (Vector ExprRef width) := do
  tell #[.num2bits width e]; Vector.ofFnM fun (_ : Fin width) ↦ ClapM.alloc
@[irreducible] def fpmul (width k : ℕ) (a b p' : Vector ExprRef k) : ClapM p (Vector ExprRef k) := do
  tell #[.fpmul width k a b p']; Vector.ofFnM fun (_ : Fin k) ↦ ClapM.alloc
```

Each emits one gate, then allocates exactly `numAllocStep` fresh variables. `eq0` is the only
constraint-only gate.

Their supporting lemma families, all in `eDSL.lean`: `wellFormed_*` (each takes the same three
hypotheses — ref in range, all needed vars present, no forward references), `eval_edsl_*`,
`getResult_*`, `getVarStore_*`, `getCircuit_*`.

### Arithmetic notation

`+ - *` on refs are *monadic*, at two priorities. In `HashConsM`
([HashConsM.lean](../Clap/eDSLState/HashCons/HashConsM.lean)) and, at higher priority, in
`ClapM` ([eDSL.lean](../Clap/eDSLState/eDSL.lean)):

```lean
instance (priority := high) {p} : HAdd (BoundRef p) (BoundRef p) (ClapM p (BoundRef p)) where
  hAdd x y := liftM (mkAdd (p := p) x y)

@[grind norm] lemma add_def {p} {l r : BoundRef p} :
  (l + r : ClapM p (BoundRef p)) = liftM (mkAdd l r) := rfl
-- likewise sub_def, mul_def
```

So `a + b : ClapM p (F p)`; inside a `do` block you write `←(a + b)`. `add_def`/`sub_def`/
`mul_def` are the rewrites that expose the underlying bind to the `step` tactic.

---

## 4. Semantics: `EvalSt`

[CircuitEvalSt.lean:15-19](../Clap/eDSLState/CircuitEvalSt.lean#L15-L19):

```lean
structure EvalSt (p : ℕ) where
  numAlloc : ℕ
  varStore : VarStore p
  constraints : Prop
  deriving Inhabited
```

**`constraints` is a `Prop`, not a `Bool`.** The constraint system is shallowly embedded, and
witness generation and constraint accumulation happen in one pass. This is why every gadget
spec states an `↔` rather than an equation.

```lean
def unconstrained (numAlloc : ℕ) (Γ : VarStore p) : EvalSt p := ⟨numAlloc, Γ, True⟩
notation "unconstrained[" numAlloc:arg "]" "[" varStore:arg "]" => unconstrained numAlloc varStore

def addConstraint (st : EvalSt p) (constraint : Prop) : EvalSt p :=
  {st with constraints := st.constraints ∧ constraint}

def alloc (result : EvalSt p) (vals : Vector (ZMod p) k) : EvalSt p   -- append fresh witness values
def assertAllocated (st : EvalSt p) (es : Vector (Expr p) k) : EvalSt p
```

One `step` function per gate, dispatched by `EvalSt.step`:

```lean
def stepEq0    (st) (σ) (e) := st.addConstraint (st[Expr.mk e σ]? = .some 0)
def stepShare  (st) (σ) (e) := (st.assertAllocated #v[⟨e, σ⟩]).alloc #v[st[Expr.mk e σ]!]
def stepIsZero (st) (σ) (e) :=
  (st.assertAllocated #v[⟨e, σ⟩]).alloc #v[if st[Expr.mk e σ]? = .some 0 then 1 else 0]
def stepNum2bits (st) (σ) (w) (e) :=
  (st.assertAllocated #v[⟨e, σ⟩]).alloc (num2bitsLsbPureV w (st[Expr.mk e σ]!))
def stepFpmul … -- range-checks each limb, asserts the modulus is nonzero, allocs fpMulPureV …

notation "[" res ", " σ "|" cmd "]ₛ" => step res cmd σ     -- CircuitEvalSt.lean:522
```

And the circuit-level fold:

```lean
def Circuit.eval (circuit : Circuit) (varStore : VarStore p) (numAlloc : ℕ) (σ : HashConsSt p)
  : EvalSt p := circuit.foldl (EvalSt.step (σ := σ)) ⟨numAlloc, varStore, True⟩

notation "[" varStore ", " σ ", " numAlloc "|" circuit "]ₑ" => Circuit.eval circuit varStore numAlloc σ
```

Key structural facts:

```lean
@[simp, grind =] lemma eval_append   : [Γ,σ,n|c1 ++ c2]ₑ = [Γ,σ,n|c1; c2]ₑ
@[simp, grind =] lemma eval_numAlloc : [Γ,σ,n|c]ₑ.numAlloc = n + c.numAllocStep
@[grind =] lemma getElem?_eval_eq_getElem?_of_lt (h : v < numAlloc) :
  [Γ,σ,n|c]ₑ.varStore[v]? = Γ[v]?          -- circuits never clobber pre-existing variables
```

### Expression evaluation

[HashCons/Eval.lean](../Clap/eDSLState/HashCons/Eval.lean) gives two evaluators, proved equal:
`eval` (memoised, bottom-up, *the definition*) and `evalRec` (recursive, induction-friendly).

```lean
notation "[" varStore "," σ "|" e "]" => eval varStore ⟨e, σ⟩     -- Eval.lean:476
notation "[" varStore "|" e "]"       => eval varStore e          -- Eval.lean:478

lemma eval_eq_evalRec (h : e.wellFormed) : [Γ|e] = evalRec Γ e    -- the most-used bridge
```

Everything is `Option`-valued: `none` means *not well-formed, or a referenced variable is
missing from `Γ`*.

```lean
def varSet (e : Expr p) : Set ℕ                                   -- which variables e depends on
def varSet_wellFormed (e : Expr p) (numAlloc : ℕ) : Prop := ∀ x ∈ e.varSet, x < numAlloc

@[grind =] def precedes (Γ₁ Γ₂ : VarStore p) (σ : HashConsSt p) :=
  ∀ e < σ.size, [Γ₁, σ|e].isSome → [Γ₂, σ|e].isSome
notation "[" σ "|" Γ₁ " ⊑ " Γ₂ "]" => precedes Γ₁ Γ₂ σ            -- Eval.lean:716
```

---

## 5. Refinement: `Conversion`, `Converts`, `ConvertsM`

This is what "correct" means. [Convert/Base.lean](../Clap/eDSLState/Convert/Base.lean):

```lean
structure Conversion (p : ℕ) (α : Type) where
  IdealT : Type                        -- the pure Lean type this circuit type models
  conversion : IdealT → List (ZMod p)  -- ideal value ↦ field elements
  toExprs : α → List ExprRef           -- circuit value ↦ expression refs

structure ClapMState (p : ℕ) where     -- the three ambient components, bundled
  varStore : VarStore p
  σ : HashConsSt p
  numAlloc : ℕ

def ClapM.getState (cmd : ClapM p α) (state : ClapMState p) : ClapMState p where
  varStore := cmd.getVarStore state.varStore state.numAlloc state.σ
  σ        := cmd.getHashConsState state.numAlloc state.σ
  numAlloc := cmd.getNumAlloc state.numAlloc state.σ
```

### `Converts` — a *value* is correct

```lean
structure Converts (conversion : Conversion p α) (state : ClapMState p)
                   (exprs : α) (val : conversion.IdealT) : Prop where
  h_conversion : (conversion.conversion val).length = (conversion.toExprs exprs).length
  varSet_wf : ∀ i, ⦃(conversion.toExprs exprs)[i], state.σ⦄.varSet_wellFormed state.numAlloc
  expr_wf   : ∀ i, ⦃(conversion.toExprs exprs)[i], state.σ⦄.wellFormed
  value_eq  : ∀ i, [state.varStore|⦃(conversion.toExprs exprs)[i], state.σ⦄]
                     = .some ((conversion.conversion val)[i])
```

Read it as: *these expression refs are well-formed, depend only on already-allocated variables,
and evaluate exactly to the field encoding of the ideal value `val`.*

Destructure it as `obtain ⟨h_length, h_varSet, h_wellFormed, h_result⟩ := h_a` — the fields are
in the order `h_conversion, varSet_wf, expr_wf, value_eq`.

### `ConvertsM` — an *action* is correct

```lean
structure ConvertsM (conversion : Conversion p α) (action : ClapM p α)
                    (state : ClapMState p) (val : conversion.IdealT)
                    (constraints : Prop) : Prop where
  result     : Converts conversion (action.getState state)
                        (action.getResult state.numAlloc state.σ) val
  wellFormed : action.wellFormed state.numAlloc state.varStore state.σ
  constraints : (action.runAndEval state.numAlloc state.varStore state.σ).2.constraints
                  ↔ constraints
```

The third field is soundness **and** completeness, as one bi-implication: *the constraints the
circuit accumulates hold exactly when the user-facing condition holds*. Left-to-right is
soundness; right-to-left is completeness. `result`'s `value_eq` simultaneously supplies the
completeness witness.

### The composition lemmas

```lean
lemma convertsM_pure  (h : Converts conversion state x val) (h_constraints : constraints)
  : ConvertsM conversion (pure x) state val constraints

lemma convertsM_bind
  (h_action   : ConvertsM conversion1 action state action_val constraints1)
  (h_function : ConvertsM conversion2 (function (action.getResult state.numAlloc state.σ))
                          (action.getState state) function_val (constraints1 → constraints))
  (h : constraints → constraints1)
  : ConvertsM conversion2 (action >>= function) state function_val constraints

lemma convertsM_map (h_action …) (h_function : Converts …)
                    (h_constraints : constraints ↔ action_constraints)
  : ConvertsM conversion2 (f <$> action) state function_val constraints

lemma converts_skip (h_action : ConvertsM conversion₁ action state val1 constraints)
                    (h : Converts conversion₂ state exprs val2)
  : Converts conversion₂ (action.getState state) exprs val2      -- carry a fact past an action

lemma converts_cast / converts_of_converts / convertsM_of_convertsM  -- rewrite value or constraints
```

Note the contravariant shape of `convertsM_bind`: the continuation is proved under the
implication `constraints1 → constraints`. That is how "constraints established earlier in the
circuit may be assumed later" is threaded through a `do` block.

### The five standard conversions

[Convert/Specialised.lean:50-97](../Clap/eDSLState/Convert/Specialised.lean#L50-L97):

```lean
abbrev F      (p : ℕ)   : Type := HashConsM.BoundRef p   -- a field element
abbrev FB     (p : ℕ)   : Type := F p                    -- a *boolean* field element
abbrev FArray (p k : ℕ) : Type := Vector (FB p) k
abbrev FList  (p : ℕ)   : Type := List (FB p)
```

| conversion | `IdealT` | `toExprs` | `conversion` |
|---|---|---|---|
| `F.conversion` | `ZMod p` | `[x]` | `[x]` |
| `FB.conversion` | `Bool` | `[x]` | `[if x then 1 else 0]` |
| `FUnit.conversion` | `Unit` | `[]` | `[]` |
| `FArray.conversion` | `Vector Bool k` | `x.toList` | `(x.map (if · then 1 else 0)).toList` |
| `FList.conversion` | `List Bool` | `x` | `x.map (if · then 1 else 0)` |

`F p`, `FB p`, `FArray p k` and `FList p` are all *the same underlying type* up to `Vector`/
`List` wrapping — `ExprRef`. The distinction is entirely in which `Conversion` you cite in the
spec. Choosing `FB.conversion` is a claim that the value is a bit.

Bridging lemmas, in the same file:

```lean
F.converts_of_FB_converts        -- FB fact ⟹ F fact (value becomes `if b then 1 else 0`)
FB.converts_of_F_converts        -- F fact + `val.val < 2` ⟹ FB fact (needs [p.AtLeastTwo])
FB.convertsM_of_F_convertsM      -- the same, at the action level
FUnit.converts                   -- always true
FArray.converts_empty / converts_iff_FB_converts / converts_push / converts_pop
FArray.converts_getElem / converts_vector_cast / convertsM_of_convertsM_toList
FList.converts_empty / converts_append / converts_of_converts_FB / converts_singleton_of_converts_FB
```

---

## Notation cheat-sheet

| Notation | Means | Defined at |
|---|---|---|
| `⦃ref, σ⦄` | `Expr.mk ref σ` | [Expr.lean:16](../Clap/eDSLState/Expr.lean#L16) |
| `*e` | `Expr.deref e` | [Expr.lean:32](../Clap/eDSLState/Expr.lean#L32) |
| `[Γ, σ\|e]` | `eval Γ ⟨e, σ⟩` | [Eval.lean:476](../Clap/eDSLState/HashCons/Eval.lean#L476) |
| `[Γ\|e]` | `eval Γ e` | [Eval.lean:478](../Clap/eDSLState/HashCons/Eval.lean#L478) |
| `[Γ, σ\|←x]` | `HashConsM.run (evalM Γ x) σ` | [Eval.lean:596](../Clap/eDSLState/HashCons/Eval.lean#L596) |
| `[σ\|Γ₁ ⊑ Γ₂]` | `precedes Γ₁ Γ₂ σ` | [Eval.lean:716](../Clap/eDSLState/HashCons/Eval.lean#L716) |
| `unconstrained[n][Γ]` | `EvalSt.unconstrained n Γ` | [CircuitEvalSt.lean:40](../Clap/eDSLState/CircuitEvalSt.lean#L40) |
| `[st, σ\|gate]ₛ` | `EvalSt.step st gate σ` | [CircuitEvalSt.lean:522](../Clap/eDSLState/CircuitEvalSt.lean#L522) |
| `[Γ, σ, n\|circuit]ₑ` | `Circuit.eval circuit Γ n σ` | [Circuit.lean:98](../Clap/eDSLState/Circuit.lean#L98) |
| `[Γ, σ, n\|c₁; c₂]ₑ` | `Circuit.seq c₁ c₂ Γ n σ` | [Circuit.lean:566](../Clap/eDSLState/Circuit.lean#L566) |

For metavariable conventions (`Γ`, `σ`, `e!` vs `e`, `x` vs `x_val`) see
[clap-agent-guide.md](clap-agent-guide.md).

---

## Intended vs. proved vocabulary

You will find the words **wellbehaved**, **complete** and **sound** in two places, and neither
is live code:

- [Test.lean](../Clap/eDSLState/Test.lean) defines them as `#eval` sanity checks —
  *wellbehaved* = the witness generator extends the inputs, *complete* = satisfiable implies the
  generated witness satisfies the constraint system, *sound* = the converse.
- [Plan.lean](../Clap/eDSLState/Plan.lean) states them as `theorem … := by done` skeletons. The
  entire file is commented out; it is a design document, not code.

In the live model these are the two directions of `ConvertsM.constraints`. Do not go looking
for a `soundness` theorem, and do not write one.

---

## Automation infrastructure

- **`grind` is the primary automation.** Nearly every declaration carries an annotation. The
  variants in use: `@[grind =]` (forward rewrite), `@[grind _=_]` / `@[grind =_]`
  (bidirectional / backward), `@[grind →]`, `@[grind ←]`, `@[grind .]` (use as a fact),
  `@[grind! .]` (aggressive), `@[grind cases]`, `@[grind norm]`, `@[grind ext]`.
- **`aesop`**: `@[aesop safe]`, `@[aesop unsafe]`, `@[aesop safe cases]`.
- **`@[irreducible]`** on the five eDSL gates — deliberate; see rule 5.
- **Custom simp set** `Clap.monads`, registered at
  [Wheels.lean:15](../Clap/eDSLState/Wheels.lean#L15) and populated at
  [Monad.lean:580](../Clap/eDSLState/Monad.lean#L580) with `bind`, `pure`, `ClapM.run`,
  `WriterT.run`, `WriterT.mk`, `tell`, `StateT.run/bind/pure/map`, `Functor.map`. Use
  `simp [Clap.monads]` to blast through monad plumbing.
- **Global tweaks** in [Clap/Lang/Wheels.lean](../Clap/Lang/Wheels.lean):
  `attribute [simp] sub_eq_zero`, `attribute [grind =] Option.isSome_eq_false_iff
  Option.isNone_iff_eq_none`, and `ZMod.val_one_le_one`.
- **Ambient lemma library** [eDSLState/Wheels.lean](../Clap/eDSLState/Wheels.lean): the
  `Array.isPrefixOf_*` prefix machinery that underpins all heap-frame reasoning, the
  `Std.ExtTreeMap.insertMany*` lemmas for the varStore, and `Vector.mapM_cast`,
  `Vector.mapM_succ`, `Vector.take_append_last`.

Note that `Clap.ZMod.zero_ne_one` / `Clap.ZMod.one_ne_zero` in `eDSLState/Wheels.lean` shadow
Mathlib names inside `namespace Clap`.

---

## Known rough edges

Flagged so you do not chase them:

1. `ConstraintSystem.lean`, `WitnessGenerator.lean`, `Plan.lean`, `Test.lean` are commented out
   of [Clap.lean](../Clap.lean); two of them do not parse.
2. `Circuit.toCs`'s `.fpmul` branch is `sorry`; `num_constraints (.fpmul …) = 42` is a
   placeholder; `ConstraintSystem/fpMul.lean`'s `check_lt_impl` is a stub.
3. `Gate.numAllocStep (.isZero _) = 1`, but `WitnessGenerator.trace_capacity` and
   `ConstraintSystem.num_constraints` both say `2` (the R1CS lowering also needs the inverse
   hint). Unreconciled.
4. [IsValid.lean](../Clap/eDSLState/IsValid.lean) compiles but is referenced nowhere — a
   superseded design. Never build on it.
5. `HashConsM.saveExpr` returns a magic `42` in its unreachable ill-formed branch. There is no
   failure monad anywhere.
6. The `seq` unexpander prints its arguments in a different order than the macro parses them.
7. `HashConsM.getResult_mkVar` is a copy-paste of `getResult_mkConstant` and states a fact
   about `mkConstant`.
8. `Circuit.varsAllocated` says `c.take i` while `bind_Circuit_wellFormed` says
   `circuit.extract 0 i` — the same thing, two spellings.
