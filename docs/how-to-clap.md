---
name: how-to-clap
description: Guided introduction to CLAP - the ClapM monad and its well-formedness conditions, Conversion/Converts/ConvertsM, a worked eq gadget proved with step, and public inputs via AllocatedProgram.
when-to-use: First contact with CLAP, or to recall why the infrastructure is shaped the way it is. Read it once before the task-specific files.
---

# How to CLAP

*Adapted from `Clap/HowToClap.md` by Frantisek Silvasi (branch `fasapa/Clapful`, e8c4797).
Where this file and the other docs disagree, this file is authoritative.*

This is the narrative tour. For reference material see [clap-model.md](clap-model.md), for
proof recipes and failure modes [proving-circuits.md](proving-circuits.md), and for whole
programs [public-inputs.md](public-inputs.md).

## Clapping

`ClapM p` in [`Clap/Model/Monad.lean`](../Clap/Model/Monad.lean) is _the_ Monad of the model. It is lawful.  
The `p` is the underlying prime which we fix and forget about, thus we can consider the `ClapM` monad. Furthermore, every monad in the stack is parameterised by `p` and receives the same treatment in this exposition. Every circuit we make is of type `ClapM Unit`, but of course, intermediate actions have an arbitrary functor type.

In a majority of cases, we use simple types, with some additional notion of well-formedness; the focus of the infrastructure is to minimise / eliminate the need to handle these notions explicitly. It is nevertheless useful to build an understanding of what they are in case an extension / alteration is needed. Or in case something unexpected goes wrong, albeit I am not sure what that could be. I guess that is what unexpected means, ey? As such, we outline these well-formed conditions throughout the exposition, with the intent for them to be skimmed over and returned to only in case of emergency. This nevertheless serves as documentation, in addition to something for Claude to read.

`ClapM` itself is a stack of the following monads:
- `StateM ℕ` - The `ℕ` here is always named `numAlloc`, and it stores the number of allocations
  the circuit has made.
- `StateM HashConsSt` - The `HashConsSt` here is always named `σ`, and it stores the underlying hash-consed representation of all encountered expressions.
- `WriterM Circuit` - The `Circuit` here is always named `circuit`, and it stores the accumulated
  sequence of gates as constructed by the eDSL.

NB `ClapM` is the circuit 'builder', _not_ evaluator.

As far as `ClapM` can tell, an expression is just a pointer of type `ExprRef`. One can also encounter `BoundRef p` which is a synonym for `ExprRef` that carries `p` for the purposes of typeclass inference. These references point into the `HashConsSt`, which itself stores an array of hash-consed expressions of type `CacheExpr`. A hash-consed expression composes expressions of parts. As such, compound expressions store references to subexpressions. This gives rise to a natural notion of well-formedness, i.e. a `CacheExpr` is well-formed with respect to some index `ref : ExprRef` iff any reference contained within precedes `ref`. The immediate corollary of this is that atomic `CacheExpr`s, constants and variables, are vacuously well-formed. This notion then further induces well-formedness of `HashConsSt`, which is bundled with the type and states the obvious -- any expression at index `i` is well-formed up to `i`. With all of that said, _do not_ use the `CacheExpr` representation directly. There is practically never a reason to so much as utter this type, unless doing fundamental changes to the infrastructure. Please consider restructuring your approach if you need to state anything in its terms.

Tip: If `a b : ExprRef`, then `a + b` | `a - b` | `a * b` will fail to infer the `p` for the underlying monad. A frictionless fix is to annotate the type of `a`/`b` explicitly with `BoundRef p`. Put the annotation on the binder -- the signature, or a typed `let a' : BoundRef p := a` -- since an inline ascription `(a : BoundRef p) + b` does not stick; see [clap-model.md §Arithmetic notation](clap-model.md#arithmetic-notation).

As such, an `ExprRef` in isolation, i.e. without an accompanying `HashConsSt` is meaningless. We therefore use `Expr` as a bundle of `ref : ExprRef` and a `σ : HashConsSt`. We say that `Expr` is well formed iff `ref < σ.size`; in other words, it is well formed if a dereference of a `ref` yields a `.some (_ : CacheExpr)`.

Expressions can be evaluated with respect to a particular variable store, typed `VarStore` throughout. It is a mapping from a trace index to a value in `ZMod p`, always named `Γ` or `varStore`. The notation `[Γ|e]` evaluates `e : Expr` in the context of `Γ : VarStore`.

`Circuit`s can be evaluated similarly, however please do note that we need an extra bit of state to evaluate an arbitrary `Circuit`, namely the `numAlloc`, which is serving here as a notion of validity of an allocation. As such, we need a `Γ`, `σ` and a `numAlloc`. This bundle is `ClapMState`. We have the following syntax for evaluating circuits: `[Γ, σ, numAlloc|circuit]ₑ : EvalSt`.

`EvalSt` can be thought of as circuit evaluation state. It carries its `numAlloc` and `Γ`, together with `constraints : Prop`. Constraints is the set of constraints accumulated throughout evaluation of a circuit.

Clap programs are sequences of monadic actions within the `ClapM` monad. Put differently, a statement in the `ClapM` monad is an expression of a circuit in the Clap eDSL. There are five (5) atomic operations / gates; namely:
- `eq0`
- `share`
- `isZero`
- `num2bits`
- `fpmul`

These are the atoms of the eDSL. Everything else is monadic Lean code. `ClapM` actions carry their notion of well-formedness as well. This notion is _not_ invisible when reasoning about `ClapM` circuits, but can be, for the most part, ignored. There are three parts of an `action : ClapM α` being well-formed with respect to some `ClapMState`:
- Recall that a `Circuit` is a sequence of gates. The underlying circuit is well-formed when:
  - No gate contains an expression that is not hash-consed,
  - all variables are allocated, i.e. exist in `Γ`,
  - no gate depends on a variable that is allocated by gates that have not been evaluated yet.
- The underlying `numAlloc` is well-formed when circuit building and evaluation agree on `numAlloc`.
- The underlying hash-cons state is well-formed when the action only appends to the hash cons state.

With an understanding of what `ClapM` is, let us have a look at the infrastructure for proving specifications of programs written in Clap.

## Clap example and how to prove properties about it

### Declaring datatypes

First, define two simple datatypes at the Clap level.
```lean
abbrev F  (p : ℕ) : Type := HashConsM.BoundRef p
abbrev FB (p : ℕ) : Type := F p
```

We do not want to abuse dependent types and leave these as simple references to expressions. The intent here is to build up the semantics with the understanding that `F = ZMod` and `FB = Bool`.

Next, define their respective 'conversion layer' to the 'ideal' Lean types. This is done by declaring an abbreviation of the specialised `Conversion` type, which is defined as follows:
```lean
structure Conversion (p : ℕ) (α : Type) where
  IdealT : Type                       -- The idealised Lean type for the `Clap` type
  conversion : IdealT → List (ZMod p) -- How to convert the ideal type into a sequence of `ZMod`s
  toExprs : α → List ExprRef          -- How to serialise the `Clap` type
```

Yes, this could be a typeclass. We choose to be explicit here.

Concretely for our types, we thus have:
```lean
abbrev F.conversion : Conversion p (F p) where
  IdealT       := ZMod p
  toExprs x    := [x]
  conversion x := [x]

abbrev FB.conversion : Conversion p (FB p) where
  IdealT       := Bool
  toExprs x    := [x]
  conversion x := [if x then 1 else 0]
```

### Defining a function over said datatypes
```lean
def eq {p : ℕ} [p.AtLeastTwo] (a b : F p) : ClapM p (FB p) := do
  isZero (←(a - b))
```
In other words, to implement whether `a = b`, we check their difference is zero. Recall that `isZero` is a primitive in the language. As a minor quirk, do note that arithmetic operations over `ExprRef`s (or `BoundRef p`s) are in `ClapM`. In particular, they access the underlying hash-consing state.

### Specifying the function

#### The infrastructure

Before we specify a monadic action, let us have a look at how to constrain a non-monadic value instead. We have the following bundle of four `Prop`s:
```lean
structure Converts
  (conversion : Conversion p α)
  (state : ClapMState p)
  (exprs : α)
  (val : conversion.IdealT)
: Prop where
  h_conversion :
    (conversion.conversion val).length = (conversion.toExprs exprs).length

  varSet_wf :
    ∀ (i : Fin (conversion.toExprs exprs).length),
      ⦃(conversion.toExprs exprs)[i], state.σ⦄.varSet_wellFormed state.numAlloc

  expr_wf :
    ∀ (i : Fin (conversion.toExprs exprs).length),
      ⦃(conversion.toExprs exprs)[i], state.σ⦄.wellFormed

  value_eq :
    ∀ (i : Fin (conversion.toExprs exprs).length),
      [state.varStore|⦃(conversion.toExprs exprs)[i], state.σ⦄] =
      .some ((conversion.conversion val)[i])
```
As scary as this looks, we promise that this is actually very straightforward. Furthermore, we normally do not need to interact with the contents of this definition. Normally. For an example as to when it _is_ necessary to do so, please use [`Clap/Lang/Data/FArray/zeroExtend.lean`](../Clap/Lang/Data/FArray/zeroExtend.lean)`:convertsM` as your starting point, up until the application of `FArray.converts_append`. That lemma ([Specialised.lean:433](../Clap/Model/Convert/Specialised.lean#L433)) and `FArray.converts_iff_FB_converts` beneath it ([Specialised.lean:313](../Clap/Model/Convert/Specialised.lean#L313)) are where `Converts` is taken apart field by field.

Anyway, there are essentially four statements this carries:
- `h_conversion` -- converting and serialising produces the same number of expressions.
- `varSet_wf` -- serialisation does not produce an expression that would refer to a yet-unallocated variable.
- `expr_wf` -- serialisation produces only hash-consed expressions.
- `value_eq` -- serialised expressions evaluate to the converted expressions at every index.

Now that we can relate Clap and 'lean' values, we can define the notion of specifying monadic actions. For this end, we use the `ConvertsM` bundle of three things:
```lean
structure ConvertsM
  (conversion : Conversion p α)
  (action : ClapM p α)
  (state : ClapMState p)
  (val : conversion.IdealT)
  (constraints : Prop)
: Prop where
  result :
    Converts
      conversion
      (action.getState state)
      (action.getResult state.numAlloc state.σ)
      val

  wellFormed : action.wellFormed state.numAlloc state.varStore state.σ

  constraints :
    (action.runAndEval state.numAlloc state.varStore state.σ).2.constraints ↔
    constraints
```
While quite wordy, not particularly complicated.
- `result` uses the above-described notion of `Converts` to relate the (functor-part) monadic result and the 'given' value `val`.
- `wellFormed` says that the `action` that goes in is well-formed.
- `constraints` say that the constraints obtained by running and evaluating the `action` hold if and only if the 'given' `constraints` hold.

#### The specification of `eq`
The name of the function gives away its specification. This better establish the inputs are equal. More formally:
```lean
lemma convertsM
  [p.AtLeastTwo]
  {a b : F p}
  {a_val b_val : ZMod p}
  (h_a : Converts F.conversion state a a_val)
  (h_b : Converts F.conversion state b b_val)
:
  ConvertsM FB.conversion (eq a b) state (a_val == b_val) (constraints := True)
```
In other words, given two inputs in the Clap-world `a b : F p`, we relate them to two Lean-world inputs `a_val b_val : ZMod p` using `h_a / h_b : Converts F.conversion ..`. The conclusion of this lemma poses the desired behaviour of the monadic program `eq a b` to be `a_val == b_val`. There are no constraints we are interested in, which reduces `constraints` of the `ConvertsM` to just 'constraints hold'.

### Proving the function correct with respect to the specification
All that is left to do is to prove the statement `convertsM` above. We proceed as follows:
```lean
lemma convertsM
  [p.AtLeastTwo]
  {a b : F p}
  {a_val b_val : ZMod p}
  (h_a : Converts F.conversion state a a_val)
  (h_b : Converts F.conversion state b b_val)
:
  ConvertsM FB.conversion (eq a b) state (a_val == b_val) True
:= by
  unfold eq
  rw [sub_def]
  step mkSub.convertsM h_a h_b as sub
  apply convertsM_of_convertsM (isZero.convertsM h_sub)
  . grind
  . grind
```
We will focus on infrastructure-specific steps here. Understand that `sub_def` unfolds to the following monadic sequence:
```lean
do
  let __do_lift ← liftM (HashConsM.mkSub a b)
  isZero __do_lift
```
As we alluded to above, we have infrastructure support for handling sequencing of well formed actions and doing the bookkeeping necessary to advance the proof state. More specifically, goals of the form `ConvertsM (do a₁; a₂; ...; aₙ)` should be addressed by inspecting the first action of the monad, here `mkSub` and using the `step` tactic. It takes a spec of an action, conventionally called `<action>.convertsM` and a name. Using our example, `step mkSub.convertsM h_a h_b` affects the proof state as follows:
- We get `sub : ClapM p (F p) := mkSub a b` in our context with the additional effect that all occurrences of `mkSub a b` are substituted by `sub`.
- We get `sub_result : F p` and `sub_state : ClapMState p` as shorthands for the result/state pair after the action executes within the `ClapM` monad.
- We get `h_wellFormed : sub.wellFormed state`. A majority of infrastructure (lemmas / the `step` tactic) need this notion around, but it just being here is normally the extent to which a user needs to interact with it. 
- We get `h_constraints : (sub.runAndEval state).2.constraints ↔ True` which imposes constraints introduced by the stepped action.
- We get `Converts F.conversion sub_state sub_result (a_val - b_val)` which is the effect of running the action, as described by the spec `mkSub.convertsM`.
- The conclusion changes in two ways*:
  - the state changes to `sub_state`
  - the action changes to `isZero sub_result`  

There is a minor asterisk here - the implementation of the `step` tactic sometimes mishandles the lift from `HashConsM` to `ClapM` and leaves the goal in a state that is only definitionally equal with the pretty state mentioned above. As such, if we so desired, in this proof we could simply write:
```lean
change ConvertsM FB.conversion
         (isZero sub_result)
         sub_state
         (a_val == b_val)
         (True → True)
```
This is an easy fix to the tactic, but timeboxing of the project is a real constraint.

Notably, the action is now `isZero sub_result`, i.e. a singular action with no additional bind sequencing. As such, we can use the spec `isZero.convertsM` to finish the goal. There is a variety of helpers available to align the misaligned bits if need be, please confer the existing examples in `Lang`.

There is also special support for `Functor.map` sequencing, which can be simply viewed as a `bind` with `pure`.

## Handling public inputs
Public inputs need a little bit of additional care as running circuits from pre-allocated state makes the notion of well-formed slightly tricky. We use the `AllocatedProgram` abstraction to reason about circuits that start from non-default states. It is defined as follows:
```lean
structure AllocatedProgram (p : ℕ) where
  InputT   : Type
  program  : InputT → ClapM p Unit
  numAlloc : ℕ
  allocate : HashConsM p InputT
```
This really just bundles a `program` for any 'pre-allocated' input type `InputT` with its allocator `allocate` that produces `numAlloc` allocations. We then define a couple of helper definitions.

First we have a bit of machinery to obtain the underlying circuit:
```lean
def getCircuit {p} (prog : AllocatedProgram p) : Circuit × HashConsSt p :=
  let (inputs, σ) := prog.allocate.run (HashConsSt.empty p)
  (
    (prog.program inputs).getCircuit prog.numAlloc σ,
    (prog.program inputs).getHashConsState prog.numAlloc σ
  )
```
Note that both `ClapM.getCircuit` and `ClapM.getHashConsState` used above `run` the `ClapM` monad, starting allocations at some `numAlloc`.

1. `getCircuit` starts with an empty `HashConsSt` and fills it in with the necessary expressions
   introduced by the `allocate` function.
2. We then build the circuit for the `program`, _notably_ starting at _not_ 0, but at `prog.numAlloc`,
   i.e. we are accounting for the number of allocations introduced by the allocator.
3. We also return the 'bootstrapped' `HashConsSt`.

And now we have a bit of machinery to obtain the underlying constraints:
```lean
def getConstraints {p} (prog : AllocatedProgram p) (inputs : Vector (ZMod p) prog.numAlloc) :=
  let (circuit, σ) := prog.getCircuit
  [.ofArray (inputs.toArray.zipIdx.map Prod.swap),
   σ,
   prog.numAlloc|circuit]ₑ.constraints
```

The only 'trick' here is that the varstore `Γ` is constructed by taking the first `prog.numAlloc` allocations. We can now easily refer to constraints of an 'allocated' circuit. For a full example, please confer [`Clap/Examples/PoseidonProgram.lean`](../Clap/Examples/PoseidonProgram.lean); the definitions above live in [`Clap/Model/AllocatedProgram.lean`](../Clap/Model/AllocatedProgram.lean).
