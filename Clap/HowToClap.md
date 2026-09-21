# Clapping

`ClapM p` in `Clap/eDSLState/Monad.lean` is _the_ Monad of the model. It is lawful.  
The `p` is the underlying prime which we fix and forget about, thus we can consider the `ClapM` monad. Furthermore, every monad in the stack is parameterised by `p` and receives the same treatment in this exposition. Every circuit we make is of type `ClapM Unit`, but of course, intermediate actions have an arbitrary functor type.

In a majority of cases, we use simple types, with some additional notion of well-formedness; the focus of the infrastructure is to minimise / eliminate the need to handle these notions explicitly. It is nevertheless useful to build an understanding of what they are in case an extension / alteration is needed. Or in case something unexepcted goes wrong, albeit I am not sure what that could be. I guess that is what unexpected means, ey? As such, we outline these well-formed conditions throughout the exposition, with the intent for them to be skimmed over and returned to only in case of emergency. This nevertheless serves as documentation, in addition to something for Claude to read.

`ClapM` itself is a stack of the following monads:
- `StateM ℕ` - The `ℕ` here is always named `numAlloc`, and it stores the number of allocations
  the circuit has made.
- `StateM HashConsSt` - The `HashConsSt` here is always named `σ`, and it stores the the underlying hash-consed representation of all encountered expressions.
- `WriterM Circuit` - The `Circuit` here is always named `circuit`, and it stores the accumulated
  sequence of gates as constructed by the eDSL.

NB `ClapM` is the circuit 'builder', _not_ evaluator.

As far as `ClapM` can tell, an expression is just a pointer of type `ExprRef`. One can also encounter `BoundRef p` which is a synonym for `ExprRef` that carries `p` for the purposes of typeclass inference. These references point into the `HashConsSt`, which itself stores an array of hash-consed expressions of type `CacheExpr`. A hash-consed expression composes expressions of parts. As such, compound expressions store references to subexpressions. This gives rise to a natural notion of well-formedness, i.e. a `CacheExpr` is well-formed with respect to some index `ref : ExprRef` iff any reference contained within precedes `ref`. The immediate corolary of this is that atomic `CacheExpr`s, constants and variables, are vacuously well-formed. This notion then further induces well-formedness of `HashConsSt`, which is bundled with the type and states the obvious -- any expression at index `i` is well-formed up to `i`. With all of that said, _do not_ use the `CacheExpr` representation directly. There is practically never a reason to so much as utter this type, unless doing fundamental changes to the infrastructure. Please consider restructuring your approach if you need to state anything in its terms.

Tip: If `a b : ExprRef`, then `a + b` | `a - b` | `a * b` will fail to infer the `p` for the underlying monad. A frictionless fix is to annotate the type of `a`/`b` explicitly with `BoundRef p`.

As such, an `ExprRef` in isolation, i.e. without an accompanying `HashConsSt` is meaningless. We therefore use `Expr` as a bundle of `ref : ExprRef` and a `σ : HashConsSt`. We say that `Expr` is well formed iff `ref < σ.size`; in other words, it is well formed if a dereference of a `ref` yields a `.some (_ : CacheExpr)`.

Expressions can be evaluated with respect to a particular variable store, typed `VarStore` throuhgout. It is a mapping from a trace index to a value in `ZMod p`, always named `Γ` or `varStore`. The notation `[Γ|e]` evaluates `e : Expr` in the context of `Γ : VarStore`.

`Circuit`s can be evaluated similarly, however please do note that we need an extra bit of state to evaluate an arbitrary `Circuit`, namely the `numAlloc`, which is serving here as a notion of validity of an allocation. As such, we need a `Γ`, `σ` and a `numAlloc`. This bundle is `ClapMState`. We have the following syntax for evaluating circuits: `[Γ, σ, numAlloc|circuit]ₑ : EvalSt`.

`EvalSt` can be thought of as circuit evaluation state. It carries its `numAlloc` and `Γ`, together with `constraints : Prop`. Constraints is the set of constarints accumulated throughout evaluation of a circuit.

Clap programs are sequences of monadic actions within the `ClapM` monad. Put differently, a statement in the `ClapM` monad is an expression of a circuit in the Clap eDSL. There are five (5) atomic operations / gates; namely:
- `eq0`
- `share`
- `isZero`
- `num2bits`
- `fpmul`

These are the atoms of the eDSL. Everything else is monadic Lean code. `ClapM` actions carry their notion of well-formedness as well. This notion is _not_ invisible when reasoning about `ClapM` circuits, but can be, for most intents and purposes, ignored.
