# Clapping

`ClapM p` in `Clap/eDSLState/Monad.lean` is _the_ Monad of the model. It is lawful.  
The `p` is the underlying prime which we fix and forget about, thus we can consider the `ClapM` monad. Furthermore, every monad in the stack is parameterised by `p` and receives the same treatment in this exposition. Every circuit we make is of type `ClapM Unit`, but of course, intermediate actions have an arbitrary functor type.

`ClapM` itself is a stack of the following monads:
- `StateM ℕ` - The `ℕ` here is always named `numAlloc`, and it stores the number of allocations
  the circuit has made.
- `StateM HashConsSt` - The `HashConsSt` here is always named `σ`, and it stores the the underlying hash-consed representation of all encountered expressions.
- `WriterM Circuit` - The `Circuit` here is always named `circuit`, and it stores the accumulated
  sequence of gates as constructed by the eDSL.

NB `ClapM` is the circuit 'builder', _not_ evaluator.

As far as `ClapM` can tell, an expression is just a pointer of type `ExprRef` into the `HashConsSt`, which itself stores an array of hash-consed expressions of type `CacheExpr`; _do not_ use this representation directly - it is an implementation detail. One can also encounter `BoundRef p` which is a synonym for `ExprRef` that carries `p` for the purposes of typeclass inference.

Tip: If `a b : ExprRef`, then `a + b` | `a - b` | `a * b` will fail to infer the `p` for the underlying monad. A frictionless fix is to annotate the type of `a`/`b` explicitly with `BoundRef p`.

As such, an `ExprRef` in isolation, i.e. without an accompanying `HashConsSt` is meaningless. We therefore use `Expr` as a bundle of `ref : ExprRef` and a `σ : HashConsSt`. We say that `Expr` is well formed iff `ref < σ.size`. 

Technical note: `HashConsSt` carries its own notion of wellformed-ness. Don't worry about it.

Expressions can be evaluated with respect to a particular variable store, typed `VarStore` throuhgout. It is a mapping from a trace index to a value in `ZMod p`, always named `Γ` or `varStore`. The notation `[Γ|e]` evaluates `e : Expr` in the context of `Γ : VarStore`.

`Circuit`s can be evaluated similarly, however please do note that we need an extra bit of state to evaluate an arbitrary `Circuit`, namely the `numAlloc`, which is serving here as a notion of validity of an allocation. As such, we need a `Γ`, `σ` and a `numAlloc`. This bundle is `ClapMState`. We have the following syntax for evaluating circuits: `[Γ, σ, numAlloc|circuit]ₑ : EvalSt`.

`EvalSt` can be thought of as circuit evaluation state. It carries its `numAlloc` and `Γ`, together with `constraints : Prop`. Constraints is the set of constarints accumulated throughout evaluation of a circuit.