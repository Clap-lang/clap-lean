import Clap.Model.Monad

/-!
# Programs with public inputs

An `AllocatedProgram` bundles a circuit-building function with the allocator that turns its
Lean-level argument into circuit variables, plus the number of variables that takes. The
contract that public input `i` is circuit variable `i` is maintained by allocating in order
and by nothing else.

The allocators themselves live in [PublicInput.lean](PublicInput.lean); a worked end-to-end
example is [Clap/Examples/PoseidonProgram.lean](../Examples/PoseidonProgram.lean), and
[docs/public-inputs.md](../../docs/public-inputs.md) explains the whole layer.
-/

namespace Clap

/--
Recall that `HashConsM` lifts to `ClapM`.

`AllocatedProgram` allows us to treat inputs received in a Lean function as 'circuit public inputs',
appropriately allocated in the underlying `ClapM` state.

The action `allocate` is the allocator of `numAlloc` allocations for the given `program`.
Note that `liftM allocate >>= program` is a valid composition in `ClapM`.

NB:
Technically, `allocate` should actually just fill the `numAlloc`, but whatever.
This will likely just be used once at the top level (depending on the proof structure),
and we have the ingredients for keyless. Namely: in `Clap/Keyless/Allocate.lean` we have:
- allocateKeyless : `HashConsM p (FKeylessInput p)`, i.e. the `allocate` function
- allocateKeylessWidth : `ℕ`, i.e. the `numAlloc`
-/
structure AllocatedProgram (p : ℕ) where
  InputT : Type
  program : InputT → ClapM p Unit
  numAlloc : ℕ
  allocate : HashConsM p InputT

namespace AllocatedProgram

/-
One can treat these opaquely really.
-/

/--
Recall that `ClapM.getCircuit` and `ClapM.getHashConsState` both `run` the `ClapM`,
starting allocations at some `numAlloc`.

1. `getCircuit` starts with an empty `HashConsSt` and fills it in with necessary expressions
  introduced by the `allocate` function
2. We then build the circuit for the `program`, _notably_ starting at _not_ 0, but at `prog.numAlloc`,
   i.e. we are accounting for the number of allocations introduced by the allocator.
3. We also return the 'bootstrapped' `HashConsState`.
-/
def getCircuit {p} (prog : AllocatedProgram p) : Circuit × HashConsSt p :=
  let (inputs, σ) := prog.allocate.run (HashConsSt.empty p)
  (
    (prog.program inputs).getCircuit prog.numAlloc σ,
    (prog.program inputs).getHashConsState prog.numAlloc σ
  )

/--
Recall that `[Γ, σ, numAlloc|circuit]ₑ` evluates the `circuit` in the `ClapMState`
`⟨Γ, σ, numAlloc⟩`, i.e. varstore, hash-cons state and number of allocations respectively.

- The only trick here is that the varstore `Γ` is constructed by taking the first `prog.numAlloc`
  allocations. NB this is already `HashConsState`-consistent because `σ` is the post-`allocate` `σ`.
-/
def getConstraints {p} (prog : AllocatedProgram p) (inputs : Vector (ZMod p) prog.numAlloc) :=
  let (circuit, σ) := prog.getCircuit
  [.ofArray (inputs.toArray.zipIdx.map Prod.swap), σ, prog.numAlloc|circuit]ₑ.constraints

end AllocatedProgram

end Clap
