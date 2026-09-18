import Clap.Model.All
import Clap.Lang.All
import Clap.Poseidon.Poseidon
import Clap.Keyless.Allocate
import Clap.Examples.PoseidonProgram
import Clap.Test.Backend

/-!
# CLAP

A compiler from a subset of Lean 4 to circuits for SNARK proof systems, and the proofs that
it preserves semantics.

The tree is layered; this file imports the top of each layer.

| Directory | What it holds |
|---|---|
| `Clap/Util/` | model-agnostic maths and Lean/Std lemmas |
| `Clap/Tactic/` | proof automation, chiefly the `step` tactic |
| `Clap/Model/` | the `ClapM` model: expression heap, monad, semantics, refinement, back ends |
| `Clap/Lang/` | the gadget library — `Gate/`, then `Core/`, then `Data/` |
| `Clap/Poseidon/` | the Poseidon hash, as a gadget package of its own |
| `Clap/Keyless/` | the Aptos Keyless application |
| `Clap/Examples/` | worked end-to-end programs |
| `Clap/Test/` | executable checks of the back end |
| `old/` | the previous `Option`/`ZMod` model, kept as reference and never built |

See [docs/repo-layout.md](docs/repo-layout.md) for the rules that keep those layers apart, and
[docs/clap-agent-guide.md](docs/clap-agent-guide.md) before changing any circuit.
-/
