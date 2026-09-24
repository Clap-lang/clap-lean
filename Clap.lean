import Clap.Model.All
import Clap.Lang.All
import Clap.Poseidon.Computes
import Clap.Poseidon.HashToField.hash64BitLimbsToField
import Clap.Poseidon.HashToField.hashBytesToField
import Clap.Poseidon.HashToField.hashElemsToField
import Clap.Poseidon.Poseidon
import Clap.Poseidon.RandomOracle
import Clap.Keyless.Allocate
import Clap.Examples.PoseidonProgram
import Clap.Examples.RangeCheckedLessThan
import Clap.Test.Backend

/-!
# CLAP

| Directory | What it holds |
|---|---|
| `Clap/Util/` | model-agnostic maths and Lean/Std lemmas |
| `Clap/Tactic/` | proof automation, chiefly the `step` tactic |
| `Clap/Model/` | the `ClapM` model, expression heap, monad, semantics, refinement, back ends |
| `Clap/Lang/` | the gadget library: `Gate/`, then `Core/`, then `Data/` |
| `Clap/Poseidon/` | the Poseidon hash, what the library assumes of it (`Computes`), its random-oracle idealisation, and the hash-to-field gadgets built on it |
| `Clap/Keyless/` | the Aptos Keyless application |
| `Clap/Examples/` | worked end-to-end programs |
| `Clap/Test/` | executable checks of the back end |
| `old/` | the previous `Option`/`ZMod` model, kept as reference and never built |
-/
