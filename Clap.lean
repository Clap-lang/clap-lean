import Clap.Model.All
import Clap.Lang.All
import Clap.RandomOracle.HashFn
import Clap.RandomOracle.RandomOracle
import Clap.FiatShamir.Polynomial
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
| `Clap/RandomOracle/` | hash families (`HashFn`), random-oracle queries, and the random oracle itself: uniformity, Schwartz–Zippel, the fresh-query lemma. Below `Lang/` |
| `Clap/FiatShamir/` | the polynomial algebra behind the Fiat–Shamir checks: what the substring and concatenation identities mean, and root counting. Below `Lang/` |
| `Clap/Lang/` | the gadget library: `Gate/`, then `Core/`, then `Poseidon/`, then `Data/` (hash-to-field and the Fiat–Shamir string checks included) |
| `Clap/Keyless/` | the Aptos Keyless application |
| `Clap/Examples/` | worked end-to-end programs |
| `Clap/Test/` | executable checks of the back end |
| `old/` | the previous `Option`/`ZMod` model, kept as reference and never built |
-/
