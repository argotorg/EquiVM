import Benchmarks.Morpho.MetaMorphoV1_1.Bytecode
import Benchmarks.Morpho.MetaMorphoV1_1.Immutables
import Reasoning.Immutables

/-!
The patch sites of the deployed runtime template, keyed by Solm immutable name.  Generated
summaries quantify the words written at these sites; `Reasoning.Immutables.wordsOf` supplies them
from a Solm immutables store.
-/

open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

/-- Patch sites in the deployed runtime template. -/
def immutableLayout : Layout :=
  ⟨immutableReferences.flatMap (fun (name, sites) =>
    sites.map (fun offset => (offset, 32, name)))⟩

end Benchmarks.Morpho.MetaMorphoV1_1
