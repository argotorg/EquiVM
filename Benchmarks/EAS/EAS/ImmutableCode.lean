import Benchmarks.EAS.EAS.Bytecode
import Benchmarks.EAS.EAS.Immutables
import Reasoning.Immutables

/-!
The patch sites of the deployed runtime template, keyed by Solm immutable name.  Generated
summaries quantify the words written at these sites; `Reasoning.Immutables.wordsOf` supplies them
from a Solm immutables store.
-/

open Reasoning.Immutables
open Benchmarks.EAS.EAS.Immutables

namespace Benchmarks.EAS.EAS

/-- Patch sites in the deployed runtime template. -/
def immutableLayout : Layout :=
  ⟨immutableReferences.flatMap (fun (name, sites) =>
    sites.map (fun offset => (offset, 32, name)))⟩

end Benchmarks.EAS.EAS
