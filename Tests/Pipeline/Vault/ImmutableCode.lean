import Tests.Pipeline.Vault.Bytecode
import Tests.Pipeline.Vault.Immutables
import Reasoning.Immutables

/-!
The patch sites of the deployed runtime template, keyed by Solm immutable name.  Generated
summaries quantify the words written at these sites; `Reasoning.Immutables.wordsOf` supplies them
from a Solm immutables store.
-/

open Reasoning.Immutables
open Tests.Pipeline.Vault.Immutables

namespace Tests.Pipeline.Vault

/-- Patch sites in the deployed runtime template. -/
def immutableLayout : Layout :=
  ⟨immutableReferences.flatMap (fun (name, sites) =>
    sites.map (fun offset => (offset, 32, name)))⟩

end Tests.Pipeline.Vault
