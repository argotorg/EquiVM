import Reasoning.ABIViews
import Examples.OpenZeppelinBench.AccessControl.Common
import Reasoning.Storage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace OpenZeppelinBench.AccessControl

/-!
# AccessControl benchmark storage helpers

Helpers for the `_roles` nested mapping layout and full-slot/low-byte storage load-store facts.
-/


theorem accessControlStorageLocLoad_bytes32 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (bytes32Loc slot)
      = .fixedBytes ⟨31, by decide⟩
          (EVM.Word.toBytesBE (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)) := by
  simpa [bytes32Loc] using storageLocLoad_bytes32 evm slot


end OpenZeppelinBench.AccessControl
