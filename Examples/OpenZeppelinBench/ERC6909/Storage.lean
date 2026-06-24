import Examples.OpenZeppelinBench.ERC6909.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace OpenZeppelinBench.ERC6909

/-! ## ERC6909-wide storage helpers -/

/-- Loading a full-slot Solidity `uint256` returns the source-level integer for that word. -/
theorem erc6909StorageLocLoad_uint256 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (wordLoc slot)
      = .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat) := by
  simpa [wordLoc, uint256Loc] using storageLocLoad_uint256 evm slot

/-- Storing a full-slot Solidity `uint256` is the corresponding EVM storage write. -/
theorem erc6909StorageLocStore_uint256 (evm : EVM.State) (slot val : UInt256) :
    storageLocStore evm (wordLoc slot) (.int (Int.ofNat val.toNat)) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot val) := by
  simpa [wordLoc, uint256Loc] using storageLocStore_uint256 evm slot val

end OpenZeppelinBench.ERC6909
