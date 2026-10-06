import Examples.ERC20.Common
import Reasoning.Storage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace ERC20

/-! ## ERC20-local storage-store helper -/

/-- Storing a full-slot ERC20 `uint256` writes exactly the EVM word in the same slot. -/
theorem erc20StorageLocStore_uint256 (evm : EVM.State) (slot val : UInt256) :
    storageLocStore evm (erc20Uint256Loc slot) (.int (Int.ofNat val.toNat)) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot val) := by
  simpa [erc20Uint256Loc, uint256Loc] using storageLocStore_uint256 evm slot val

end ERC20
