import Examples.VyperERC20.Spec
import Reasoning.Storage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

set_option maxRecDepth 2000000

namespace VyperERC20

/-! ## Vyper ERC20-local storage-store helpers -/

/-- Loading a Vyper ERC20 full-slot `uint256` location is the source-level integer value of the
same word. -/
theorem vyperERC20StorageLocLoad_uint256 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (vyperUint256Loc slot)
      = .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat) := by
  simpa [vyperUint256Loc, vyperWordLoc, uint256Loc] using storageLocLoad_uint256 evm slot

/-- Storing a full-slot Vyper `uint256` writes exactly the EVM word in the same slot. -/
theorem vyperERC20StorageLocStore_uint256 (evm : EVM.State) (slot val : UInt256) :
    storageLocStore evm (vyperUint256Loc slot) (.int (Int.ofNat val.toNat)) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot val) := by
  simpa [vyperUint256Loc, vyperWordLoc, uint256Loc] using
    storageLocStore_uint256 evm slot val

/-- `EVM.storageStore`'s account map is exactly the map carried by `RD.sstore`. -/
theorem vyperERC20StorageStore_accountMap (evm : EVM.State) (a : AccountAddress)
    (slot val : UInt256) :
    (Solm.EVM.storageStore evm a slot val).accountMap =
      sstoreAccountMap a evm.accountMap slot val := by
  exact storageStore_accountMap evm a slot val

/-- `EVM.storageStore` does not create accounts. -/
theorem vyperERC20StorageStore_createdAccounts (evm : EVM.State) (a : AccountAddress)
    (slot val : UInt256) :
    (Solm.EVM.storageStore evm a slot val).createdAccounts = evm.createdAccounts := by
  exact storageStore_createdAccounts evm a slot val

end VyperERC20
