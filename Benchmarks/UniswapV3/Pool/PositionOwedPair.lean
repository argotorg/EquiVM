import Benchmarks.UniswapV3.Pool.PositionOwedStorage
import Benchmarks.UniswapV3.Pool.StorageWordUpdate

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem protocolFeeUpdateWord_comm (old value0 value1 : UInt256) :
    protocolFeeUpdateWord true (protocolFeeUpdateWord false old value0) value1 =
      protocolFeeUpdateWord false (protocolFeeUpdateWord true old value1) value0 := by
  apply u256_inj
  rw [protocolFeeUpdateWord_true_toNat, protocolFeeUpdateWord_false_toNat,
    protocolFeeUpdateWord_false_toNat, protocolFeeUpdateWord_true_toNat]
  omega

theorem storePositionOwedPair_eq (evm : EVM.State) (key value0 value1 : UInt256) :
    storePositionOwed (storePositionOwed evm key false value0) key true value1 =
      modifyStorageWord evm (solcMappingSlot ⟨7⟩ key + UInt256.ofNat 3)
        (fun old ↦ protocolFeeUpdateWord false (protocolFeeUpdateWord true old value1) value0) := by
  change modifyStorageWord
    (modifyStorageWord evm (solcMappingSlot ⟨7⟩ key + UInt256.ofNat 3)
      (fun old ↦ protocolFeeUpdateWord false old value0))
    (solcMappingSlot ⟨7⟩ key + UInt256.ofNat 3)
    (fun old ↦ protocolFeeUpdateWord true old value1) = _
  rw [modifyStorageWord_comp]
  congr 1
  funext old
  exact protocolFeeUpdateWord_comm old value0 value1

end Benchmarks.UniswapV3.Pool
