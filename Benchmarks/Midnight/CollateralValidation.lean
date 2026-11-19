import Benchmarks.Midnight.CollateralLifSource
import Benchmarks.Midnight.EnableSource
import Benchmarks.Midnight.MarketBytesMemory
import Benchmarks.Midnight.PositionUpdateMemory

/-! Shared source/runtime conditions for a collateral in a newly created market. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def collateralEnabledWord (evm : EVM.State) (cursor : Bool) (key : UInt256) : UInt256 :=
  UInt256.land (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner
    (solcMappingSlot (enableSlot cursor) key)) ⟨255⟩

def CollateralValid (evm : EVM.State) (previous : AccountAddress) (c : CollateralData) : Prop :=
  previous.val < c.token.val ∧ collateralEnabledWord evm false c.lltv ≠ ⟨0⟩ ∧
    collateralEnabledWord evm true c.liquidationCursor ≠ ⟨0⟩ ∧
    CollateralLifSafe c.lltv c.liquidationCursor

def collateralValidationMemory (mem : ByteArray) (c : CollateralData) : ByteArray :=
  twoWordHashMem c.liquidationCursor (UInt256.ofNat 8)
    (twoWordHashMem c.lltv (UInt256.ofNat 7) mem)

theorem collateralValidationMemory_prefix (mem : ByteArray) (c : CollateralData) (limit : Nat) :
    MemoryPrefix mem (collateralValidationMemory mem c) limit :=
  (twoWordHashMem_prefix mem c.lltv (UInt256.ofNat 7) limit).trans
    (twoWordHashMem_prefix _ c.liquidationCursor (UInt256.ofNat 8) limit)

theorem collateralValidationMemory_free (mem : ByteArray) (c : CollateralData)
    (hin : 96 ≤ mem.size) :
    memLoad (UInt256.ofNat 64) (collateralValidationMemory mem c) =
      memLoad (UInt256.ofNat 64) mem := by
  rw [collateralValidationMemory, memLoad_twoWordHashMem _ _ (UInt256.ofNat 64) (by decide) (by
    rw [twoWordHashMem_size_of_ge_64 _ _ (by omega)]; exact hin),
    memLoad_twoWordHashMem _ _ (UInt256.ofNat 64) (by decide) hin]

theorem evalCollateralEnabled {frame : Frame} {evm : EVM.State} {key : UInt256}
    (cursor : Bool) (hc : frame.contract = contract)
    (hn : frame.locals.get? (enableName cursor) = none)
    (hk : frame.locals.get? (enableArg cursor) = some (.int key.toNat)) :
    evalExpr? config frame evm
      (.storage { base := enableName cursor, steps := [.mindex (.var (enableArg cursor))] }) =
      .ok (.bool (decide (collateralEnabledWord evm cursor key ≠ ⟨0⟩))) := by
  apply evalExpr_storage_scalar_value (loc := boolOffset0Loc (solcMappingSlot (enableSlot cursor) key))
    (er := { base := enableName cursor, steps := [.mindex (.int key.toNat)] })
    (t := .bool) hn
  · simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?, hk,
      EvalResult.ofOption, bind, pure, EvalResult.bind, valueToKey?]
  · rw [hc]; cases cursor <;> rfl
  · rfl
  · cases cursor <;>
      change some (StorageAddr.leaf (boolOffset0Loc (solcMappingSlot _
        (keyValueToWord (.int (Int.ofNat key.toNat)))))) = _ <;> rw [keyValueToWord_uint256] <;> rfl
  · by_cases hz : collateralEnabledWord evm cursor key = ⟨0⟩
    · rw [decide_eq_false (not_not.mpr hz)]
      exact storageLocLoad_bool_offset0_false evm _ hz
    · rw [decide_eq_true hz]
      exact storageLocLoad_bool_offset0_true evm _ hz

end Benchmarks.Midnight
