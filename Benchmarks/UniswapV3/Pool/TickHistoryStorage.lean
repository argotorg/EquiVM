import Benchmarks.UniswapV3.Pool.TickLiquidityStorage
import Benchmarks.UniswapV3.Pool.TickFeeModel
import Benchmarks.UniswapV3.Pool.PackedFieldWord

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

inductive TickHistoryField where
  | cumulative
  | secondsPerLiquidity
  | seconds
  | initialized

def TickHistoryField.name : TickHistoryField → Ident
  | .cumulative => "tickCumulativeOutside"
  | .secondsPerLiquidity => "secondsPerLiquidityOutsideX128"
  | .seconds => "secondsOutside"
  | .initialized => "initialized"

def TickHistoryField.bits : TickHistoryField → Nat × Nat
  | .cumulative => (0, 56)
  | .secondsPerLiquidity => (56, 160)
  | .seconds => (216, 32)
  | .initialized => (248, 8)

def tickHistoryLoc (tick : Int) : TickHistoryField → StorageLoc
  | .cumulative => tickClearCumulativeLoc tick
  | .secondsPerLiquidity => tickClearSecondsPerLiquidityLoc tick
  | .seconds => tickClearSecondsLoc tick
  | .initialized => tickClearInitializedLoc tick

def tickHistoryUpdate (field : TickHistoryField) (old value : UInt256) : UInt256 :=
  packedFieldUpdate old value field.bits.1 field.bits.2

def tickHistoryState (evm : EVM.State) (tick : Int) (field : TickHistoryField)
    (word : UInt256) : EVM.State :=
  modifyStorageWord evm (tickFieldSlot tick 3) (fun old ↦ tickHistoryUpdate field old word)

theorem assignTickHistory (locals imms : Store) (evm : EVM.State) (bindingName : Ident)
    (tick : Int) (field : TickHistoryField) (value : Value) (word : UInt256)
    (hget : locals.get? bindingName = some (tickAlias tick)) (hv : valueToWord value = some word) :
    assignStorageRef? config {contract := contract, locals := locals, immutables := imms} evm
      .storage ⟨bindingName, [.field field.name]⟩ value =
      .ok ({contract := contract, locals := locals, immutables := imms},
        tickHistoryState evm tick field word) := by
  apply assignTickAliasField field.name (tickHistoryLoc tick field).type (tickHistoryLoc tick field)
    locals imms evm _ bindingName tick value hget
  · cases field <;> rfl
  · cases field <;> rfl
  · have h := storageLocStore_packedValue evm (tickHistoryLoc tick field) value word hv
      (by cases field <;> rfl)
    cases field <;> exact h

theorem tickHistoryState_executionEnv (evm : EVM.State) (tick : Int) (field : TickHistoryField)
    (word : UInt256) : (tickHistoryState evm tick field word).executionEnv = evm.executionEnv :=
  storageStore_executionEnv _ _ _ _

def tickHistoryMap (σ : AccountMap) (ee : ExecutionEnv) (tick : Int)
    (field : TickHistoryField) (word : UInt256) : AccountMap :=
  sstoreAccountMap ee.codeOwner σ (tickFieldSlot tick 3)
    (tickHistoryUpdate field (solcSlotWordAt (tickFieldSlot tick 3) σ ee) word)

theorem SourceState.tickHistory {s0 : EVM.State} {ee : ExecutionEnv} {σ : AccountMap}
    {evm : EVM.State} (hs : SourceState s0 ee σ evm) (tick : Int)
    (field : TickHistoryField) (word : UInt256) :
    SourceState s0 ee (tickHistoryMap σ ee tick field word)
      (tickHistoryState evm tick field word) :=
  hs.readModifyWrite (tickFieldSlot tick 3) (fun old ↦ tickHistoryUpdate field old word)

def tickFeeOutsideState (evm : EVM.State) (tick : Int) (second : Bool) (word : UInt256) : EVM.State :=
  EVM.storageStore evm evm.executionEnv.codeOwner (tickFieldSlot tick (if second then 2 else 1)) word

theorem assignTickFeeOutside (locals imms : Store) (evm : EVM.State) (bindingName : Ident)
    (tick : Int) (second : Bool) (word : UInt256)
    (hget : locals.get? bindingName = some (tickAlias tick)) :
    assignStorageRef? config {contract := contract, locals := locals, immutables := imms} evm
      .storage ⟨bindingName, [.field (tickFeeOutsideName second)]⟩ (.int (Int.ofNat word.toNat)) =
      .ok ({contract := contract, locals := locals, immutables := imms},
        tickFeeOutsideState evm tick second word) := by
  apply assignTickAliasField (tickFeeOutsideName second) (.int (.uint ⟨256, by decide⟩))
    (uint256Loc (tickFieldSlot tick (if second then 2 else 1)))
    locals imms evm _ bindingName tick _ hget
  · cases second <;> rfl
  · cases second <;> rfl
  · exact storageLocStore_uint256 evm _ word

theorem tickFeeOutsideState_executionEnv (evm : EVM.State) (tick : Int) (second : Bool)
    (word : UInt256) : (tickFeeOutsideState evm tick second word).executionEnv = evm.executionEnv :=
  storageStore_executionEnv _ _ _ _

end Benchmarks.UniswapV3.Pool
