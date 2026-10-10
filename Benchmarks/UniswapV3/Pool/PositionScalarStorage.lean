import Benchmarks.UniswapV3.Pool.PositionOwedStorage
import Benchmarks.UniswapV3.Pool.TickLiquidityStorage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

def positionLiquidityState (evm : EVM.State) (key word : UInt256) : EVM.State :=
  EVM.storageStore evm evm.executionEnv.codeOwner (solcMappingSlot ⟨7⟩ key)
    (protocolFeeUpdateWord false
      (EVM.storageLoad evm evm.executionEnv.codeOwner (solcMappingSlot ⟨7⟩ key)) word)

theorem assignPositionLiquidity (locals imms : Store) (evm : EVM.State) (bindingName : Ident)
    (key : UInt256) (value : Int) (hget : locals.get? bindingName = some (positionAlias key)) :
    assignStorageRef? config {contract := contract, locals := locals, immutables := imms} evm .storage
      ⟨bindingName, [.field "liquidity"]⟩ (.int value) =
      .ok ({contract := contract, locals := locals, immutables := imms},
        positionLiquidityState evm key (EVM.wordOfInt value)) := by
  apply assignStorageRef_resolved_scalar
    (resolvePositionAliasField locals imms evm bindingName "liquidity" key _ hget rfl)
    poolStorageBackend_eq
    (loc := {
      slot := solcMappingSlot ⟨7⟩ key
      offset := 0
      size := 16
      type := .int (.uint ⟨128, by decide⟩)
      hbound := by decide})
  · change some (StorageAddr.leaf {
      slot := solcMappingSlot ⟨7⟩ (keyValueToWord
        (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE key)))
      offset := 0
      size := 16
      type := .int (.uint ⟨128, by decide⟩)
      hbound := by decide}) = _
    rw [keyValueToWord_fixedBytes32]
  · exact storageLocStore_pair128Value evm (solcMappingSlot ⟨7⟩ key) false _
      (.int value) (EVM.wordOfInt value) rfl

def positionLastField (second : Bool) : Ident :=
  if second then "feeGrowthInside1LastX128" else "feeGrowthInside0LastX128"

def positionLastState (evm : EVM.State) (key : UInt256) (second : Bool) (word : UInt256) : EVM.State :=
  EVM.storageStore evm evm.executionEnv.codeOwner
    (solcMappingSlot ⟨7⟩ key + UInt256.ofNat (if second then 2 else 1)) word

theorem assignPositionLast (locals imms : Store) (evm : EVM.State) (bindingName : Ident)
    (key : UInt256) (second : Bool) (word : UInt256)
    (hget : locals.get? bindingName = some (positionAlias key)) :
    assignStorageRef? config {contract := contract, locals := locals, immutables := imms} evm .storage
      ⟨bindingName, [.field (positionLastField second)]⟩ (.int (Int.ofNat word.toNat)) =
      .ok ({contract := contract, locals := locals, immutables := imms},
        positionLastState evm key second word) := by
  apply assignStorageRef_resolved_scalar
    (resolvePositionAliasField locals imms evm bindingName (positionLastField second) key _ hget
      (by cases second <;> rfl)) poolStorageBackend_eq
    (loc := uint256Loc (solcMappingSlot ⟨7⟩ key + UInt256.ofNat (if second then 2 else 1)))
  · cases second
    all_goals
      change some (StorageAddr.leaf (uint256Loc
        (solcMappingSlot ⟨7⟩ (keyValueToWord (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE key))) +
          UInt256.ofNat _))) = _
      rw [keyValueToWord_fixedBytes32]
      rfl
  · exact storageLocStore_uint256 evm _ word

theorem positionLiquidityState_executionEnv (evm : EVM.State) (key word : UInt256) :
    (positionLiquidityState evm key word).executionEnv = evm.executionEnv :=
  storageStore_executionEnv _ _ _ _

theorem positionLastState_executionEnv (evm : EVM.State) (key : UInt256) (second : Bool)
    (word : UInt256) : (positionLastState evm key second word).executionEnv = evm.executionEnv :=
  storageStore_executionEnv _ _ _ _

end Benchmarks.UniswapV3.Pool
