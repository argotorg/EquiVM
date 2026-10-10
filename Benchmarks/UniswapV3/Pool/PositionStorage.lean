import Benchmarks.UniswapV3.Pool.Storage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.UniswapV3.Pool

def positionFieldWord (key : UInt256) (slotDelta offset size : Nat)
    (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (UInt256.div (solcSlotWordAt (solcMappingSlot ⟨7⟩ key + UInt256.ofNat slotDelta) σ I)
    (UInt256.ofNat (256 ^ offset))) (UInt256.ofNat (256 ^ size - 1))

theorem evalPositionUIntField (name : Ident) (slotDelta : Nat) (offset : Fin 32) (size : Fin 33)
    (width : ABI.BitWidth) (locals imms : Store) (evm : EVM.State) (key : UInt256)
    (hbase : locals.get? "positions" = none)
    (hkey : locals.get? "arg0" = some (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE key)))
    (htype : storageTypeAt? contract.storage
      ⟨"positions", [.mindex (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE key)), .field name]⟩ =
      some (.elem (.int (.uint width))))
    (hbound : offset.val + size.val - 1 < 32)
    (hloc : storageBackend.locate?
      ⟨"positions", [.mindex (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE key)), .field name]⟩ =
      some (.leaf { slot := solcMappingSlot ⟨7⟩ key + UInt256.ofNat slotDelta, offset := offset, size := size, hbound := hbound, type := .int (.uint width) }))
    (hwidth : width.val = 8 * size.val) (hoff : 8 * offset.val < 256) (hsize : 8 * size.val ≤ 256) :
    evalExpr? config {contract := contract, locals := locals, immutables := imms} evm
      (.storage ⟨"positions", [.mindex (.var "arg0"), .field name]⟩) =
      .ok (.int (Int.ofNat (positionFieldWord key slotDelta offset.val size.val
        evm.accountMap evm.executionEnv).toNat)) := by
  have hkeylen : (EVM.Word.toBytesBE key).length = 32 := by
    simpa using word_toBytesBE_toByteArray_size key
  rw [Std.HashMap.get?_eq_getElem?] at hkey
  apply evalExpr_storage_scalar_value hbase
    (by simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?, hkey,
      valueToKey?, hkeylen, EvalResult.bind, bind, pure, EvalResult.ofOption])
    htype poolStorageBackend_eq hloc
  rw [storageLocLoad_uint_offset _ _ _ _ _ hwidth hoff hsize,
    storageLoad_codeOwner_eq_solcSlotWordAt evm evm.executionEnv _ rfl]
  rfl

theorem evalPositionLiquidity (locals imms : Store) (evm : EVM.State) (key : UInt256)
    (hbase : locals.get? "positions" = none)
    (hkey : locals.get? "arg0" = some (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE key))) :
    evalExpr? config {contract := contract, locals := locals, immutables := imms} evm
      (.storage ⟨"positions", [.mindex (.var "arg0"), .field "liquidity"]⟩) =
      .ok (.int (Int.ofNat (positionFieldWord key 0 0 16 evm.accountMap evm.executionEnv).toNat)) := by
  apply evalPositionUIntField "liquidity" 0 0 16 ⟨128, by decide⟩ locals imms evm key
    hbase hkey rfl (by decide) ?_ rfl (by decide) (by decide)
  change some (StorageAddr.leaf { slot := solcMappingSlot ⟨7⟩ (keyValueToWord (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE key))), offset := 0, size := 16, hbound := by decide, type := .int (.uint ⟨128, by decide⟩) }) = _
  rw [keyValueToWord_fixedBytes32]
  simp only [show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl, u256_add_zero]

theorem evalPositionFeeGrowthInside0LastX128 (locals imms : Store) (evm : EVM.State) (key : UInt256)
    (hbase : locals.get? "positions" = none)
    (hkey : locals.get? "arg0" = some (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE key))) :
    evalExpr? config {contract := contract, locals := locals, immutables := imms} evm
      (.storage ⟨"positions", [.mindex (.var "arg0"), .field "feeGrowthInside0LastX128"]⟩) =
      .ok (.int (Int.ofNat (positionFieldWord key 1 0 32 evm.accountMap evm.executionEnv).toNat)) := by
  apply evalPositionUIntField "feeGrowthInside0LastX128" 1 0 32 ⟨256, by decide⟩ locals imms evm key
    hbase hkey rfl (by decide) ?_ rfl (by decide) (by decide)
  change some (StorageAddr.leaf { slot := solcMappingSlot ⟨7⟩ (keyValueToWord (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE key))) + UInt256.ofNat 1, offset := 0, size := 32, hbound := by decide, type := .int (.uint ⟨256, by decide⟩) }) = _
  rw [keyValueToWord_fixedBytes32]

theorem evalPositionFeeGrowthInside1LastX128 (locals imms : Store) (evm : EVM.State) (key : UInt256)
    (hbase : locals.get? "positions" = none)
    (hkey : locals.get? "arg0" = some (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE key))) :
    evalExpr? config {contract := contract, locals := locals, immutables := imms} evm
      (.storage ⟨"positions", [.mindex (.var "arg0"), .field "feeGrowthInside1LastX128"]⟩) =
      .ok (.int (Int.ofNat (positionFieldWord key 2 0 32 evm.accountMap evm.executionEnv).toNat)) := by
  apply evalPositionUIntField "feeGrowthInside1LastX128" 2 0 32 ⟨256, by decide⟩ locals imms evm key
    hbase hkey rfl (by decide) ?_ rfl (by decide) (by decide)
  change some (StorageAddr.leaf { slot := solcMappingSlot ⟨7⟩ (keyValueToWord (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE key))) + UInt256.ofNat 2, offset := 0, size := 32, hbound := by decide, type := .int (.uint ⟨256, by decide⟩) }) = _
  rw [keyValueToWord_fixedBytes32]

theorem evalPositionTokensOwed0 (locals imms : Store) (evm : EVM.State) (key : UInt256)
    (hbase : locals.get? "positions" = none)
    (hkey : locals.get? "arg0" = some (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE key))) :
    evalExpr? config {contract := contract, locals := locals, immutables := imms} evm
      (.storage ⟨"positions", [.mindex (.var "arg0"), .field "tokensOwed0"]⟩) =
      .ok (.int (Int.ofNat (positionFieldWord key 3 0 16 evm.accountMap evm.executionEnv).toNat)) := by
  apply evalPositionUIntField "tokensOwed0" 3 0 16 ⟨128, by decide⟩ locals imms evm key
    hbase hkey rfl (by decide) ?_ rfl (by decide) (by decide)
  change some (StorageAddr.leaf { slot := solcMappingSlot ⟨7⟩ (keyValueToWord (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE key))) + UInt256.ofNat 3, offset := 0, size := 16, hbound := by decide, type := .int (.uint ⟨128, by decide⟩) }) = _
  rw [keyValueToWord_fixedBytes32]

theorem evalPositionTokensOwed1 (locals imms : Store) (evm : EVM.State) (key : UInt256)
    (hbase : locals.get? "positions" = none)
    (hkey : locals.get? "arg0" = some (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE key))) :
    evalExpr? config {contract := contract, locals := locals, immutables := imms} evm
      (.storage ⟨"positions", [.mindex (.var "arg0"), .field "tokensOwed1"]⟩) =
      .ok (.int (Int.ofNat (positionFieldWord key 3 16 16 evm.accountMap evm.executionEnv).toNat)) := by
  apply evalPositionUIntField "tokensOwed1" 3 16 16 ⟨128, by decide⟩ locals imms evm key
    hbase hkey rfl (by decide) ?_ rfl (by decide) (by decide)
  change some (StorageAddr.leaf { slot := solcMappingSlot ⟨7⟩ (keyValueToWord (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE key))) + UInt256.ofNat 3, offset := 16, size := 16, hbound := by decide, type := .int (.uint ⟨128, by decide⟩) }) = _
  rw [keyValueToWord_fixedBytes32]

end Benchmarks.UniswapV3.Pool
