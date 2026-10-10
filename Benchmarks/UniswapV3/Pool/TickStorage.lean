import Benchmarks.UniswapV3.Pool.Storage
import Benchmarks.UniswapV3.Pool.SignedWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.UniswapV3.Pool

def tickFieldSlot (key : Int) (slotDelta : Nat) : UInt256 :=
  solcMappingSlot ⟨5⟩ (EVM.wordOfInt key) + UInt256.ofNat slotDelta

def tickFieldWord (key : Int) (slotDelta offset size : Nat)
    (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (UInt256.div (solcSlotWordAt (tickFieldSlot key slotDelta) σ I)
    (UInt256.ofNat (256 ^ offset))) (UInt256.ofNat (256 ^ size - 1))

def tickSignedFieldValue (key : Int) (slotDelta offset : Nat) (width : ABI.BitWidth)
    (σ : AccountMap) (I : ExecutionEnv) : Int :=
  normalizeInt (.sint width) (Int.ofNat
    (UInt256.div (solcSlotWordAt (tickFieldSlot key slotDelta) σ I)
      (UInt256.ofNat (256 ^ offset))).toNat)

theorem evalTickField (name : Ident) (ty : ABI.ElemType) (loc : StorageLoc)
    (locals imms : Store) (evm : EVM.State) (key : Int)
    (hbase : locals.get? "ticks" = none) (hkey : locals.get? "arg0" = some (.int key))
    (htype : storageTypeAt? contract.storage ⟨"ticks", [.mindex (.int key), .field name]⟩ =
      some (.elem ty))
    (hloc : storageBackend.locate? ⟨"ticks", [.mindex (.int key), .field name]⟩ = some (.leaf loc)) :
    evalExpr? config {contract := contract, locals := locals, immutables := imms} evm
      (.storage ⟨"ticks", [.mindex (.var "arg0"), .field name]⟩) = .ok (storageLocLoad evm loc) := by
  rw [Std.HashMap.get?_eq_getElem?] at hkey
  exact evalExpr_storage_scalar hbase
    (by simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?, hkey,
      valueToKey?, EvalResult.bind, bind, pure, EvalResult.ofOption])
    htype poolStorageBackend_eq hloc

theorem evalTickLiquidityGross (locals imms : Store) (evm : EVM.State) (key : Int)
    (hbase : locals.get? "ticks" = none) (hkey : locals.get? "arg0" = some (.int key)) :
    evalExpr? config {contract := contract, locals := locals, immutables := imms} evm
      (.storage ⟨"ticks", [.mindex (.var "arg0"), .field "liquidityGross"]⟩) =
      .ok (.int (Int.ofNat (tickFieldWord key 0 0 16 evm.accountMap evm.executionEnv).toNat)) := by
  rw [evalTickField "liquidityGross" (.int (.uint ⟨128, by decide⟩))
    { slot := tickFieldSlot key 0, offset := 0, size := 16, hbound := by decide, type := .int (.uint ⟨128, by decide⟩) }
    locals imms evm key hbase hkey rfl (by
      change some (StorageAddr.leaf { slot := solcMappingSlot ⟨5⟩ (EVM.wordOfInt key), offset := 0, size := 16, hbound := by decide, type := .int (.uint ⟨128, by decide⟩) }) = _
      simp only [tickFieldSlot, show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl, u256_add_zero])]
  rw [storageLocLoad_uint_offset _ _ _ _ _ rfl (by decide) (by decide),
    storageLoad_codeOwner_eq_solcSlotWordAt evm evm.executionEnv _ rfl]
  rfl

theorem evalTickLiquidityNet (locals imms : Store) (evm : EVM.State) (key : Int)
    (hbase : locals.get? "ticks" = none) (hkey : locals.get? "arg0" = some (.int key)) :
    evalExpr? config {contract := contract, locals := locals, immutables := imms} evm
      (.storage ⟨"ticks", [.mindex (.var "arg0"), .field "liquidityNet"]⟩) =
      .ok (.int (tickSignedFieldValue key 0 16 ⟨128, by decide⟩ evm.accountMap evm.executionEnv)) := by
  rw [evalTickField "liquidityNet" (.int (.sint ⟨128, by decide⟩))
    { slot := tickFieldSlot key 0, offset := 16, size := 16, hbound := by decide, type := .int (.sint ⟨128, by decide⟩) }
    locals imms evm key hbase hkey rfl (by
      change some (StorageAddr.leaf { slot := solcMappingSlot ⟨5⟩ (EVM.wordOfInt key), offset := 16, size := 16, hbound := by decide, type := .int (.sint ⟨128, by decide⟩) }) = _
      simp only [tickFieldSlot, show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl, u256_add_zero])]
  rw [storageLocLoad_elem_offset _ _ _ _ _ (by decide) (by decide),
    storageLoad_codeOwner_eq_solcSlotWordAt evm evm.executionEnv _ rfl]
  simp only [wordToElem, normalizeSint_mask ⟨128, by decide⟩ _
    (UInt256.ofNat (256 ^ (16 : Fin 33).val - 1)) (by native_decide)]
  rfl

theorem evalTickFeeGrowthOutside0X128 (locals imms : Store) (evm : EVM.State) (key : Int)
    (hbase : locals.get? "ticks" = none) (hkey : locals.get? "arg0" = some (.int key)) :
    evalExpr? config {contract := contract, locals := locals, immutables := imms} evm
      (.storage ⟨"ticks", [.mindex (.var "arg0"), .field "feeGrowthOutside0X128"]⟩) =
      .ok (.int (Int.ofNat (tickFieldWord key 1 0 32 evm.accountMap evm.executionEnv).toNat)) := by
  rw [evalTickField "feeGrowthOutside0X128" (.int (.uint ⟨256, by decide⟩))
    { slot := tickFieldSlot key 1, offset := 0, size := 32, hbound := by decide, type := .int (.uint ⟨256, by decide⟩) }
    locals imms evm key hbase hkey rfl (by
      change some (StorageAddr.leaf { slot := solcMappingSlot ⟨5⟩ (EVM.wordOfInt key) + UInt256.ofNat 1, offset := 0, size := 32, hbound := by decide, type := .int (.uint ⟨256, by decide⟩) }) = _
      rfl)]
  rw [storageLocLoad_uint_offset _ _ _ _ _ rfl (by decide) (by decide),
    storageLoad_codeOwner_eq_solcSlotWordAt evm evm.executionEnv _ rfl]
  rfl

theorem evalTickFeeGrowthOutside1X128 (locals imms : Store) (evm : EVM.State) (key : Int)
    (hbase : locals.get? "ticks" = none) (hkey : locals.get? "arg0" = some (.int key)) :
    evalExpr? config {contract := contract, locals := locals, immutables := imms} evm
      (.storage ⟨"ticks", [.mindex (.var "arg0"), .field "feeGrowthOutside1X128"]⟩) =
      .ok (.int (Int.ofNat (tickFieldWord key 2 0 32 evm.accountMap evm.executionEnv).toNat)) := by
  rw [evalTickField "feeGrowthOutside1X128" (.int (.uint ⟨256, by decide⟩))
    { slot := tickFieldSlot key 2, offset := 0, size := 32, hbound := by decide, type := .int (.uint ⟨256, by decide⟩) }
    locals imms evm key hbase hkey rfl (by
      change some (StorageAddr.leaf { slot := solcMappingSlot ⟨5⟩ (EVM.wordOfInt key) + UInt256.ofNat 2, offset := 0, size := 32, hbound := by decide, type := .int (.uint ⟨256, by decide⟩) }) = _
      rfl)]
  rw [storageLocLoad_uint_offset _ _ _ _ _ rfl (by decide) (by decide),
    storageLoad_codeOwner_eq_solcSlotWordAt evm evm.executionEnv _ rfl]
  rfl

theorem evalTickTickCumulativeOutside (locals imms : Store) (evm : EVM.State) (key : Int)
    (hbase : locals.get? "ticks" = none) (hkey : locals.get? "arg0" = some (.int key)) :
    evalExpr? config {contract := contract, locals := locals, immutables := imms} evm
      (.storage ⟨"ticks", [.mindex (.var "arg0"), .field "tickCumulativeOutside"]⟩) =
      .ok (.int (tickSignedFieldValue key 3 0 ⟨56, by decide⟩ evm.accountMap evm.executionEnv)) := by
  rw [evalTickField "tickCumulativeOutside" (.int (.sint ⟨56, by decide⟩))
    { slot := tickFieldSlot key 3, offset := 0, size := 7, hbound := by decide, type := .int (.sint ⟨56, by decide⟩) }
    locals imms evm key hbase hkey rfl (by
      change some (StorageAddr.leaf { slot := solcMappingSlot ⟨5⟩ (EVM.wordOfInt key) + UInt256.ofNat 3, offset := 0, size := 7, hbound := by decide, type := .int (.sint ⟨56, by decide⟩) }) = _
      rfl)]
  rw [storageLocLoad_elem_offset _ _ _ _ _ (by decide) (by decide),
    storageLoad_codeOwner_eq_solcSlotWordAt evm evm.executionEnv _ rfl]
  simp only [wordToElem, normalizeSint_mask ⟨56, by decide⟩ _
    (UInt256.ofNat (256 ^ (7 : Fin 33).val - 1)) (by native_decide)]
  rfl

theorem evalTickSecondsPerLiquidityOutsideX128 (locals imms : Store) (evm : EVM.State) (key : Int)
    (hbase : locals.get? "ticks" = none) (hkey : locals.get? "arg0" = some (.int key)) :
    evalExpr? config {contract := contract, locals := locals, immutables := imms} evm
      (.storage ⟨"ticks", [.mindex (.var "arg0"), .field "secondsPerLiquidityOutsideX128"]⟩) =
      .ok (.int (Int.ofNat (tickFieldWord key 3 7 20 evm.accountMap evm.executionEnv).toNat)) := by
  rw [evalTickField "secondsPerLiquidityOutsideX128" (.int (.uint ⟨160, by decide⟩))
    { slot := tickFieldSlot key 3, offset := 7, size := 20, hbound := by decide, type := .int (.uint ⟨160, by decide⟩) }
    locals imms evm key hbase hkey rfl (by
      change some (StorageAddr.leaf { slot := solcMappingSlot ⟨5⟩ (EVM.wordOfInt key) + UInt256.ofNat 3, offset := 7, size := 20, hbound := by decide, type := .int (.uint ⟨160, by decide⟩) }) = _
      rfl)]
  rw [storageLocLoad_uint_offset _ _ _ _ _ rfl (by decide) (by decide),
    storageLoad_codeOwner_eq_solcSlotWordAt evm evm.executionEnv _ rfl]
  rfl

theorem evalTickSecondsOutside (locals imms : Store) (evm : EVM.State) (key : Int)
    (hbase : locals.get? "ticks" = none) (hkey : locals.get? "arg0" = some (.int key)) :
    evalExpr? config {contract := contract, locals := locals, immutables := imms} evm
      (.storage ⟨"ticks", [.mindex (.var "arg0"), .field "secondsOutside"]⟩) =
      .ok (.int (Int.ofNat (tickFieldWord key 3 27 4 evm.accountMap evm.executionEnv).toNat)) := by
  rw [evalTickField "secondsOutside" (.int (.uint ⟨32, by decide⟩))
    { slot := tickFieldSlot key 3, offset := 27, size := 4, hbound := by decide, type := .int (.uint ⟨32, by decide⟩) }
    locals imms evm key hbase hkey rfl (by
      change some (StorageAddr.leaf { slot := solcMappingSlot ⟨5⟩ (EVM.wordOfInt key) + UInt256.ofNat 3, offset := 27, size := 4, hbound := by decide, type := .int (.uint ⟨32, by decide⟩) }) = _
      rfl)]
  rw [storageLocLoad_uint_offset _ _ _ _ _ rfl (by decide) (by decide),
    storageLoad_codeOwner_eq_solcSlotWordAt evm evm.executionEnv _ rfl]
  rfl

theorem evalTickInitialized (locals imms : Store) (evm : EVM.State) (key : Int)
    (hbase : locals.get? "ticks" = none) (hkey : locals.get? "arg0" = some (.int key)) :
    evalExpr? config {contract := contract, locals := locals, immutables := imms} evm
      (.storage ⟨"ticks", [.mindex (.var "arg0"), .field "initialized"]⟩) =
      .ok (wordToElem .bool (tickFieldWord key 3 31 1 evm.accountMap evm.executionEnv)) := by
  rw [evalTickField "initialized" (.bool)
    { slot := tickFieldSlot key 3, offset := 31, size := 1, hbound := by decide, type := .bool }
    locals imms evm key hbase hkey rfl (by
      change some (StorageAddr.leaf { slot := solcMappingSlot ⟨5⟩ (EVM.wordOfInt key) + UInt256.ofNat 3, offset := 31, size := 1, hbound := by decide, type := .bool }) = _
      rfl)]
  rw [storageLocLoad_elem_offset _ _ _ _ _ (by decide) (by decide),
    storageLoad_codeOwner_eq_solcSlotWordAt evm evm.executionEnv _ rfl]
  rfl

end Benchmarks.UniswapV3.Pool
