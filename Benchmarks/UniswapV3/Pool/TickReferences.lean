import Benchmarks.UniswapV3.Pool.TickStorage
import Benchmarks.UniswapV3.Pool.StorageReferences
import Benchmarks.UniswapV3.Pool.SourceExpressions

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def tickStorageType : StorageType :=
  .struct "TickInfo" [
    ("liquidityGross", .elem (.int (.uint ⟨128, by decide⟩))),
    ("liquidityNet", .elem (.int (.sint ⟨128, by decide⟩))),
    ("feeGrowthOutside0X128", .elem (.int (.uint ⟨256, by decide⟩))),
    ("feeGrowthOutside1X128", .elem (.int (.uint ⟨256, by decide⟩))),
    ("tickCumulativeOutside", .elem (.int (.sint ⟨56, by decide⟩))),
    ("secondsPerLiquidityOutsideX128", .elem (.int (.uint ⟨160, by decide⟩))),
    ("secondsOutside", .elem (.int (.uint ⟨32, by decide⟩))),
    ("initialized", .elem .bool)]

def tickReference (key : Int) : EvaledStorageRef := ⟨"ticks", [.mindex (.int key)]⟩
def tickAlias (key : Int) : Value := .storageRef (tickReference key) tickStorageType

theorem resolveTickReference (locals imms : Store) (evm : EVM.State) (name : Ident) (key : Int)
    (hbase : locals.get? "ticks" = none) (hkey : locals.get? name = some (.int key)) :
    resolveStorageRef? config {contract := contract, locals := locals, immutables := imms} evm
      ⟨"ticks", [.mindex (.var name)]⟩ = .ok (tickReference key, tickStorageType) := by
  apply resolveStorageRef?_ok hbase
  · simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr_var_get (frame := {contract := contract, locals := locals, immutables := imms})
      (cfg := config) (evm := evm) hkey,
      valueToKey?, bind, EvalResult.bind, EvalResult.ofOption, pure, tickReference]
  · rfl

theorem resolveTickAliasField (locals imms : Store) (evm : EVM.State) (bindingName name : Ident)
    (key : Int) (ty : StorageType) (hget : locals.get? bindingName = some (tickAlias key))
    (htype : storageTypeStep? tickStorageType (.field name) = some ty) :
    resolveStorageRef? config {contract := contract, locals := locals, immutables := imms} evm
      ⟨bindingName, [.field name]⟩ = .ok (⟨"ticks", [.mindex (.int key), .field name]⟩, ty) := by
  simp only [resolveStorageRef?, hget, tickAlias, evalStorageRefFrom?, evalStorageRefStep,
    htype, tickReference, bind, EvalResult.bind, EvalResult.ofOption, pure, List.cons_append, List.nil_append]

theorem evalTickAliasField (name : Ident) (ty : ABI.ElemType) (loc : StorageLoc)
    (locals imms : Store) (evm : EVM.State) (bindingName : Ident) (key : Int)
    (hget : locals.get? bindingName = some (tickAlias key))
    (htype : storageTypeStep? tickStorageType (.field name) = some (.elem ty))
    (hloc : storageBackend.locate? ⟨"ticks", [.mindex (.int key), .field name]⟩ = some (.leaf loc)) :
    evalExpr? config {contract := contract, locals := locals, immutables := imms} evm
      (.storage ⟨bindingName, [.field name]⟩) = .ok (storageLocLoad evm loc) :=
  evalExpr_storage_resolved (resolveTickAliasField locals imms evm bindingName name key _ hget htype)
    poolStorageBackend_eq hloc

theorem evalTickAliasCumulative (locals imms : Store) (evm : EVM.State) (bindingName : Ident) (key : Int)
    (hget : locals.get? bindingName = some (tickAlias key)) :
    evalExpr? config {contract := contract, locals := locals, immutables := imms} evm
      (.storage ⟨bindingName, [.field "tickCumulativeOutside"]⟩) =
      .ok (.int (tickSignedFieldValue key 3 0 ⟨56, by decide⟩ evm.accountMap evm.executionEnv)) := by
  rw [evalTickAliasField "tickCumulativeOutside" (.int (.sint ⟨56, by decide⟩))
    { slot := tickFieldSlot key 3, offset := 0, size := 7, hbound := by decide, type := .int (.sint ⟨56, by decide⟩) }
    locals imms evm bindingName key hget rfl (by
      change some (StorageAddr.leaf { slot := solcMappingSlot ⟨5⟩ (EVM.wordOfInt key) + UInt256.ofNat 3, offset := 0, size := 7, hbound := by decide, type := .int (.sint ⟨56, by decide⟩) }) = _
      rfl)]
  rw [storageLocLoad_elem_offset _ _ _ _ _ (by decide) (by decide),
    storageLoad_codeOwner_eq_solcSlotWordAt evm evm.executionEnv _ rfl]
  simp only [wordToElem, normalizeSint_mask ⟨56, by decide⟩ _
    (UInt256.ofNat (256 ^ (7 : Fin 33).val - 1)) (by native_decide)]
  rfl

theorem evalTickAliasSecondsPerLiquidity (locals imms : Store) (evm : EVM.State) (bindingName : Ident) (key : Int)
    (hget : locals.get? bindingName = some (tickAlias key)) :
    evalExpr? config {contract := contract, locals := locals, immutables := imms} evm
      (.storage ⟨bindingName, [.field "secondsPerLiquidityOutsideX128"]⟩) =
      .ok (.int (Int.ofNat (tickFieldWord key 3 7 20 evm.accountMap evm.executionEnv).toNat)) := by
  rw [evalTickAliasField "secondsPerLiquidityOutsideX128" (.int (.uint ⟨160, by decide⟩))
    { slot := tickFieldSlot key 3, offset := 7, size := 20, hbound := by decide, type := .int (.uint ⟨160, by decide⟩) }
    locals imms evm bindingName key hget rfl (by
      change some (StorageAddr.leaf { slot := solcMappingSlot ⟨5⟩ (EVM.wordOfInt key) + UInt256.ofNat 3, offset := 7, size := 20, hbound := by decide, type := .int (.uint ⟨160, by decide⟩) }) = _
      rfl)]
  rw [storageLocLoad_uint_offset _ _ _ _ _ rfl (by decide) (by decide),
    storageLoad_codeOwner_eq_solcSlotWordAt evm evm.executionEnv _ rfl]
  rfl

theorem evalTickAliasSeconds (locals imms : Store) (evm : EVM.State) (bindingName : Ident) (key : Int)
    (hget : locals.get? bindingName = some (tickAlias key)) :
    evalExpr? config {contract := contract, locals := locals, immutables := imms} evm
      (.storage ⟨bindingName, [.field "secondsOutside"]⟩) =
      .ok (.int (Int.ofNat (tickFieldWord key 3 27 4 evm.accountMap evm.executionEnv).toNat)) := by
  rw [evalTickAliasField "secondsOutside" (.int (.uint ⟨32, by decide⟩))
    { slot := tickFieldSlot key 3, offset := 27, size := 4, hbound := by decide, type := .int (.uint ⟨32, by decide⟩) }
    locals imms evm bindingName key hget rfl (by
      change some (StorageAddr.leaf { slot := solcMappingSlot ⟨5⟩ (EVM.wordOfInt key) + UInt256.ofNat 3, offset := 27, size := 4, hbound := by decide, type := .int (.uint ⟨32, by decide⟩) }) = _
      rfl)]
  rw [storageLocLoad_uint_offset _ _ _ _ _ rfl (by decide) (by decide),
    storageLoad_codeOwner_eq_solcSlotWordAt evm evm.executionEnv _ rfl]
  rfl

theorem evalTickAliasInitialized (locals imms : Store) (evm : EVM.State) (bindingName : Ident) (key : Int)
    (hget : locals.get? bindingName = some (tickAlias key)) :
    evalExpr? config {contract := contract, locals := locals, immutables := imms} evm
      (.storage ⟨bindingName, [.field "initialized"]⟩) =
      .ok (wordToElem .bool (tickFieldWord key 3 31 1 evm.accountMap evm.executionEnv)) := by
  rw [evalTickAliasField "initialized" (.bool)
    { slot := tickFieldSlot key 3, offset := 31, size := 1, hbound := by decide, type := .bool }
    locals imms evm bindingName key hget rfl (by
      change some (StorageAddr.leaf { slot := solcMappingSlot ⟨5⟩ (EVM.wordOfInt key) + UInt256.ofNat 3, offset := 31, size := 1, hbound := by decide, type := .bool }) = _
      rfl)]
  rw [storageLocLoad_elem_offset _ _ _ _ _ (by decide) (by decide),
    storageLoad_codeOwner_eq_solcSlotWordAt evm evm.executionEnv _ rfl]
  rfl

end Benchmarks.UniswapV3.Pool
