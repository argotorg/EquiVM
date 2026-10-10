import Benchmarks.UniswapV3.Pool.PositionStorage
import Benchmarks.UniswapV3.Pool.StorageReferences
import Benchmarks.UniswapV3.Pool.ProtocolFeeStorage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def positionStorageType : StorageType :=
  .struct "PositionInfo"
    [("liquidity", .elem (.int (.uint ⟨128, by decide⟩))),
     ("feeGrowthInside0LastX128", .elem (.int (.uint ⟨256, by decide⟩))),
     ("feeGrowthInside1LastX128", .elem (.int (.uint ⟨256, by decide⟩))),
     ("tokensOwed0", .elem (.int (.uint ⟨128, by decide⟩))),
     ("tokensOwed1", .elem (.int (.uint ⟨128, by decide⟩)))]

def positionReference (key : UInt256) : EvaledStorageRef :=
  ⟨"positions", [.mindex (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE key))]⟩

def positionAlias (key : UInt256) : Value := .storageRef (positionReference key) positionStorageType

def positionOwedField (second : Bool) : Ident := if second then "tokensOwed1" else "tokensOwed0"

def positionOwedReference (key : UInt256) (second : Bool) : EvaledStorageRef :=
  ⟨"positions", [.mindex (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE key)),
    .field (positionOwedField second)]⟩

def positionOwedLoc (key : UInt256) (second : Bool) : StorageLoc :=
  { slot := solcMappingSlot ⟨7⟩ key + UInt256.ofNat 3
    offset := if second then 16 else 0
    size := 16
    type := .int (.uint ⟨128, by decide⟩)
    hbound := by cases second <;> decide }

def positionOwedWord (key : UInt256) (second : Bool) (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  positionFieldWord key 3 (if second then 16 else 0) 16 σ I

theorem positionOwedWord_lt (key : UInt256) (second : Bool) (σ : AccountMap) (I : ExecutionEnv) :
    (positionOwedWord key second σ I).toNat < 2 ^ 128 :=
  u256LandMaskToNatLtOfToNat _ _ (by decide)

theorem resolvePositionAliasField (locals imms : Store) (evm : EVM.State)
    (bindingName name : Ident) (key : UInt256) (ty : StorageType)
    (hget : locals.get? bindingName = some (positionAlias key))
    (htype : storageTypeStep? positionStorageType (.field name) = some ty) :
    resolveStorageRef? config {contract := contract, locals := locals, immutables := imms} evm
      ⟨bindingName, [.field name]⟩ =
      .ok (⟨"positions", [.mindex (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE key)),
        .field name]⟩, ty) := by
  simp only [resolveStorageRef?, hget, positionAlias, evalStorageRefFrom?, evalStorageRefStep,
    htype, positionReference, bind, EvalResult.bind, EvalResult.ofOption, pure,
    List.cons_append, List.nil_append]

theorem positionOwedResolve (locals imms : Store) (evm : EVM.State) (key : UInt256) (second : Bool)
    (hget : locals.get? "position" = some (positionAlias key)) :
    resolveStorageRef? config {contract := contract, locals := locals, immutables := imms} evm
      ⟨"position", [.field (positionOwedField second)]⟩ =
      .ok (positionOwedReference key second, .elem (.int (.uint ⟨128, by decide⟩))) := by
  exact resolvePositionAliasField locals imms evm "position" (positionOwedField second)
    key _ hget (by cases second <;> rfl)

theorem positionOwedLocate (key : UInt256) (second : Bool) :
    storageBackend.locate? (positionOwedReference key second) = some (.leaf (positionOwedLoc key second)) := by
  cases second
  · change some (StorageAddr.leaf
      { slot := solcMappingSlot ⟨7⟩ (keyValueToWord (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE key))) + UInt256.ofNat 3
        offset := 0
        size := 16
        type := .int (.uint ⟨128, by decide⟩)
        hbound := by decide }) = _
    rw [keyValueToWord_fixedBytes32]
    rfl
  · change some (StorageAddr.leaf
      { slot := solcMappingSlot ⟨7⟩ (keyValueToWord (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE key))) + UInt256.ofNat 3
        offset := 16
        size := 16
        type := .int (.uint ⟨128, by decide⟩)
        hbound := by decide }) = _
    rw [keyValueToWord_fixedBytes32]
    rfl

theorem evalPositionAliasOwed (locals imms : Store) (evm : EVM.State) (bindingName : Ident)
    (key : UInt256) (second : Bool) (hget : locals.get? bindingName = some (positionAlias key)) :
    evalExpr? config {contract := contract, locals := locals, immutables := imms} evm
      (.storage ⟨bindingName, [.field (positionOwedField second)]⟩) =
      .ok (.int (Int.ofNat (positionOwedWord key second evm.accountMap evm.executionEnv).toNat)) := by
  rw [evalExpr_storage_resolved
    (resolvePositionAliasField locals imms evm bindingName (positionOwedField second) key _ hget
      (by cases second <;> rfl)) poolStorageBackend_eq (positionOwedLocate key second)]
  simp only [positionOwedLoc]
  rw [storageLocLoad_uint_offset _ _ _ _ _ rfl (by cases second <;> decide) (by decide),
    storageLoad_codeOwner_eq_solcSlotWordAt evm evm.executionEnv _ rfl]
  cases second <;> rfl

theorem evalPositionOwed (locals imms : Store) (evm : EVM.State) (key : UInt256) (second : Bool)
    (hget : locals.get? "position" = some (positionAlias key)) :
    evalExpr? config {contract := contract, locals := locals, immutables := imms} evm
      (.storage ⟨"position", [.field (positionOwedField second)]⟩) =
      .ok (.int (Int.ofNat (positionOwedWord key second evm.accountMap evm.executionEnv).toNat)) := by
  exact evalPositionAliasOwed locals imms evm "position" key second hget

def storePositionOwed (evm : EVM.State) (key : UInt256) (second : Bool) (value : UInt256) : EVM.State :=
  EVM.storageStore evm evm.executionEnv.codeOwner (solcMappingSlot ⟨7⟩ key + UInt256.ofNat 3)
    (protocolFeeUpdateWord second
      (EVM.storageLoad evm evm.executionEnv.codeOwner (solcMappingSlot ⟨7⟩ key + UInt256.ofNat 3)) value)

theorem assignPositionAliasOwed (locals imms : Store) (evm : EVM.State) (bindingName : Ident)
    (key : UInt256) (second : Bool) (value : UInt256)
    (hget : locals.get? bindingName = some (positionAlias key)) :
    assignStorageRef? config {contract := contract, locals := locals, immutables := imms} evm .storage
      ⟨bindingName, [.field (positionOwedField second)]⟩ (.int (Int.ofNat value.toNat)) =
      .ok ({contract := contract, locals := locals, immutables := imms},
        storePositionOwed evm key second value) := by
  exact assignStorageRef_resolved_scalar
    (resolvePositionAliasField locals imms evm bindingName (positionOwedField second) key _ hget
      (by cases second <;> rfl)) poolStorageBackend_eq (positionOwedLocate key second)
    (storageLocStore_uint128PairField evm _ second value)

theorem assignPositionOwed (locals imms : Store) (evm : EVM.State) (key : UInt256) (second : Bool)
    (value : UInt256) (hget : locals.get? "position" = some (positionAlias key)) :
    assignStorageRef? config {contract := contract, locals := locals, immutables := imms} evm .storage
      ⟨"position", [.field (positionOwedField second)]⟩ (.int (Int.ofNat value.toNat)) =
      .ok ({contract := contract, locals := locals, immutables := imms}, storePositionOwed evm key second value) := by
  exact assignPositionAliasOwed locals imms evm "position" key second value hget

theorem storePositionOwed_accountMap (evm : EVM.State) (key : UInt256) (second : Bool) (value : UInt256) :
    (storePositionOwed evm key second value).accountMap =
      sstoreAccountMap evm.executionEnv.codeOwner evm.accountMap (solcMappingSlot ⟨7⟩ key + UInt256.ofNat 3)
        (protocolFeeUpdateWord second
          (solcSlotWordAt (solcMappingSlot ⟨7⟩ key + UInt256.ofNat 3) evm.accountMap evm.executionEnv) value) := by
  rw [storePositionOwed, storageStore_accountMap,
    storageLoad_codeOwner_eq_solcSlotWordAt evm evm.executionEnv _ rfl]

theorem storePositionOwed_executionEnv (evm : EVM.State) (key : UInt256) (second : Bool) (value : UInt256) :
    (storePositionOwed evm key second value).executionEnv = evm.executionEnv :=
  storageStore_executionEnv _ _ _ _

end Benchmarks.UniswapV3.Pool
