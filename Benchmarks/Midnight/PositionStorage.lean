import Benchmarks.Midnight.PackedFields

variable {fork : Ethereum.Fork}

/-! Source evaluation shared by the scalar position getters. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def positionArguments (id user : UInt256) : Store :=
  ((∅ : Store).insert "id" (wordBytes32Value id)).insert "user"
    (.address (AccountAddress.ofNat user.toNat))

def positionSlot (id user : UInt256) : UInt256 :=
  solcMappingSlot (solcMappingSlot ⟨0⟩ id) user

theorem evalNestedBytes32AddressField
    {cfg : Config} {frame : Frame} {layout : StorageLayout}
    {name arg0 arg1 field : Ident} {t : ElemType} {loc : StorageLoc} {value : Value}
    (evm : EVM.State) (id user : UInt256)
    (hbase : frame.locals.get? name = none)
    (hid : frame.locals.get? arg0 = some (wordBytes32Value id))
    (huser : frame.locals.get? arg1 = some (.address (AccountAddress.ofNat user.toNat)))
    (hbackend : cfg.storageBackend = solidityStorageBackend layout)
    (hty : storageTypeAt? frame.contract.storage
      { base := name, steps := [.mindex (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id)),
        .mindex (.address (AccountAddress.ofNat user.toNat)), .field field] } = some (.elem t))
    (hloc : layout { base := name, steps :=
        [.mindex (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id)),
         .mindex (.address (AccountAddress.ofNat user.toNat)), .field field] } = some (.leaf loc))
    (hload : storageLocLoad evm loc = value) :
    evalExpr? cfg frame evm (.storage { base := name, steps :=
      [.mindex (.var arg0), .mindex (.var arg1), .field field] }) = .ok value := by
  apply evalExpr_storage_scalar_value (loc := loc)
    (er := { base := name, steps :=
      [.mindex (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id)),
       .mindex (.address (AccountAddress.ofNat user.toNat)), .field field] }) (t := t)
    hbase ?_ hty hbackend hloc hload
  have hlen : (EVM.Word.toBytesBE id).length = 32 := by
    simpa using word_toBytesBE_toByteArray_size id
  simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?, hid, huser,
    EvalResult.bind, EvalResult.ofOption, valueToKey?, wordBytes32Value, pure, bind,
    hlen, show (abiBytes32Width : Nat) + 1 = 32 from rfl, ite_true]

theorem guardedPositionFieldGetter
    {cfg : Config} {C : ContractDecl} {layout : StorageLayout}
    {field : Ident} {t : ElemType} {loc : StorageLoc} {value : Value}
    (evm : EVM.State) (id user : UInt256)
    (hbackend : cfg.storageBackend = solidityStorageBackend layout)
    (hty : storageTypeAt? C.storage
      { base := "position", steps :=
        [.mindex (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id)),
         .mindex (.address (AccountAddress.ofNat user.toNat)), .field field] } = some (.elem t))
    (hloc : layout { base := "position", steps :=
        [.mindex (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id)),
         .mindex (.address (AccountAddress.ofNat user.toNat)), .field field] } = some (.leaf loc))
    (hload : storageLocLoad evm loc = value)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit) :
    ExecTransitionBody fork cfg C evm (positionArguments id user)
      (entryPrefix ++ [.return [.storage { base := "position", steps :=
        [.mindex (.var "id"), .mindex (.var "user"), .field field] }]])
      (.returned (calldataFrame C (positionArguments id user) ∅ evm) evm (some [value])) := by
  apply guardedReturnBody hwv hhi
  apply evalNestedBytes32AddressField evm id user (by simp [calldataFrame, positionArguments])
    ?_ ?_ hbackend hty hloc hload
  · change ((((∅ : Store).insert "id" (wordBytes32Value id)).insert "user"
      (.address (AccountAddress.ofNat user.toNat))).insert "__calldata"
        (.bytes evm.executionEnv.calldata)).get? "id" = _
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), store_get_self]
  · change ((((∅ : Store).insert "id" (wordBytes32Value id)).insert "user"
      (.address (AccountAddress.ofNat user.toNat))).insert "__calldata"
        (.bytes evm.executionEnv.calldata)).get? "user" = _
    rw [store_get_ne _ _ (by decide), store_get_self]

end Benchmarks.Midnight
