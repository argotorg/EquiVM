import Benchmarks.Midnight.Entry

variable {fork : Ethereum.Fork}

/-! Storage and return-value lemmas shared by Midnight's entry points. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

-- Address getter with Midnight's nonpayable and signed-calldata entry guards.
theorem guardedAddressGetter {cfg : Config} {C : ContractDecl} {layout : StorageLayout}
    {name : Ident} {slot : UInt256} (evm : EVM.State)
    (hbackend : cfg.storageBackend = solidityStorageBackend layout)
    (hty : storageTypeAt? C.storage { base := name } = some (.elem .address))
    (hloc : layout { base := name } = some (.leaf (addressOffset0Loc slot)))
    (hname : name ≠ "__calldata")
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit) :
    ExecTransitionBody fork cfg C evm ∅ (entryPrefix ++ [.return [.storage { base := name }]])
      (.returned (calldataFrame C ∅ ∅ evm) evm
        (some [.address (AccountAddress.ofNat
          (UInt256.land (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
            solcAddrMask).toNat)])) := by
  apply guardedReturnBody hwv hhi
  apply evalExpr_storage_scalar_value (loc := addressOffset0Loc slot)
    (er := { base := name }) (t := .address)
  · simp [calldataFrame, Ne.symm hname]
  · simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind]
  · exact hty
  · exact hbackend
  · exact hloc
  · exact storageLocLoad_address_offset0 evm slot

theorem guardedBoolMappingGetter {cfg : Config} {C : ContractDecl} {layout : StorageLayout}
    {name : Ident} {slot : UInt256} (evm : EVM.State) (key : UInt256)
    (hbackend : cfg.storageBackend = solidityStorageBackend layout)
    (hty : storageTypeAt? C.storage
      { base := name, steps := [.mindex (.int key.toNat)] } = some (.elem .bool))
    (hloc : layout { base := name, steps := [.mindex (.int key.toNat)] } =
      some (.leaf (boolOffset0Loc (solcMappingSlot slot key))))
    (hname : name ≠ "__calldata") (harg : name ≠ "arg0")
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit) :
    ExecTransitionBody fork cfg C evm ((∅ : Store).insert "arg0" (.int key.toNat))
      (entryPrefix ++ [.return [.storage { base := name, steps := [.mindex (.var "arg0")] }]])
      (.returned (calldataFrame C ((∅ : Store).insert "arg0" (.int key.toNat)) ∅ evm) evm
        (some [wordToElem .bool (UInt256.land
          (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner (solcMappingSlot slot key))
          ⟨255⟩)])) := by
  apply guardedReturnBody hwv hhi
  apply evalExpr_storage_scalar_value (loc := boolOffset0Loc (solcMappingSlot slot key))
    (er := { base := name, steps := [.mindex (.int key.toNat)] }) (t := .bool)
  · simp [calldataFrame, Ne.symm hname, Ne.symm harg]
  · have hget :
        (calldataFrame C ((∅ : Store).insert "arg0" (.int key.toNat)) ∅ evm).locals.get?
          "arg0" = some (.int key.toNat) := by
      change (((∅ : Store).insert "arg0" (.int key.toNat)).insert "__calldata"
        (.bytes evm.executionEnv.calldata)).get? "arg0" = _
      rw [store_get_ne _ _ (by decide), store_get_self]
    simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?, hget,
      EvalResult.bind, EvalResult.ofOption, valueToKey?, pure, bind]
  · exact hty
  · exact hbackend
  · exact hloc
  · exact storageLocLoad_bool_offset0 evm _

theorem evalBytes32MappingField
    {cfg : Config} {C : ContractDecl} {layout : StorageLayout}
    {name arg field : Ident} {t : ElemType} {loc : StorageLoc} {value : Value}
    (evm : EVM.State) (key : UInt256)
    (hbackend : cfg.storageBackend = solidityStorageBackend layout)
    (hty : storageTypeAt? C.storage
      { base := name, steps := [.mindex (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE key)),
        .field field] } = some (.elem t))
    (hloc : layout
      { base := name, steps := [.mindex (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE key)),
        .field field] } = some (.leaf loc))
    (hload : storageLocLoad evm loc = value)
    (hname : name ≠ "__calldata") (harg : name ≠ arg) (hargData : arg ≠ "__calldata") :
    evalExpr? cfg (calldataFrame C ((∅ : Store).insert arg (wordBytes32Value key)) ∅ evm) evm
      (.storage { base := name, steps := [.mindex (.var arg), .field field] }) = .ok value := by
  apply evalExpr_storage_scalar_value (loc := loc)
    (er := { base := name, steps :=
      [.mindex (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE key)), .field field] }) (t := t)
  · simp [calldataFrame, Ne.symm hname, Ne.symm harg]
  · have hget :
        (calldataFrame C ((∅ : Store).insert arg (wordBytes32Value key)) ∅ evm).locals.get?
          arg = some (wordBytes32Value key) := by
      change (((∅ : Store).insert arg (wordBytes32Value key)).insert "__calldata"
        (.bytes evm.executionEnv.calldata)).get? arg = _
      rw [store_get_ne _ _ (by simpa using Ne.symm hargData), store_get_self]
    have hlen : (EVM.Word.toBytesBE key).length = 32 := by
      simpa using word_toBytesBE_toByteArray_size key
    simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?, hget,
      EvalResult.bind, EvalResult.ofOption, valueToKey?, wordBytes32Value, pure, bind,
      hlen, show (abiBytes32Width : Nat) + 1 = 32 from rfl, ite_true]
  · exact hty
  · exact hbackend
  · exact hloc
  · exact hload

theorem guardedBytes32MappingFieldGetter
    {cfg : Config} {C : ContractDecl} {layout : StorageLayout}
    {name arg field : Ident} {t : ElemType} {loc : StorageLoc} {value : Value}
    (evm : EVM.State) (key : UInt256)
    (hbackend : cfg.storageBackend = solidityStorageBackend layout)
    (hty : storageTypeAt? C.storage
      { base := name, steps := [.mindex (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE key)),
        .field field] } = some (.elem t))
    (hloc : layout
      { base := name, steps := [.mindex (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE key)),
        .field field] } = some (.leaf loc))
    (hload : storageLocLoad evm loc = value)
    (hname : name ≠ "__calldata") (harg : name ≠ arg) (hargData : arg ≠ "__calldata")
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit) :
    ExecTransitionBody fork cfg C evm ((∅ : Store).insert arg (wordBytes32Value key))
      (entryPrefix ++ [.return [.storage
        { base := name, steps := [.mindex (.var arg), .field field] }]])
      (.returned (calldataFrame C ((∅ : Store).insert arg (wordBytes32Value key)) ∅ evm) evm
        (some [value])) := by
  apply guardedReturnBody hwv hhi
  exact evalBytes32MappingField evm key hbackend hty hloc hload hname harg hargData

theorem midnightReturnWord_freePtr (word : UInt256) :
    (writeWord midnightEntryMemory (memLoad ⟨64⟩ midnightEntryMemory).toNat word).readWithPadding
      (memLoad ⟨64⟩ midnightEntryMemory).toNat 32 = word.toByteArray := by
  rw [midnightEntryMemory_freePtr]
  exact midnightReturnWord word

theorem midnightEntryMemory_zero :
    memLoad (UInt256.ofNat 800) midnightEntryMemory = ⟨0⟩ := by
  native_decide

theorem guardedAddressMappingGetter
    {cfg : Config} {C : ContractDecl} {layout : StorageLayout}
    {name : Ident} {t : ElemType} {loc : StorageLoc} {value : Value}
    (evm : EVM.State) (key : UInt256)
    (hbackend : cfg.storageBackend = solidityStorageBackend layout)
    (hty : storageTypeAt? C.storage
      { base := name, steps := [.mindex (.address (AccountAddress.ofNat key.toNat))] } =
        some (.elem t))
    (hloc : layout
      { base := name, steps := [.mindex (.address (AccountAddress.ofNat key.toNat))] } =
        some (.leaf loc))
    (hload : storageLocLoad evm loc = value)
    (hname : name ≠ "__calldata") (harg : name ≠ "arg0")
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit) :
    ExecTransitionBody fork cfg C evm
      ((∅ : Store).insert "arg0" (.address (AccountAddress.ofNat key.toNat)))
      (entryPrefix ++ [.return [.storage { base := name, steps := [.mindex (.var "arg0")] }]])
      (.returned (calldataFrame C
        ((∅ : Store).insert "arg0" (.address (AccountAddress.ofNat key.toNat))) ∅ evm) evm
        (some [value])) := by
  apply guardedReturnBody hwv hhi
  apply evalExpr_storage_scalar_value (loc := loc)
    (er := { base := name, steps := [.mindex (.address (AccountAddress.ofNat key.toNat))] })
    (t := t)
  · simp [calldataFrame, Ne.symm hname, Ne.symm harg]
  · have hget :
        (calldataFrame C
          ((∅ : Store).insert "arg0" (.address (AccountAddress.ofNat key.toNat))) ∅ evm).locals.get?
          "arg0" = some (.address (AccountAddress.ofNat key.toNat)) := by
      change (((∅ : Store).insert "arg0" (.address (AccountAddress.ofNat key.toNat))).insert
        "__calldata" (.bytes evm.executionEnv.calldata)).get? "arg0" = _
      rw [store_get_ne _ _ (by decide), store_get_self]
    simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?, hget,
      EvalResult.bind, EvalResult.ofOption, valueToKey?, pure, bind]
  · exact hty
  · exact hbackend
  · exact hloc
  · exact hload

end Benchmarks.Midnight
