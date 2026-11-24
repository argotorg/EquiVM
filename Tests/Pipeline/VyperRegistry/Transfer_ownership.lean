import Tests.Pipeline.VyperRegistry.Helpers

variable {fork : Ethereum.Fork}

/-!
# Registry `transfer_ownership(address)`

Dispatcher bucket 4, arm entry pc 36: the guard, the address validation, the internal
`ownable._check_owner` (pc 1537, returning through pc 1659), `new_owner != 0` (pc 68), then
the `previous` read, the `SSTORE` of slot 0 and the log (pc 196).
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
  Reasoning.VyperBounded

namespace Tests.Pipeline.VyperRegistry

set_option maxRecDepth 2000000

theorem transfer_ownershipBody_eq : transfer_ownershipTransition.body =
    [.require (.binary .eq (.env .callvalue) (.intLit 0)),
     .internalCall "ownable__check_owner" [] "__c0",
     .require (.binary .ne (.var "new_owner") (.cast (.intLit 0) (.elem .address))),
     .letDecl "previous" (some (.elem .address)) (.storage ownerRef),
     .assign .storage ownerRef (.var "new_owner"),
     .emit "OwnershipTransferred" [.var "previous", .var "new_owner"]] := by rfl

abbrev toStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "new_owner" (.address (AccountAddress.ofNat (argWord I).toNat))
abbrev toL1 (I : ExecutionEnv) : Store := (toStore I).insert "__c0" .unit
abbrev toL2 (σ : AccountMap) (I : ExecutionEnv) : Store :=
  (toL1 I).insert "previous" (.address (AccountAddress.ofNat (solcSlotWordAt ⟨0⟩ σ I).toNat))

theorem toDecode_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size)
    (hcanon : (argWord I).toNat < EVM.addressModulus) :
    config.externalABI.decodeCalldata? (transfer_ownershipTransition.params.map Param.name)
      (transitionSignature transfer_ownershipTransition).paramTypes I.calldata = some (toStore I) := by
  rw [argWord_eq] at hcanon
  simpa [config, contract, Syntax.contractSyntax, transfer_ownershipTransition, toStore, argWord_eq] using
    decodeCalldataWithMode_vyper_address_ok (cd := I.calldata) (x := "new_owner") hsz36 hcanon

theorem toDecode_short {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    config.externalABI.decodeCalldata? (transfer_ownershipTransition.params.map Param.name)
      (transitionSignature transfer_ownershipTransition).paramTypes I.calldata = none := by
  simpa [config, contract, Syntax.contractSyntax, transfer_ownershipTransition] using
    decodeCalldataWithMode_vyper_address_none_short (cd := I.calldata) (x := "new_owner") hsz hshort

theorem toDecode_noncanon {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size)
    (hnc : ¬ (argWord I).toNat < EVM.addressModulus) :
    config.externalABI.decodeCalldata? (transfer_ownershipTransition.params.map Param.name)
      (transitionSignature transfer_ownershipTransition).paramTypes I.calldata = none := by
  rw [argWord_eq] at hnc
  simpa [config, contract, Syntax.contractSyntax, transfer_ownershipTransition] using
    decodeCalldataWithMode_vyper_address_none_noncanon (cd := I.calldata) (x := "new_owner") hsz36 hnc

/-- The argument word at memory offset 256 (written by the call sequence at pc 57). -/
abbrev mem57 (I : ExecutionEnv) : ByteArray := (argWord I).toByteArray.write 0 (registryDispatchMem 4) 256 32

theorem memLoad256_mem57 (I : ExecutionEnv) : memLoad (UInt256.ofNat 256) (mem57 I) = argWord I :=
  memLoad_write_back _ _ 256 (by decide) (by rw [dispatchMem_size 4 (by decide)]; exact lt_usize _ (by decide))

theorem mem57_size (I : ExecutionEnv) : (mem57 I).size = 288 :=
  toByteArray_write32_size_of_ge _ _ 256 32 288 (dispatchMem_size 4 (by decide)) (by omega) (lt_usize _ (by decide)) rfl

/-- `transfer_ownership(address)`: the theorem `Correct.lean` routes selector 10 to. -/
theorem registryTransfer_ownershipBody {σ σ₀ A I} {g : UInt256} (hwf : storageWF σ I)
    (hcode : I.code = registryBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (registrySelBytes 10)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (registrySelBytes 10) rfl hsel
  obtain ⟨_, _, rd⟩ := registryReachTransfer_ownershipBody (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) hcode hsz hsize hsel
  have hd : dispatchMsg contract I.calldata = some transfer_ownershipTransition :=
    registryDispatch_transfer_ownership (selIs_exclusive (by native_decide) hsel) (selIs_exclusive (by native_decide) hsel)
      (selIs_exclusive (by native_decide) hsel) (selIs_exclusive (by native_decide) hsel)
      (selIs_exclusive (by native_decide) hsel) (selIs_exclusive (by native_decide) hsel)
      (selIs_exclusive (by native_decide) hsel) (selIs_exclusive (by native_decide) hsel)
      (selIs_exclusive (by native_decide) hsel) (selIs_exclusive (by native_decide) hsel) hsel
  by_cases hshort : I.calldata.size < 36
  · have rd1 := registryBlocks.registry_block_36_taken (by simp) (guard_short hsize hshort) (by jump_dest) rd
    have rd2 := registryBlocks.registry_block_1661 (by simp) rd1
    exact RDrev.reEquivDecodingFailed hcode rd2 hd (toDecode_short hsz hshort)
  have hsz36 : 36 ≤ I.calldata.size := by omega
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · have rd1 := registryBlocks.registry_block_36_taken (by simp) (guard_wv hwv) (by jump_dest) rd
    have rd2 := registryBlocks.registry_block_1661 (by simp) rd1
    exact RDrev.reEquivOfDispatch hcode hd
      (fun _ => by rw [transfer_ownershipBody_eq]; exact bodyReverts_nonPayable (by simpa [initState] using hwv)) rd2
  have rd1 := registryBlocks.registry_block_36_fallthrough (by simp) (guard_ok hwv hsz36 hsize) rd
  by_cases hcanon : (argWord I).toNat < EVM.addressModulus
  swap
  · have rd2 := registryBlocks.registry_block_46_taken (by simp)
      (by intro h; exact hcanon (u256_lt_addressModulus_of_shiftRight160_zero _ h)) (by jump_dest) rd1
    have rd3 := registryBlocks.registry_block_1661 (by simp [registryBlocks.registry_block_46_taken_stack]) rd2
    exact RDrev.reEquivDecodingFailed hcode rd3 hd (toDecode_noncanon hsz36 hcanon)
  have rd2 := registryBlocks.registry_block_46_fallthrough (by simp) (u256_shiftRight160_zero_of_lt _ hcanon) rd1
  simp only [registryBlocks.registry_block_46_fallthrough_stack] at rd2
  have rd3 := registryBlocks.registry_block_57 (by simp) (by jump_dest) rd2
  simp only [registryBlocks.registry_block_57_stack, registryBlocks.registry_block_57_memory,
    ulit_toNat' 256 (by decide)] at rd3
  have hdec := toDecode_ok (I := I) hsz36 hcanon
  have hcv : evalExpr? config (frame (toStore I)) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (.binary .eq (.env .callvalue) (.intLit 0)) = .ok (.bool true) :=
    evalCallvalueEq_true (by simpa [initState] using hwv)
  -- the owner check runs with an empty frame
  have howner : evalExpr? config (frame ∅) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (.binary .eq (.env .caller) (.storage ownerRef)) =
      .ok (.bool (decide (UInt256.ofNat I.source.val = solcSlotWordAt ⟨0⟩ σ I))) := by
    rw [evalCallerEqOwner _ (by simp) (by rw [storageLoad_initState_ofUInt256_solcSlotWordAt]; exact hwf.1),
      storageLoad_initState_ofUInt256_solcSlotWordAt]
    rfl
  by_cases hown : UInt256.ofNat I.source.val = solcSlotWordAt ⟨0⟩ σ I
  swap
  · obtain ⟨_, _, rd4⟩ := registryBlocks.registry_block_1537_fallthrough (by simp)
      (by rw [slotWord_eq]; exact isZero_xor_eq_zero_of_ne hown) rd3
    have rd5 := registryBlocks.registry_block_1547 (by simp) rd4
    refine RDrev.reEquivExecutionRevert hcode rd5 hd hdec ?_
    rw [transfer_ownershipBody_eq]
    exact ExecFuncBody.execBlockRevert (ExecBlock.consNormal (ExecStmt.requireTrue hcv)
      (ExecBlock.consRevert (ExecStmt.internalCallRevert (callee := checkOwnerCallee) rfl checkOwnerCallee_lookup rfl
        (ExecFuncBody.execBlockRevert (ExecBlock.consRevert (ExecStmt.requireFalse
          (by rw [howner, decide_eq_false hown])))))))
  obtain ⟨_, _, rd4⟩ := registryBlocks.registry_block_1537_taken (by simp)
    (by rw [slotWord_eq]; exact isZero_xor_ne_zero_of_eq hown) (by jump_dest) rd3
  have rd5 := registryBlocks.registry_block_1659 (by simp) (by jump_dest) rd4
  simp only [registryBlocks.registry_block_1659_stack] at rd5
  have hcheck : ExecStmt fork config (frame (toStore I)) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (.internalCall "ownable__check_owner" [] "__c0")
      (.ok (resumeAfterInternalCall (frame (toStore I)) "__c0" none) (initState σ σ₀ (Sat256.ofUInt256 g) A I)) :=
    ExecStmt.internalCallReturn (callee := checkOwnerCallee) rfl checkOwnerCallee_lookup rfl
      (ExecFuncBody.execBlockOK (ExecBlock.consNormal (ExecStmt.requireTrue (by rw [howner, decide_eq_true hown]))
        ExecBlock.nil))
  have h0 : evalExpr? config (frame (toL1 I)) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (.cast (.intLit 0) (.elem .address)) = .ok (.address 0) := evalAddressLiteral config _ _ 0
  have hne0 : evalExpr? config (frame (toL1 I)) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (.binary .ne (.var "new_owner") (.cast (.intLit 0) (.elem .address))) =
      .ok (.bool (!decide (AccountAddress.ofNat (argWord I).toNat = 0))) := by
    rw [evalExpr_binary_nonshort (by decide) (by decide),
      evalVar _ _ "new_owner" _ (by rw [store_get_ne _ _ (by decide), store_get_self]), h0]
    simp only [EvalResult.bind, bind, evalBinaryOp?]
    rw [value_address_beq]
  have hzero_iff : (AccountAddress.ofNat (argWord I).toNat = 0) ↔ (argWord I = ⟨0⟩) := by
    rw [show (0 : AccountAddress) = AccountAddress.ofNat (⟨0⟩ : UInt256).toNat from rfl]
    constructor
    · intro h
      have h2 := (addr_eq_iff_word (a := AccountAddress.ofNat (⟨0⟩ : UInt256).toNat) hcanon).mp h.symm
      rw [word_roundtrip (by decide)] at h2
      exact h2.symm
    · intro h; rw [h]
  by_cases hzero : argWord I = ⟨0⟩
  · -- `assert new_owner != empty(address)` fails
    have rd6 := registryBlocks.registry_block_68_fallthrough (by simp) (by rw [memLoad256_mem57, hzero]; rfl) rd5
    have rd7 := registryBlocks.registry_block_77 (by simp) rd6
    refine RDrev.reEquivExecutionRevert hcode rd7 hd hdec ?_
    rw [transfer_ownershipBody_eq]
    exact ExecFuncBody.execBlockRevert (ExecBlock.consNormal (ExecStmt.requireTrue hcv)
      (ExecBlock.consNormal hcheck (ExecBlock.consRevert (ExecStmt.requireFalse
        (by
          show evalExpr? config (frame (toL1 I)) _ _ = _
          rw [hne0, decide_eq_true (hzero_iff.mpr hzero)]; rfl)))))
  have rd6 := registryBlocks.registry_block_68_taken (by simp) (by rw [memLoad256_mem57]; exact fun h => hzero h)
    (by jump_dest) rd5
  have hne0' : evalExpr? config (frame (toL1 I)) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (.binary .ne (.var "new_owner") (.cast (.intLit 0) (.elem .address))) = .ok (.bool true) := by
    rw [hne0, decide_eq_false (fun h => hzero (hzero_iff.mp h))]; rfl
  have hprev : evalExpr? config (frame (toL1 I)) (initState σ σ₀ (Sat256.ofUInt256 g) A I) (.storage ownerRef) =
      .ok (.address (AccountAddress.ofNat (solcSlotWordAt ⟨0⟩ σ I).toNat)) := by
    rw [evalOwnerRead _ (by simp), storageLoad_initState_ofUInt256_solcSlotWordAt]
  have hnew : evalExpr? config (frame (toL2 σ I)) (initState σ σ₀ (Sat256.ofUInt256 g) A I) (.var "new_owner") =
      .ok (.address (AccountAddress.ofNat (argWord I).toNat)) :=
    evalVar _ _ "new_owner" _ (by rw [store_get_ne2 _ _ _ (by decide) (by decide), store_get_self])
  have hassign : assignStorageRef? config (frame (toL2 σ I)) (initState σ σ₀ (Sat256.ofUInt256 g) A I) .storage ownerRef
      (.address (AccountAddress.ofNat (argWord I).toNat)) =
      .ok (frame (toL2 σ I), Stele.EVM.storageStore (initState σ σ₀ (Sat256.ofUInt256 g) A I) I.codeOwner ⟨0⟩ (argWord I)) := by
    apply assignStorageRef_storage_vyper_scalar_value (hbackend := rfl) (hcheck := by rfl)
      (er := { base := "ownable_owner", steps := [] })
      (hleaf := Or.inl ⟨_, rfl⟩) (ty := .elem .address) (loc := vyperWordLoc ⟨0⟩ .address)
      (hbase := by simp) (her := by simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
      (hty := by show storageTypeAt? contract.storage _ = _; decide) (hloc := rfl)
    rw [storageLocStore_vyperWord_address, word_roundtrip hcanon]
    rfl
  by_cases hperm : I.perm = true
  · have rd7 := registryBlocks.registry_block_196 (by simp) hperm rd6
    rw [ulit_toNat' 288 (by decide), slotWord_eq,
      memLoad_below_write _ _ 288 256 (by rw [mem57_size]) (by omega)
        (by rw [mem57_size]; exact lt_usize _ (by decide)) (by decide), memLoad256_mem57] at rd7
    have hemit : evalExprs? config (frame (toL2 σ I))
        (Stele.EVM.storageStore (initState σ σ₀ (Sat256.ofUInt256 g) A I) I.codeOwner ⟨0⟩ (argWord I))
        [.var "previous", .var "new_owner"] =
        .ok [.address (AccountAddress.ofNat (solcSlotWordAt ⟨0⟩ σ I).toNat), .address (AccountAddress.ofNat (argWord I).toNat)] := by
      rw [evalExprs?, evalVar _ _ "previous" _ (store_get_self _ _ _), evalExprs?,
        evalVar _ _ "new_owner" _ (by rw [store_get_ne2 _ _ _ (by decide) (by decide), store_get_self]), evalExprs?]
      rfl
    have hbody : ExecTransitionBody fork config contract (initState σ σ₀ (Sat256.ofUInt256 g) A I) (toStore I)
        transfer_ownershipTransition.body
        (.returned (frame (toL2 σ I))
          (Stele.EVM.storageStore (initState σ σ₀ (Sat256.ofUInt256 g) A I) I.codeOwner ⟨0⟩ (argWord I)) none) := by
      rw [transfer_ownershipBody_eq]
      exact ExecFuncBody.execBlockOK (ExecBlock.consNormal (ExecStmt.requireTrue hcv)
        (ExecBlock.consNormal hcheck
          (ExecBlock.consNormal (ExecStmt.requireTrue hne0')
            (ExecBlock.consNormal (ExecStmt.letDecl hprev)
              (ExecBlock.consNormal (ExecStmt.assign (hperm := by first | assumption | exact Or.inr ‹_› | exact Or.inl rfl) hnew hassign)
                (ExecBlock.consNormal (ExecStmt.emit (hperm := by simpa only [storageStore_executionEnv, initState] using hperm) hemit) ExecBlock.nil))))))
    exact rd7.reEquivExecutionGen hcode hd hdec hbody (by rw [storageStore_accountMap]; rfl)
      (returnEquiv.fallthrough rfl rfl (by native_decide))
  · have hpf : I.perm = false := by simpa using hperm
    have r1 := rd6.jumpdest (by native_decide) (by evm_ov)
    have r2 := r1.push0 (by native_decide) (by evm_ov)
    obtain ⟨_, _, r3⟩ := RD.sload r2 (by native_decide) (by evm_ov)
    have r4 := r3.push2 (UInt256.ofNat 288) (by native_decide) (by evm_ov)
    have r5 := RD.genMstore r4 (by native_decide) (by evm_ov)
    have r6 := r5.push2 (UInt256.ofNat 256) (by native_decide) (by evm_ov)
    have r7 := RD.genMload r6 (by native_decide) (by evm_ov)
    have r8 := r7.push0 (by native_decide) (by evm_ov)
    have rs := r8.sstoreStatic hpf (by native_decide) (by evm_ov)
    refine RDstatic.reEquivStaticHalt hcode rs hd hdec ?_
    rw [transfer_ownershipBody_eq]
    exact ExecFuncBody.execBlockStatic (ExecBlock.consNormal (ExecStmt.requireTrue hcv)
      (ExecBlock.consNormal hcheck
        (ExecBlock.consNormal (ExecStmt.requireTrue hne0')
          (ExecBlock.consNormal (ExecStmt.letDecl hprev)
            (ExecBlock.consStatic (ExecStmt.assignStatic hnew hassign (by show I.perm = false; exact hpf)))))))

end Tests.Pipeline.VyperRegistry
