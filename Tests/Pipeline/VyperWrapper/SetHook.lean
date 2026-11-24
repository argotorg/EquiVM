import Tests.Pipeline.VyperWrapper.Helpers

variable {fork : Ethereum.Fork}

/-!
# Wrapper `setHook(address)`

Dispatcher bucket 3, arm entry pc 36: the guard, the address validation (pc 46), the
`hook == empty(address)` check (pc 57, revert at 67), and the store (pc 179).
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
open Reasoning.VyperImmutables Reasoning.VyperBounded

namespace Tests.Pipeline.VyperWrapper

set_option maxRecDepth 2000000

theorem setHookBody_eq : setHookTransition.body =
    [.require (.binary .eq (.env .callvalue) (.intLit 0)),
     .require (.binary .eq (.storage hookRef) (.cast (.intLit 0) (.elem .address))),
     .assign .storage hookRef (.var "target")] := by rfl

abbrev setHookStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "target" (.address (AccountAddress.ofNat (argWord I).toNat))

theorem setHookDecode_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size)
    (hcanon : (argWord I).toNat < EVM.addressModulus) :
    config.externalABI.decodeCalldata? (setHookTransition.params.map Param.name)
      (transitionSignature setHookTransition).paramTypes I.calldata = some (setHookStore I) := by
  rw [argWord_eq] at hcanon
  simpa [config, contract, Syntax.contractSyntax, setHookTransition, setHookStore, argWord_eq] using
    decodeCalldataWithMode_vyper_address_ok (cd := I.calldata) (x := "target") hsz36 hcanon

theorem setHookDecode_short {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    config.externalABI.decodeCalldata? (setHookTransition.params.map Param.name)
      (transitionSignature setHookTransition).paramTypes I.calldata = none := by
  simpa [config, contract, Syntax.contractSyntax, setHookTransition] using
    decodeCalldataWithMode_vyper_address_none_short (cd := I.calldata) (x := "target") hsz hshort

theorem setHookDecode_noncanon {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size)
    (hnc : ¬ (argWord I).toNat < EVM.addressModulus) :
    config.externalABI.decodeCalldata? (setHookTransition.params.map Param.name)
      (transitionSignature setHookTransition).paramTypes I.calldata = none := by
  rw [argWord_eq] at hnc
  simpa [config, contract, Syntax.contractSyntax, setHookTransition] using
    decodeCalldataWithMode_vyper_address_none_noncanon (cd := I.calldata) (x := "target") hsz36 hnc

/-- `setHook(address)`: the theorem `Correct.lean` routes selector 1 to. -/
theorem wrapperSetHookBody {σ σ₀ A I} {g : UInt256} (imms : Store) (hfit : immutablesFit contract imms)
    (hwf : storageWF σ I)
    (hcode : I.code = immutableLayout.deployed wrapperBytecode imms) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (wrapperSelBytes 1)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I (restrictImmutables contract imms) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (wrapperSelBytes 1) rfl hsel
  have hcode' : I.code = wrapperBytecode ++ immutableLayout.suffixWords (wordsOf imms) := by
    rw [hcode, deployed_of_fit hfit]
  obtain ⟨_, _, rd⟩ := wrapperReachSetHookBody (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) hcode' hsz hsize hsel
  have hd : dispatchMsg contract I.calldata = some setHookTransition :=
    wrapperDispatch_setHook (selIs_exclusive (by native_decide) hsel) hsel
  by_cases hshort : I.calldata.size < 36
  · have rd1 := wrapperBlocks.wrapper_block_36_taken (by simp) (guard_short hsize hshort)
      (by apply D_J_contains_append_left; jump_dest) rd
    have rd2 := wrapperBlocks.wrapper_block_1760 (by simp) rd1
    exact RDrev.reEquivDecodingFailed hcode' rd2 hd (setHookDecode_short hsz hshort)
  have hsz36 : 36 ≤ I.calldata.size := by omega
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · have rd1 := wrapperBlocks.wrapper_block_36_taken (by simp) (guard_wv hwv)
      (by apply D_J_contains_append_left; jump_dest) rd
    have rd2 := wrapperBlocks.wrapper_block_1760 (by simp) rd1
    exact RDrev.reEquivOfDispatch hcode' hd
      (fun _ => by rw [setHookBody_eq]; exact bodyReverts_nonPayable (by simpa [initState] using hwv)) rd2
  have rd1 := wrapperBlocks.wrapper_block_36_fallthrough (by simp) (guard_ok hwv hsz36 hsize) rd
  by_cases hcanon : (argWord I).toNat < EVM.addressModulus
  swap
  · have rd2 := wrapperBlocks.wrapper_block_46_taken (by simp)
      (by intro h; exact hcanon (u256_lt_addressModulus_of_shiftRight160_zero _ h))
      (by apply D_J_contains_append_left; jump_dest) rd1
    have rd3 := wrapperBlocks.wrapper_block_1760 (by simp [wrapperBlocks.wrapper_block_46_taken_stack]) rd2
    exact RDrev.reEquivDecodingFailed hcode' rd3 hd (setHookDecode_noncanon hsz36 hcanon)
  have rd2 := wrapperBlocks.wrapper_block_46_fallthrough (by simp) (u256_shiftRight160_zero_of_lt _ hcanon) rd1
  simp only [wrapperBlocks.wrapper_block_46_fallthrough_stack] at rd2
  have hdec := setHookDecode_ok (I := I) hsz36 hcanon
  have hcv : evalExpr? config (frame imms (setHookStore I)) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (.binary .eq (.env .callvalue) (.intLit 0)) = .ok (.bool true) :=
    evalCallvalueEq_true (by simpa [initState] using hwv)
  have hhook : evalExpr? config (frame imms (setHookStore I)) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (.binary .eq (.storage hookRef) (.cast (.intLit 0) (.elem .address))) =
      .ok (.bool (decide (solcSlotWordAt ⟨0⟩ σ I = ⟨0⟩))) := by
    rw [evalExpr_binary_nonshort (by decide) (by decide), evalHookRead imms _ _ (by simp), evalAddrZero,
      storageLoad_initState_ofUInt256_solcSlotWordAt]
    simp only [EvalResult.bind, bind, evalBinaryOp?, value_address_beq, pure]
    rw [show decide (AccountAddress.ofNat (solcSlotWordAt ⟨0⟩ σ I).toNat = AccountAddress.ofNat 0) =
      decide (solcSlotWordAt ⟨0⟩ σ I = ⟨0⟩) from by simp only [addrZero_iff_word hwf.1]]
  by_cases hz : solcSlotWordAt ⟨0⟩ σ I = ⟨0⟩
  swap
  · -- the hook is set: the guard reverts
    obtain ⟨_, _, rd3⟩ := wrapperBlocks.wrapper_block_57_fallthrough (by simp)
      (by rw [slotWord_eq]; exact isZero_eq_zero_of_ne hz) rd2
    have rd4 := wrapperBlocks.wrapper_block_67 (by simp [wrapperBlocks.wrapper_block_57_fallthrough_stack]) rd3
    refine RDrev.reEquivExecutionRevert hcode' rd4 hd hdec ?_
    rw [setHookBody_eq]
    exact ExecFuncBody.execBlockRevert (ExecBlock.consNormal (ExecStmt.requireTrue hcv)
      (ExecBlock.consRevert (ExecStmt.requireFalse (by rw [hhook, decide_eq_false hz]))))
  obtain ⟨_, _, rd3⟩ := wrapperBlocks.wrapper_block_57_taken (by simp)
    (by rw [slotWord_eq, hz]; decide) (by apply D_J_contains_append_left; jump_dest) rd2
  simp only [wrapperBlocks.wrapper_block_57_taken_stack, wrapperBlocks.wrapper_block_57_taken_memory,
    ulit_toNat' 64 (by decide)] at rd3
  have hload : memLoad (UInt256.ofNat 64) ((argWord I).toByteArray.write 0 (wrapperDispatchMem 3) 64 32) = argWord I :=
    memLoad_write_back _ _ 64 (by decide) (by rw [dispatchMem_size 3 (by decide)]; exact lt_usize _ (by decide))
  have htarget : evalExpr? config (frame imms (setHookStore I)) (initState σ σ₀ (Sat256.ofUInt256 g) A I) (.var "target") =
      .ok (.address (AccountAddress.ofNat (argWord I).toNat)) :=
    evalVar imms _ _ "target" _ (store_get_self _ _ _)
  have hassign : assignStorageRef? config (frame imms (setHookStore I)) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      .storage hookRef (.address (AccountAddress.ofNat (argWord I).toNat)) =
      .ok (frame imms (setHookStore I), Stele.EVM.storageStore (initState σ σ₀ (Sat256.ofUInt256 g) A I) I.codeOwner ⟨0⟩ (argWord I)) := by
    apply assignStorageRef_storage_vyper_scalar_value (hbackend := rfl) (hcheck := by rfl)
      (er := { base := "hook", steps := [] })
      (hleaf := Or.inl ⟨_, rfl⟩) (ty := .elem .address) (loc := vyperWordLoc ⟨0⟩ .address) (hbase := by simp)
      (her := by simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
      (hty := by show storageTypeAt? contract.storage _ = _; decide) (hloc := rfl)
    rw [storageLocStore_vyperWord_address, word_roundtrip hcanon]
    rfl
  have hhookT : evalExpr? config (frame imms (setHookStore I)) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (.binary .eq (.storage hookRef) (.cast (.intLit 0) (.elem .address))) = .ok (.bool true) := by
    rw [hhook, decide_eq_true hz]
  by_cases hperm : I.perm = true
  swap
  · have hpf : I.perm = false := by simpa using hperm
    have r1 := rd3.jumpdest
      (by append_decode(wrapperBytecode, (immutableLayout.suffixWords (wordsOf imms)), (⟨179⟩ : UInt256), .JUMPDEST, none))
      (by evm_ov)
    have r2 := r1.push1 (UInt256.ofNat 64)
      (by append_decode(wrapperBytecode, (immutableLayout.suffixWords (wordsOf imms)), (⟨180⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 64), 1)))
      (by evm_ov)
    have r3 := RD.genMload r2
      (by append_decode(wrapperBytecode, (immutableLayout.suffixWords (wordsOf imms)), (⟨182⟩ : UInt256), .MLOAD, none))
      (by evm_ov)
    have r4 := r3.push0
      (by append_decode(wrapperBytecode, (immutableLayout.suffixWords (wordsOf imms)), (⟨183⟩ : UInt256), .PUSH0, none))
      (by evm_ov)
    have rs := r4.sstoreStatic hpf
      (by append_decode(wrapperBytecode, (immutableLayout.suffixWords (wordsOf imms)), (⟨184⟩ : UInt256), .SSTORE, none))
      (by evm_ov)
    refine RDstatic.reEquivStaticHalt hcode' rs hd hdec ?_
    rw [setHookBody_eq]
    exact ExecFuncBody.execBlockStatic (ExecBlock.consNormal (ExecStmt.requireTrue hcv)
      (ExecBlock.consNormal (ExecStmt.requireTrue hhookT)
        (ExecBlock.consStatic (ExecStmt.assignStatic htarget hassign (by show I.perm = false; exact hpf)))))
  have rd4 := wrapperBlocks.wrapper_block_179 (by simp) hperm rd3
  rw [hload] at rd4
  have hbody : ExecTransitionBody fork config contract (initState σ σ₀ (Sat256.ofUInt256 g) A I) (setHookStore I)
      setHookTransition.body
      (.returned (frame imms (setHookStore I))
        (Stele.EVM.storageStore (initState σ σ₀ (Sat256.ofUInt256 g) A I) I.codeOwner ⟨0⟩ (argWord I)) none)
      (restrictImmutables contract imms) := by
    rw [setHookBody_eq]
    exact ExecFuncBody.execBlockOK (ExecBlock.consNormal (ExecStmt.requireTrue hcv)
      (ExecBlock.consNormal (ExecStmt.requireTrue hhookT)
        (ExecBlock.consNormal (ExecStmt.assign (hperm := by first | assumption | exact Or.inr ‹_› | exact Or.inl rfl) htarget hassign) ExecBlock.nil)))
  exact rd4.reEquivExecutionGen hcode' hd hdec hbody (by rw [storageStore_accountMap]; rfl)
    (returnEquiv.fallthrough rfl rfl (by native_decide))

end Tests.Pipeline.VyperWrapper
