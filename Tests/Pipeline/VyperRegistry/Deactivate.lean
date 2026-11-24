import Tests.Pipeline.VyperRegistry.Helpers

variable {fork : Ethereum.Fork}

/-!
# Registry `deactivate(uint256)`

Dispatcher bucket 1, arm entry pc 1135: the guard, `ownable._check_owner`, the three field words
of `entries[id]` into memory (pc 1152, the local `entry`), `assert entry.active`, the `SSTORE` of
`active := False` (pc 1341), and `totalWeight -= entry.weight` with its underflow check (pc 1319/1359).
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
  Reasoning.VyperBounded

namespace Tests.Pipeline.VyperRegistry

set_option maxRecDepth 2000000

abbrev twRef : StorageRef := { base := "totalWeight", steps := [] }
abbrev activeRef : StorageRef := { base := "entries", steps := [.mindex (.var "id"), .field "active"] }

theorem deactivateBody_eq : deactivateTransition.body =
    [.require (.binary .eq (.env .callvalue) (.intLit 0)),
     .internalCall "ownable__check_owner" [] "__c0",
     .letDecl "entry" (some (.tuple [.elem .address, .elem (.int (.uint ⟨256, by decide⟩)), .elem .bool]))
       (.storage { base := "entries", steps := [.mindex (.var "id")] }),
     .require (.field (.var "entry") "active"),
     .assign .storage activeRef (.boolLit false),
     .assign .storage twRef (.inRange (.uint ⟨256, by decide⟩) (.binary .sub (.storage twRef) (.field (.var "entry") "weight")))] := by rfl

abbrev dStore (I : ExecutionEnv) : Store := (∅ : Store).insert "id" (uint256Value (argWord I))
abbrev dL1 (I : ExecutionEnv) : Store := (dStore I).insert "__c0" .unit

theorem dDecode_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    config.externalABI.decodeCalldata? (deactivateTransition.params.map Param.name)
      (transitionSignature deactivateTransition).paramTypes I.calldata = some (dStore I) := by
  simpa [config, contract, Syntax.contractSyntax, deactivateTransition, dStore, argWord_eq] using
    decodeMode_uint256_ok "id" I.calldata hsz36

theorem dDecode_short {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    config.externalABI.decodeCalldata? (deactivateTransition.params.map Param.name)
      (transitionSignature deactivateTransition).paramTypes I.calldata = none := by
  simpa [config, contract, Syntax.contractSyntax, deactivateTransition] using
    decodeMode_uint256_none_short "id" I.calldata hsz hshort

/-- The words of `entries[id]` at the initial state. -/
abbrev dAcc (σ : AccountMap) (I : ExecutionEnv) : UInt256 := solcSlotWordAt (entrySlot (argWord I)) σ I
abbrev dWt (σ : AccountMap) (I : ExecutionEnv) : UInt256 := solcSlotWordAt (entrySlot (argWord I) + UInt256.ofNat 1) σ I
abbrev dAct (σ : AccountMap) (I : ExecutionEnv) : UInt256 := solcSlotWordAt (entrySlot (argWord I) + UInt256.ofNat 2) σ I

/-- The hash scratch (bucket 1) and the memory after the three field loads. -/
abbrev dHash (I : ExecutionEnv) : ByteArray :=
  (UInt256.ofNat 1).toByteArray.write 0 ((argWord I).toByteArray.write 0 (registryDispatchMem 1) 32 32) 0 32
abbrev dMem (σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  (dAct σ I).toByteArray.write 0 ((dWt σ I).toByteArray.write 0 ((dAcc σ I).toByteArray.write 0 (dHash I) 256 32) 288 32) 320 32

theorem dHash_size (I : ExecutionEnv) : (dHash I).size = 64 := by
  have h1 : ((argWord I).toByteArray.write 0 (registryDispatchMem 1) 32 32).size = 64 :=
    toByteArray_write32_size_of_ge _ _ 32 32 64 (dispatchMem_size 1 (by decide)) (by omega) (lt_usize _ (by decide)) rfl
  rw [byteArray_write_size_of_inBounds _ _ _ _ (by rw [toByteArray_size]) (by rw [h1]; omega), h1]

theorem dMem_sizes (σ : AccountMap) (I : ExecutionEnv) :
    ((dAcc σ I).toByteArray.write 0 (dHash I) 256 32).size = 288 ∧
    ((dWt σ I).toByteArray.write 0 ((dAcc σ I).toByteArray.write 0 (dHash I) 256 32) 288 32).size = 320 ∧
    (dMem σ I).size = 352 := by
  have h1 : ((dAcc σ I).toByteArray.write 0 (dHash I) 256 32).size = 288 :=
    toByteArray_write32_size_of_ge _ _ 256 64 288 (dHash_size I) (by omega) (lt_usize _ (by decide)) rfl
  have h2 := toByteArray_write32_size_of_ge _ (dWt σ I) 288 288 320 h1 (by omega) (lt_usize _ (by decide)) rfl
  exact ⟨h1, h2, toByteArray_write32_size_of_ge _ (dAct σ I) 320 320 352 h2 (by omega) (lt_usize _ (by decide)) rfl⟩

theorem memLoad320_dMem (σ : AccountMap) (I : ExecutionEnv) : memLoad (UInt256.ofNat 320) (dMem σ I) = dAct σ I :=
  memLoad_write_back _ _ 320 (by decide) (by rw [(dMem_sizes σ I).2.1]; exact lt_usize _ (by decide))

theorem memLoad288_dMem (σ : AccountMap) (I : ExecutionEnv) : memLoad (UInt256.ofNat 288) (dMem σ I) = dWt σ I := by
  obtain ⟨h1, h2, _⟩ := dMem_sizes σ I
  rw [memLoad_below_write _ _ 320 288 (by rw [h2]) (by omega) (by rw [h2]; exact lt_usize _ (by decide)) (by decide)]
  exact memLoad_write_back _ _ 288 (by decide) (by rw [h1]; exact lt_usize _ (by decide))

/-- The scratch words re-written over the loaded memory (pc 1319). -/
abbrev dMem2 (σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  (UInt256.ofNat 1).toByteArray.write 0 ((argWord I).toByteArray.write 0 (dMem σ I) 32 32) 0 32

theorem memLoad288_dMem2 (σ : AccountMap) (I : ExecutionEnv) : memLoad (UInt256.ofNat 288) (dMem2 σ I) = dWt σ I := by
  have h3 := (dMem_sizes σ I).2.2
  have hB : ((argWord I).toByteArray.write 0 (dMem σ I) 32 32).size = 352 := by
    rw [byteArray_write_size_of_inBounds _ _ _ _ (by rw [toByteArray_size]) (by rw [h3]; omega)]; exact h3
  rw [memLoad_above_write _ _ 0 288 (by rw [toByteArray_size]) (by omega) (by omega) (by omega) (by decide),
    memLoad_above_write _ _ 32 288 (by rw [toByteArray_size]) (by omega) (by omega) (by omega) (by decide)]
  exact memLoad288_dMem σ I

/-- `deactivate(uint256)`: the theorem `Correct.lean` routes selector 6 to. -/
theorem registryDeactivateBody {σ σ₀ A I} {g : UInt256} (hwf : storageWF σ I)
    (hcode : I.code = registryBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (registrySelBytes 6)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (registrySelBytes 6) rfl hsel
  obtain ⟨_, _, rd⟩ := registryReachDeactivateBody (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) hcode hsz hsize hsel
  have hd : dispatchMsg contract I.calldata = some deactivateTransition :=
    registryDispatch_deactivate (selIs_exclusive (by native_decide) hsel) (selIs_exclusive (by native_decide) hsel)
      (selIs_exclusive (by native_decide) hsel) (selIs_exclusive (by native_decide) hsel)
      (selIs_exclusive (by native_decide) hsel) (selIs_exclusive (by native_decide) hsel) hsel
  by_cases hshort : I.calldata.size < 36
  · have rd1 := registryBlocks.registry_block_1135_taken (by simp) (guard_short hsize hshort) (by jump_dest) rd
    have rd2 := registryBlocks.registry_block_1661 (by simp) rd1
    exact RDrev.reEquivDecodingFailed hcode rd2 hd (dDecode_short hsz hshort)
  have hsz36 : 36 ≤ I.calldata.size := by omega
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · have rd1 := registryBlocks.registry_block_1135_taken (by simp) (guard_wv hwv) (by jump_dest) rd
    have rd2 := registryBlocks.registry_block_1661 (by simp) rd1
    exact RDrev.reEquivOfDispatch hcode hd
      (fun _ => by rw [deactivateBody_eq]; exact bodyReverts_nonPayable (by simpa [initState] using hwv)) rd2
  have rd1 := registryBlocks.registry_block_1135_fallthrough (by simp) (guard_ok hwv hsz36 hsize) rd
  have rd2 := registryBlocks.registry_block_1145 (by simp) (by jump_dest) rd1
  simp only [registryBlocks.registry_block_1145_stack] at rd2
  have hdec := dDecode_ok (I := I) hsz36
  have hcv : evalExpr? config (frame (dStore I)) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (.binary .eq (.env .callvalue) (.intLit 0)) = .ok (.bool true) :=
    evalCallvalueEq_true (by simpa [initState] using hwv)
  have howner : evalExpr? config (frame ∅) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (.binary .eq (.env .caller) (.storage ownerRef)) =
      .ok (.bool (decide (UInt256.ofNat I.source.val = solcSlotWordAt ⟨0⟩ σ I))) := by
    rw [evalCallerEqOwner _ (by simp) (by rw [storageLoad_initState_ofUInt256_solcSlotWordAt]; exact hwf.1),
      storageLoad_initState_ofUInt256_solcSlotWordAt]
    rfl
  by_cases hown : UInt256.ofNat I.source.val = solcSlotWordAt ⟨0⟩ σ I
  swap
  · obtain ⟨_, _, rd3⟩ := registryBlocks.registry_block_1537_fallthrough (by simp)
      (by rw [slotWord_eq]; exact isZero_xor_eq_zero_of_ne hown) rd2
    have rd4 := registryBlocks.registry_block_1547 (by simp) rd3
    refine RDrev.reEquivExecutionRevert hcode rd4 hd hdec ?_
    rw [deactivateBody_eq]
    exact ExecFuncBody.execBlockRevert (ExecBlock.consNormal (ExecStmt.requireTrue hcv)
      (ExecBlock.consRevert (ExecStmt.internalCallRevert (callee := checkOwnerCallee) rfl checkOwnerCallee_lookup rfl
        (ExecFuncBody.execBlockRevert (ExecBlock.consRevert (ExecStmt.requireFalse
          (by rw [howner, decide_eq_false hown])))))))
  obtain ⟨_, _, rd3⟩ := registryBlocks.registry_block_1537_taken (by simp)
    (by rw [slotWord_eq]; exact isZero_xor_ne_zero_of_eq hown) (by jump_dest) rd2
  have rd4 := registryBlocks.registry_block_1659 (by simp) (by jump_dest) rd3
  simp only [registryBlocks.registry_block_1659_stack] at rd4
  have hcheck : ExecStmt fork config (frame (dStore I)) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (.internalCall "ownable__check_owner" [] "__c0")
      (.ok (resumeAfterInternalCall (frame (dStore I)) "__c0" none) (initState σ σ₀ (Sat256.ofUInt256 g) A I)) :=
    ExecStmt.internalCallReturn (callee := checkOwnerCallee) rfl checkOwnerCallee_lookup rfl
      (ExecFuncBody.execBlockOK (ExecBlock.consNormal (ExecStmt.requireTrue (by rw [howner, decide_eq_true hown]))
        ExecBlock.nil))
  -- pc 1152: the struct read
  have hkec := keccak_entry 1 (by decide) (argWord I)
  have hentry : evalExpr? config (frame (dL1 I)) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (.storage { base := "entries", steps := [.mindex (.var "id")] }) =
      .ok (.struct "Entry" [("account", .address (AccountAddress.ofNat (dAcc σ I).toNat)),
        ("weight", uint256Value (dWt σ I)), ("active", wordToElem .bool (dAct σ I))]) := by
    rw [evalEntriesRead _ _ (argWord I) "id" (by rw [store_get_ne _ _ (by decide), store_get_self]) (by simp)]
    simp only [entryValue, storageLoad_initState_ofUInt256_solcSlotWordAt]
  set L2 : Store := (dL1 I).insert "entry" (.struct "Entry" [("account", .address (AccountAddress.ofNat (dAcc σ I).toNat)),
        ("weight", uint256Value (dWt σ I)), ("active", wordToElem .bool (dAct σ I))]) with hL2
  have hactive : evalExpr? config (frame L2) (initState σ σ₀ (Sat256.ofUInt256 g) A I) (.field (.var "entry") "active") =
      .ok (wordToElem .bool (dAct σ I)) :=
    evalExpr_field_local (store_get_self _ _ _) rfl
  have hweight : ∀ evm, evalExpr? config (frame L2) evm (.field (.var "entry") "weight") = .ok (uint256Value (dWt σ I)) :=
    fun evm => evalExpr_field_local (store_get_self _ _ _) rfl
  by_cases hact : dAct σ I = ⟨0⟩
  · -- inactive: `assert entry.active` fails
    obtain ⟨_, _, rd5⟩ := registryBlocks.registry_block_1152_fallthrough (by simp)
      (by
        simp only [ulit_toNat' 32 (by decide), ulit_toNat' 256 (by decide), ulit_toNat' 288 (by decide),
          ulit_toNat' 320 (by decide), show (⟨0⟩ : UInt256).toNat = 0 from rfl]
        rw [hkec, slotWord_eq, slotWord_eq, slotWord_eq, memLoad320_dMem, hact]; rfl) rd4
    have rd6 := registryBlocks.registry_block_1200 (by simp) rd5
    refine RDrev.reEquivExecutionRevert hcode rd6 hd hdec ?_
    rw [deactivateBody_eq]
    exact ExecFuncBody.execBlockRevert (ExecBlock.consNormal (ExecStmt.requireTrue hcv)
      (ExecBlock.consNormal hcheck (ExecBlock.consNormal (ExecStmt.letDecl hentry)
        (ExecBlock.consRevert (ExecStmt.requireFalse (by
          show evalExpr? config (frame L2) _ _ = _
          rw [hactive, hact]; rfl))))))
  obtain ⟨_, _, rd5⟩ := registryBlocks.registry_block_1152_taken (by simp)
    (by
      simp only [ulit_toNat' 32 (by decide), ulit_toNat' 256 (by decide), ulit_toNat' 288 (by decide),
        ulit_toNat' 320 (by decide), show (⟨0⟩ : UInt256).toNat = 0 from rfl]
      rw [hkec, slotWord_eq, slotWord_eq, slotWord_eq, memLoad320_dMem]; exact fun h => hact h) (by jump_dest) rd4
  simp only [registryBlocks.registry_block_1152_taken_memory, ulit_toNat' 32 (by decide), ulit_toNat' 256 (by decide),
    ulit_toNat' 288 (by decide), ulit_toNat' 320 (by decide), show (⟨0⟩ : UInt256).toNat = 0 from rfl] at rd5
  rw [hkec, slotWord_eq, slotWord_eq, slotWord_eq] at rd5
  have hactTrue : evalExpr? config (frame L2) (initState σ σ₀ (Sat256.ofUInt256 g) A I) (.field (.var "entry") "active") =
      .ok (.bool true) := by
    rw [hactive]
    rcases hwf.2 (argWord I) with ⟨_, h | h⟩
    · exact absurd h hact
    · show EvalResult.ok (wordToElem .bool (solcSlotWordAt (entrySlot (argWord I) + UInt256.ofNat 2) σ I)) = _
      rw [h]; rfl
  have hassignA : assignStorageRef? config (frame L2) (initState σ σ₀ (Sat256.ofUInt256 g) A I) .storage activeRef
      (.bool false) = .ok (frame L2, Stele.EVM.storageStore (initState σ σ₀ (Sat256.ofUInt256 g) A I) I.codeOwner
        (entrySlot (argWord I) + UInt256.ofNat 2) ⟨0⟩) := by
    apply assignStorageRef_storage_vyper_scalar_value (hbackend := rfl) (hcheck := by rfl)
      (er := { base := "entries", steps := [.mindex (.int (Int.ofNat (argWord I).toNat)), .field "active"] })
      (hleaf := Or.inl ⟨_, rfl⟩) (ty := .elem .bool) (loc := vyperWordLoc (entrySlot (argWord I) + UInt256.ofNat 2) .bool)
      (hbase := by simp [hL2])
      (her := evalEntriesFieldRef _ _ (argWord I) "id" "active" (by rw [hL2, store_get_ne2 _ _ _ (by decide) (by decide), store_get_self]))
      (hty := rfl) (hloc := rfl)
    rw [storageLocStore_vyperWord_value _ _ _ _ ⟨0⟩ rfl]
    rfl
  have hkec2 := keccak_entry_over (dMem σ I) (by rw [(dMem_sizes σ I).2.2]; omega) (argWord I)
  have htw : evalExpr? config (frame L2)
      (Stele.EVM.storageStore (initState σ σ₀ (Sat256.ofUInt256 g) A I) I.codeOwner (entrySlot (argWord I) + UInt256.ofNat 2) ⟨0⟩)
      (.storage twRef) =
      .ok (uint256Value (solcSlotWordAt (UInt256.ofNat 20)
        (sstoreAccountMap I.codeOwner σ (entrySlot (argWord I) + UInt256.ofNat 2) ⟨0⟩) I)) := by
    rw [evalExpr_storage_vyper_uint256_backend (hbackend := rfl) (hcheck := by rfl)
        (er := { base := "totalWeight", steps := [] }) (physicalSlot := UInt256.ofNat 20) (hbase := by simp [hL2])
        (her := by simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
        (hty := by show storageTypeAt? contract.storage _ = _; decide) (hloc := rfl),
      storageLoad_eq_slotWord, storageStore_executionEnv, storageStore_accountMap]
    rfl
  by_cases hperm : I.perm = true
  swap
  · have hpf : I.perm = false := by simpa using hperm
    have r1 := rd5.jumpdest (by native_decide) (by evm_ov)
    have r2 := r1.push0 (by native_decide) (by evm_ov)
    have r3 := r2.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
    have r4 := r3.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
    have r5 := r4.calldataload (by native_decide) (by evm_ov)
    have r6 := r5.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
    have r7 := RD.genMstore r6 (by native_decide) (by evm_ov)
    have r8 := r7.push0 (by native_decide) (by evm_ov)
    have r9 := RD.genMstore r8 (by native_decide) (by evm_ov)
    have r10 := r9.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
    have r11 := r10.push0 (by native_decide) (by evm_ov)
    have r12 := RD.genKeccak256 r11 (by native_decide) (by evm_ov)
    have r13 := r12.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
    have r14 := r13.dup2 (by native_decide) (by evm_ov)
    have r15 := r14.add (by native_decide) (by evm_ov)
    have r16 := r15.swap1 (by native_decide) (by evm_ov)
    have r17 := r16.pop (by native_decide) (by evm_ov)
    have rs := r17.sstoreStatic hpf (by native_decide) (by evm_ov)
    refine RDstatic.reEquivStaticHalt hcode rs hd hdec ?_
    rw [deactivateBody_eq]
    exact ExecFuncBody.execBlockStatic (ExecBlock.consNormal (ExecStmt.requireTrue hcv)
      (ExecBlock.consNormal hcheck (ExecBlock.consNormal (ExecStmt.letDecl hentry)
        (ExecBlock.consNormal (ExecStmt.requireTrue hactTrue)
          (ExecBlock.consStatic (ExecStmt.assignStatic (by rw [evalExpr?]; rfl) hassignA (by show I.perm = false; exact hpf)))))))
  by_cases hund : (dWt σ I).toNat ≤ (solcSlotWordAt (UInt256.ofNat 20) (sstoreAccountMap I.codeOwner σ (entrySlot (argWord I) + UInt256.ofNat 2) ⟨0⟩) I).toNat
  swap
  · obtain ⟨_, _, rd6⟩ := registryBlocks.registry_block_1319_taken (by simp) hperm
      (by
        simp only [ulit_toNat' 32 (by decide), show (⟨0⟩ : UInt256).toNat = 0 from rfl]
        rw [hkec2, memLoad288_dMem2, slotWord_eq]
        rw [ugt_one (by
          show (solcSlotWordAt (UInt256.ofNat 20) _ I).toNat < (UInt256.sub (solcSlotWordAt (UInt256.ofNat 20) _ I) (dWt σ I)).toNat
          rw [usub_toNat_underflow (by omega)]
          have hlt := (dWt σ I).val.isLt
          change (dWt σ I).toNat < UInt256.size at hlt
          omega)]
        decide) (by jump_dest) rd5
    have rd7 := registryBlocks.registry_block_1661 (by simp [registryBlocks.registry_block_1319_taken_stack]) rd6
    refine RDrev.reEquivExecutionRevert hcode rd7 hd hdec ?_
    rw [deactivateBody_eq]
    exact ExecFuncBody.execBlockRevert (ExecBlock.consNormal (ExecStmt.requireTrue hcv)
      (ExecBlock.consNormal hcheck (ExecBlock.consNormal (ExecStmt.letDecl hentry)
        (ExecBlock.consNormal (ExecStmt.requireTrue hactTrue)
          (ExecBlock.consNormal (ExecStmt.assign (hperm := by first | assumption | exact Or.inr ‹_› | exact Or.inl rfl) (by rw [evalExpr?]; rfl) hassignA)
            (ExecBlock.consRevert (ExecStmt.assignExprRevert
              (evalExpr_uint256_sub_underflow htw (hweight _) (by omega)))))))))
  obtain ⟨_, _, rd6⟩ := registryBlocks.registry_block_1319_fallthrough (by simp) hperm
    (by
      simp only [ulit_toNat' 32 (by decide), show (⟨0⟩ : UInt256).toNat = 0 from rfl]
      rw [hkec2, memLoad288_dMem2, slotWord_eq]
      exact ugt_zero (by
        show (UInt256.sub (solcSlotWordAt (UInt256.ofNat 20) _ I) (dWt σ I)).toNat ≤ (solcSlotWordAt (UInt256.ofNat 20) _ I).toNat
        rw [usub_toNat hund]; omega)) rd5
  simp only [registryBlocks.registry_block_1319_fallthrough_stack, ulit_toNat' 32 (by decide),
    show (⟨0⟩ : UInt256).toNat = 0 from rfl] at rd6
  rw [hkec2, memLoad288_dMem2, slotWord_eq] at rd6
  have rd7 := registryBlocks.registry_block_1359 (by simp) hperm rd6
  have hsub := evalExpr_uint256_sub htw (hweight _) hund
  have hassignT : assignStorageRef? config (frame L2)
      (Stele.EVM.storageStore (initState σ σ₀ (Sat256.ofUInt256 g) A I) I.codeOwner (entrySlot (argWord I) + UInt256.ofNat 2) ⟨0⟩)
      .storage twRef (uint256Value (UInt256.sub (solcSlotWordAt (UInt256.ofNat 20)
        (sstoreAccountMap I.codeOwner σ (entrySlot (argWord I) + UInt256.ofNat 2) ⟨0⟩) I) (dWt σ I))) =
      .ok (frame L2, Stele.EVM.storageStore
        (Stele.EVM.storageStore (initState σ σ₀ (Sat256.ofUInt256 g) A I) I.codeOwner (entrySlot (argWord I) + UInt256.ofNat 2) ⟨0⟩)
        I.codeOwner (UInt256.ofNat 20) (UInt256.sub (solcSlotWordAt (UInt256.ofNat 20)
          (sstoreAccountMap I.codeOwner σ (entrySlot (argWord I) + UInt256.ofNat 2) ⟨0⟩) I) (dWt σ I))) := by
    apply assignStorageRef_storage_vyper_scalar (hbackend := rfl) (hcheck := by rfl)
      (er := { base := "totalWeight", steps := [] })
      (hleaf := Or.inl ⟨_, rfl⟩) (ty := .elem (.int (.uint ⟨256, by decide⟩))) (loc := vyperUint256Loc (UInt256.ofNat 20))
      (hbase := by simp [hL2]) (her := by simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
      (hty := by show storageTypeAt? contract.storage _ = _; decide) (hloc := rfl)
    erw [storageLocStore_uint256, storageStore_executionEnv]
    rfl
  have hbody : ExecTransitionBody fork config contract (initState σ σ₀ (Sat256.ofUInt256 g) A I) (dStore I)
      deactivateTransition.body
      (.returned (frame L2)
        (Stele.EVM.storageStore
          (Stele.EVM.storageStore (initState σ σ₀ (Sat256.ofUInt256 g) A I) I.codeOwner (entrySlot (argWord I) + UInt256.ofNat 2) ⟨0⟩)
          I.codeOwner (UInt256.ofNat 20) (UInt256.sub (solcSlotWordAt (UInt256.ofNat 20)
            (sstoreAccountMap I.codeOwner σ (entrySlot (argWord I) + UInt256.ofNat 2) ⟨0⟩) I) (dWt σ I))) none) := by
    rw [deactivateBody_eq]
    exact ExecFuncBody.execBlockOK (ExecBlock.consNormal (ExecStmt.requireTrue hcv)
      (ExecBlock.consNormal hcheck (ExecBlock.consNormal (ExecStmt.letDecl hentry)
        (ExecBlock.consNormal (ExecStmt.requireTrue hactTrue)
          (ExecBlock.consNormal (ExecStmt.assign (hperm := by first | assumption | exact Or.inr ‹_› | exact Or.inl rfl) (by rw [evalExpr?]; rfl) hassignA)
            (ExecBlock.consNormal (ExecStmt.assign (hperm := Or.inr (by simpa only [storageStore_executionEnv, initState] using hperm)) hsub hassignT) ExecBlock.nil))))))
  exact rd7.reEquivExecutionGen hcode hd hdec hbody
    (by rw [storageStore_accountMap, storageStore_accountMap]; rfl)
    (returnEquiv.fallthrough rfl rfl (by native_decide))

end Tests.Pipeline.VyperRegistry
