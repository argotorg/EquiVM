import Tests.Pipeline.VyperVault.Withdraw

variable {fork : Ethereum.Fork}

/-!
# VyperVault `collectFees()`

Dispatcher bucket 9, arm entry pc 473: the guard, the reentrancy lock (set at pc 490), the owner
check against the immutable `OWNER` (pc 487), `feesCollected` read and zeroed (pc 628),
`send(OWNER, amount)` as a `CALL` at pc 656 (bridged through `callBridge`), the success check at
pc 657, the unlock and the `uint256` return at pc 662.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
  Reasoning.VyperImmutables

namespace Tests.Pipeline.VyperVault

set_option maxRecDepth 2000000

theorem collectFeesBody_eq : collectFeesTransition.body =
    [.require (.binary .eq (.env .callvalue) (.intLit 0)),
     .require (.binary .ne (.storage lockRef) (.intLit 2)),
     .assign .storage lockRef (.intLit 2),
     .internalCall "collectFees_body" [] "__r",
     .assign .storage lockRef (.intLit 3),
     .return [.var "__r"]] := by rfl

/-- The internal `collectFees_body`. -/
def collectFeesCallee : CallableDecl :=
  { params := [],
    returnType := [.elem (.int (.uint ⟨256, by decide⟩))],
    body := [.require (.binary .eq (.env .caller) (.immutable "OWNER")),
             .letDecl "amount" (some u256T) (.storage fcRef),
             .assign .storage fcRef (.intLit 0),
             .letDecl "__a0" (some (.elem .address)) (.immutable "OWNER"),
             .lowLevelCall (.var "__a0") (.var "amount") (.newBytes (.intLit 0)) "__ok1" "__data1" true,
             .require (.var "__ok1"),
             .return [.var "amount"]] }

theorem collectFeesCallee_lookup : lookupCallable? contract "collectFees_body" = some collectFeesCallee := by rfl

/-- `feesCollected` after the lock store. -/
abbrev fcL (σ : AccountMap) (I : ExecutionEnv) : UInt256 := solcSlotWordAt (UInt256.ofNat 3) (σL σ I) I
abbrev σF (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner (σL σ I) (UInt256.ofNat 3) ⟨0⟩
abbrev evmF (σ σ₀ : AccountMap) (g : Sat256) (A : Substate) (I : ExecutionEnv) : EVM.State :=
  Stele.EVM.storageStore (evmL σ σ₀ g A I) I.codeOwner (UInt256.ofNat 3) ⟨0⟩

/-- The callee's locals before and after the call. -/
abbrev cfLocals (σ : AccountMap) (I : ExecutionEnv) (a : AccountAddress) : Store :=
  ((∅ : Store).insert "amount" (uint256Value (fcL σ I))).insert "__a0" (.address a)
abbrev cfLocals' (σ : AccountMap) (I : ExecutionEnv) (a : AccountAddress) (z : Bool) (out : ByteArray) : Store :=
  ((cfLocals σ I a).insert "__ok1" (.bool z)).insert "__data1" (.bytes out)

/-- The memory at the call: `OWNER` at 0, `amount` at 64, over the 32-byte dispatcher memory. -/
abbrev mem487 (a : AccountAddress) : ByteArray :=
  (EVM.Word.ofNat a.toNat).toByteArray.write 0 (vyperVaultDispatchMem 9) 0 32
abbrev mem628 (σ : AccountMap) (I : ExecutionEnv) (a : AccountAddress) : ByteArray :=
  (EVM.Word.ofNat a.toNat).toByteArray.write 0 ((fcL σ I).toByteArray.write 0 (mem487 a) 64 32) 0 32

theorem mem487_size (a : AccountAddress) (hmemsize : (vyperVaultDispatchMem 9).size = 32) : (mem487 a).size = 32 := by
  rw [byteArray_write_size_of_inBounds _ _ _ _ (by rw [toByteArray_size]) (by omega), hmemsize]

theorem memLoad64_mem628 (σ : AccountMap) (I : ExecutionEnv) (a : AccountAddress)
    (hmemsize : (vyperVaultDispatchMem 9).size = 32) :
    memLoad (UInt256.ofNat 64) ((fcL σ I).toByteArray.write 0 (mem487 a) 64 32) = fcL σ I :=
  memLoad_write_back _ _ 64 (by decide) (by rw [mem487_size a hmemsize]; exact lt_usize _ (by decide))

theorem mem628_read64 (σ : AccountMap) (I : ExecutionEnv) (a : AccountAddress)
    (hmemsize : (vyperVaultDispatchMem 9).size = 32) :
    (mem628 σ I a).readWithPadding 64 32 = (fcL σ I).toByteArray := by
  have hin : ((fcL σ I).toByteArray.write 0 (mem487 a) 64 32).size = 96 :=
    toByteArray_write32_size_of_ge _ _ 64 32 96 (mem487_size a hmemsize) (by omega) (lt_usize _ (by decide)) rfl
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size]) (by omega) (by omega) (by rw [hin]),
    toByteArray_write_read_back_of_gap _ _ 64 (by rw [mem487_size a hmemsize]; exact lt_usize _ (by decide))]

/-- `collectFees()`: the theorem `Correct.lean` routes selector 7 to. -/
theorem vyperVaultCollectFeesBody {σ σ₀ A I} {g : UInt256} (imms : Store) (hfit : immutablesFit contract imms)
    (hwf : storageWF σ I)
    (hcode : I.code = immutableLayout.deployed vyperVaultBytecode imms) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vyperVaultSelBytes 7)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I (restrictImmutables contract imms) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (vyperVaultSelBytes 7) rfl hsel
  have hcode' : I.code = vyperVaultBytecode ++ immutableLayout.suffixWords (wordsOf imms) := by
    rw [hcode, deployed_of_fit hfit]
  obtain ⟨a, hget⟩ := owner_of_fit hfit
  obtain ⟨_, _, rd⟩ := vyperVaultReachCollectFeesBody (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) hcode' hsz hsize hsel
  have hd : dispatchMsg contract I.calldata = some collectFeesTransition :=
    vyperVaultDispatch_collectFees (selIs_exclusive (by native_decide) hsel) (selIs_exclusive (by native_decide) hsel)
      (selIs_exclusive (by native_decide) hsel) (selIs_exclusive (by native_decide) hsel)
      (selIs_exclusive (by native_decide) hsel) (selIs_exclusive (by native_decide) hsel)
      (selIs_exclusive (by native_decide) hsel) hsel
  have hdec : config.externalABI.decodeCalldata? (collectFeesTransition.params.map Param.name)
      (transitionSignature collectFeesTransition).paramTypes I.calldata = some ∅ := by
    simpa [config, contract, Syntax.contractSyntax, collectFeesTransition] using
      (decodeCalldataWithMode_empty_ok (mode := DecodeMode.vyper) (cd := I.calldata) hsz)
  have hmemsize : (vyperVaultDispatchMem 9).size = 32 := by native_decide
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · have rd1 := vyperVaultBlocks.vyperVault_block_473_taken (by simp) (fun h => hwv h)
      (by apply D_J_contains_append_left; jump_dest) rd
    have rd2 := vyperVaultBlocks.vyperVault_block_1403 (by simp) rd1
    exact RDrev.reEquivOfDispatch hcode' hd
      (fun _ => by rw [collectFeesBody_eq]; exact bodyReverts_nonPayable (by simpa [initState] using hwv)) rd2
  have rd1 := vyperVaultBlocks.vyperVault_block_473_fallthrough (by simp) (by rw [hwv]; rfl) rd
  have hcv : evalExpr? config (frame imms ∅) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (.binary .eq (.env .callvalue) (.intLit 0)) = .ok (.bool true) :=
    evalCallvalueEq_true (by simpa [initState] using hwv)
  -- the lock
  have hlockRead : evalExpr? config (frame imms ∅) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (.storage lockRef) = .ok (uint256Value (solcSlotWordAt ⟨0⟩ σ I)) := by
    rw [evalExpr_storage_vyper_uint256_backend (hbackend := rfl) (hcheck := by rfl)
        (er := { base := "nonreentrant_lock", steps := [] }) (physicalSlot := ⟨0⟩) (hbase := by simp)
        (her := by simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
        (hty := by show storageTypeAt? contract.storage _ = _; decide) (hloc := rfl),
      storageLoad_initState_ofUInt256_solcSlotWordAt]
  have hlit2 : evalExpr? config (frame imms ∅) (initState σ σ₀ (Sat256.ofUInt256 g) A I) (.intLit 2) =
      .ok (uint256Value (UInt256.ofNat 2)) := evalExpr_intLit_word _ 2 (by decide)
  by_cases hlock : solcSlotWordAt ⟨0⟩ σ I = UInt256.ofNat 2
  · obtain ⟨_, _, rd2⟩ := vyperVaultBlocks.vyperVault_block_478_taken (by simp)
      (by rw [slotWord_eq, hlock, u256_eq_refl]; decide) (by apply D_J_contains_append_left; jump_dest) rd1
    have rd3 := vyperVaultBlocks.vyperVault_block_1403 (by simp) rd2
    refine RDrev.reEquivExecutionRevert hcode' rd3 hd hdec ?_
    rw [collectFeesBody_eq]
    have h2 : (solcSlotWordAt ⟨0⟩ σ I).toNat = 2 := by rw [hlock]; rfl
    exact ExecFuncBody.execBlockRevert (ExecBlock.consNormal (ExecStmt.requireTrue hcv)
      (ExecBlock.consRevert (ExecStmt.requireFalse
        (by rw [evalExpr_ne_words hlockRead hlit2, ulit_toNat' 2 (by decide), h2]; rfl))))
  obtain ⟨_, _, rd2⟩ := vyperVaultBlocks.vyperVault_block_478_fallthrough (by simp)
    (by rw [slotWord_eq]; exact u256_eq_of_ne (fun h => hlock h.symm)) rd1
  have hne : evalExpr? config (frame imms ∅) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (.binary .ne (.storage lockRef) (.intLit 2)) = .ok (.bool true) := by
    rw [evalExpr_ne_words hlockRead hlit2, ulit_toNat' 2 (by decide),
      decide_eq_false (fun h => hlock (u256_inj (by rw [h]; rfl)))]
    rfl
  have hassignL : assignStorageRef? config (frame imms ∅) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      .storage lockRef (uint256Value (UInt256.ofNat 2)) =
      .ok (frame imms ∅, evmL σ σ₀ (Sat256.ofUInt256 g) A I) := by
    apply assignStorageRef_storage_vyper_scalar (hbackend := rfl) (hcheck := by rfl)
      (er := { base := "nonreentrant_lock", steps := [] })
      (hleaf := Or.inl ⟨_, rfl⟩) (ty := .elem (.int (.uint ⟨256, by decide⟩))) (loc := vyperUint256Loc ⟨0⟩)
      (hbase := by simp) (her := by simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
      (hty := by show storageTypeAt? contract.storage _ = _; decide) (hloc := rfl)
    erw [storageLocStore_uint256]
    rfl
  by_cases hperm : I.perm = true
  swap
  · -- static mode: the lock store (pc 490) halts
    have hpf : I.perm = false := by simpa using hperm
    have r1 := rd2.push1 (UInt256.ofNat 2)
      (by append_decode(vyperVaultBytecode, (immutableLayout.suffixWords (wordsOf imms)), (⟨487⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 2), 1)))
      (by evm_ov)
    have r2 := r1.push0
      (by append_decode(vyperVaultBytecode, (immutableLayout.suffixWords (wordsOf imms)), (⟨489⟩ : UInt256), .PUSH0, none))
      (by evm_ov)
    have rs := r2.sstoreStatic hpf
      (by append_decode(vyperVaultBytecode, (immutableLayout.suffixWords (wordsOf imms)), (⟨490⟩ : UInt256), .SSTORE, none))
      (by evm_ov)
    refine RDstatic.reEquivStaticHalt hcode' rs hd hdec ?_
    rw [collectFeesBody_eq]
    exact ExecFuncBody.execBlockStatic (ExecBlock.consNormal (ExecStmt.requireTrue hcv)
      (ExecBlock.consNormal (ExecStmt.requireTrue hne)
        (ExecBlock.consStatic (ExecStmt.assignStatic hlit2 hassignL (by show I.perm = false; exact hpf)))))
  -- the owner check (pc 487), after the lock store
  have hargs : ∀ evm, evalExprs? config (frame imms ∅) evm [] = .ok [] := fun _ => rfl
  have hcaller : evalExpr? config (frame imms ∅) (evmL σ σ₀ (Sat256.ofUInt256 g) A I)
      (.binary .eq (.env .caller) (.immutable "OWNER")) = .ok (.bool (decide (I.source = a))) := by
    rw [evalCallerEqOwner' hget ∅ _, storageStore_executionEnv]
    rfl
  by_cases hown : I.source = a
  swap
  · -- not the owner: the callee's `assert` reverts
    obtain ⟨_, _, rd3⟩ := vyperVaultBlocks.vyperVault_block_487_fallthrough (immWords := wordsOf imms) (by simp) hperm
      (by rw [wordsOf_OWNER hget]; exact isZero_xor_eq_zero_of_ne (fun h => hown (ofNat_addr_inj h))) rd2
    have rd4 := vyperVaultBlocks.vyperVault_block_507 (by simp) rd3
    have rd5 := vyperVaultBlocks.vyperVault_block_622 (by simp) rd4
    refine RDrev.reEquivExecutionRevert hcode' rd5 hd hdec ?_
    rw [collectFeesBody_eq]
    rw [decide_eq_false hown] at hcaller
    exact ExecFuncBody.execBlockRevert (ExecBlock.consNormal (ExecStmt.requireTrue hcv)
      (ExecBlock.consNormal (ExecStmt.requireTrue hne)
        (ExecBlock.consNormal (ExecStmt.assign (hperm := Or.inr (by simpa only [storageStore_executionEnv, initState] using hperm)) hlit2 hassignL)
          (ExecBlock.consRevert (ExecStmt.internalCallRevert (callee := collectFeesCallee) (hargs _)
            collectFeesCallee_lookup rfl
            (ExecFuncBody.execBlockRevert (ExecBlock.consRevert (ExecStmt.requireFalse hcaller))))))))
  rw [decide_eq_true hown] at hcaller
  obtain ⟨_, _, rd3⟩ := vyperVaultBlocks.vyperVault_block_487_taken (immWords := wordsOf imms) (by simp) hperm
    (by rw [wordsOf_OWNER hget]; exact isZero_xor_ne_zero_of_eq (by rw [hown]; rfl))
    (by apply D_J_contains_append_left; jump_dest) rd2
  simp only [vyperVaultBlocks.vyperVault_block_487_taken_memory, show (⟨0⟩ : UInt256).toNat = 0 from rfl] at rd3
  rw [wordsOf_OWNER hget] at rd3
  -- pc 628: read and zero `feesCollected`, set up the call
  obtain ⟨_, _, rd4⟩ := vyperVaultBlocks.vyperVault_block_628 (immWords := wordsOf imms) (by simp) hperm rd3
  simp only [vyperVaultBlocks.vyperVault_block_628_stack, vyperVaultBlocks.vyperVault_block_628_memory,
    ulit_toNat' 64 (by decide), show (⟨0⟩ : UInt256).toNat = 0 from rfl] at rd4
  rw [wordsOf_OWNER hget, slotWord_eq, memLoad64_mem628 σ I a hmemsize] at rd4
  -- Stele: the callee's `let`s and the store
  have hfcRead : evalExpr? config (frame imms ∅) (evmL σ σ₀ (Sat256.ofUInt256 g) A I) (.storage fcRef) =
      .ok (uint256Value (fcL σ I)) := by
    rw [evalExpr_storage_vyper_uint256_backend (hbackend := rfl) (hcheck := by rfl)
        (er := { base := "feesCollected", steps := [] }) (physicalSlot := UInt256.ofNat 3) (hbase := by simp)
        (her := by simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
        (hty := by show storageTypeAt? contract.storage _ = _; decide) (hloc := rfl),
      storageLoad_eq_slotWord, storageStore_executionEnv, storageStore_accountMap]
    rfl
  have hlit0 : evalExpr? config (frame imms ((∅ : Store).insert "amount" (uint256Value (fcL σ I))))
      (evmL σ σ₀ (Sat256.ofUInt256 g) A I) (.intLit 0) = .ok (uint256Value ⟨0⟩) := evalExpr_intLit_word _ 0 (by decide)
  have hassignF : assignStorageRef? config (frame imms ((∅ : Store).insert "amount" (uint256Value (fcL σ I))))
      (evmL σ σ₀ (Sat256.ofUInt256 g) A I) .storage fcRef (uint256Value ⟨0⟩) =
      .ok (frame imms ((∅ : Store).insert "amount" (uint256Value (fcL σ I))), evmF σ σ₀ (Sat256.ofUInt256 g) A I) := by
    apply assignStorageRef_storage_vyper_scalar (hbackend := rfl) (hcheck := by rfl)
      (er := { base := "feesCollected", steps := [] })
      (hleaf := Or.inl ⟨_, rfl⟩) (ty := .elem (.int (.uint ⟨256, by decide⟩))) (loc := vyperUint256Loc (UInt256.ofNat 3))
      (hbase := by simp) (her := by simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
      (hty := by show storageTypeAt? contract.storage _ = _; decide) (hloc := rfl)
    erw [storageLocStore_uint256, storageStore_executionEnv]
    rfl
  have ha0 : evalExpr? config (frame imms ((∅ : Store).insert "amount" (uint256Value (fcL σ I))))
      (evmF σ σ₀ (Sat256.ofUInt256 g) A I) (.immutable "OWNER") = .ok (.address a) := evalImmutable_OWNER hget _ _
  -- the `CALL` (pc 656)
  have hs : SourceState (initState σ σ₀ (Sat256.ofUInt256 g) A I) I (σF σ I) (evmF σ σ₀ (Sat256.ofUInt256 g) A I) :=
    (SourceState.init.storageWrite ⟨0⟩ (UInt256.ofNat 2)).storageWrite (UInt256.ofNat 3) ⟨0⟩
  obtain ⟨evm', σ', z, out, _, _, hcall, hs', rd5, _⟩ := callBridge rd4 hs hperm
    (by append_decode(vyperVaultBytecode, (immutableLayout.suffixWords (wordsOf imms)), (⟨656⟩ : UInt256), .CALL, none))
    (show (mem628 σ I a).readWithPadding 0 0 = ByteArray.empty from byteArray_readWithPadding_zero _ _)
    (by show ByteArray.empty.size ≤ _; exact Nat.zero_le _) (by simp)
  have rd6 := RD.normalizePC (pc' := UInt256.ofNat 657) rd5 (by native_decide)
  have hamt : ∀ evm, evalExpr? config (frame imms (cfLocals σ I a)) evm (.var "amount") =
      .ok (uint256Value (fcL σ I)) := fun evm =>
    evalVar imms _ _ "amount" _ (by rw [store_get_ne _ _ (by decide), store_get_self])
  have hcallStmt : ExecStmt fork config (frame imms (cfLocals σ I a)) (evmF σ σ₀ (Sat256.ofUInt256 g) A I)
      (.lowLevelCall (.var "__a0") (.var "amount") (.newBytes (.intLit 0)) "__ok1" "__data1" true)
      (.ok { frame imms (cfLocals σ I a) with locals := cfLocals' σ I a z out } evm') :=
    lowLevelCallSource (hperm := Or.inr (by simpa only [hs.env] using hperm))
      (by
        rw [evalVar imms _ _ "__a0" _ (store_get_self _ _ _)]
        show EvalResult.ok (Value.address a) = EvalResult.ok (Value.address (AccountAddress.ofUInt256 (UInt256.ofNat a.val)))
        rw [accountAddress_roundtrip])
      (hamt _) (evalExpr_newBytes_zero _) hcall
  cases z with
  | false =>
    have rd7 := vyperVaultBlocks.vyperVault_block_657_taken (by simp) (by decide)
      (by apply D_J_contains_append_left; jump_dest) rd6
    have rd8 := vyperVaultBlocks.vyperVault_block_1403 (by simp [vyperVaultBlocks.vyperVault_block_657_taken_stack]) rd7
    refine RDrev.reEquivExecutionRevert hcode' rd8 hd hdec ?_
    rw [collectFeesBody_eq]
    exact ExecFuncBody.execBlockRevert (ExecBlock.consNormal (ExecStmt.requireTrue hcv)
      (ExecBlock.consNormal (ExecStmt.requireTrue hne)
        (ExecBlock.consNormal (ExecStmt.assign (hperm := Or.inr (by simpa only [storageStore_executionEnv, initState] using hperm)) hlit2 hassignL)
          (ExecBlock.consRevert (ExecStmt.internalCallRevert (callee := collectFeesCallee) (hargs _)
            collectFeesCallee_lookup rfl
            (ExecFuncBody.execBlockRevert (ExecBlock.consNormal (ExecStmt.requireTrue hcaller)
              (ExecBlock.consNormal (ExecStmt.letDecl hfcRead)
                (ExecBlock.consNormal (ExecStmt.assign (hperm := Or.inr (by simpa only [storageStore_executionEnv, initState] using hperm)) hlit0 hassignF)
                  (ExecBlock.consNormal (ExecStmt.letDecl ha0)
                    (ExecBlock.consNormal hcallStmt
                      (ExecBlock.consRevert (ExecStmt.requireFalse
                        (evalVar imms _ _ "__ok1" _ (by rw [store_get_ne _ _ (by decide), store_get_self])))))))))))))))
  | true =>
    have rd7 := vyperVaultBlocks.vyperVault_block_657_fallthrough (by simp) (by decide) rd6
    simp only [vyperVaultBlocks.vyperVault_block_657_fallthrough_stack] at rd7
    have rd8 := vyperVaultBlocks.vyperVault_block_662 (by simp) hperm rd7
    rw [callOutputMem_zero, ulit_toNat' 64 (by decide), ulit_toNat' 32 (by decide), mem628_read64 σ I a hmemsize] at rd8
    have hok : evalExpr? config (frame imms (cfLocals' σ I a true out)) evm' (.var "__ok1") = .ok (.bool true) :=
      evalVar imms _ _ "__ok1" _ (by rw [store_get_ne _ _ (by decide), store_get_self])
    have hret : evalExpr? config (frame imms (cfLocals' σ I a true out)) evm' (.var "amount") =
        .ok (uint256Value (fcL σ I)) :=
      evalVar imms _ _ "amount" _ (by
        rw [store_get_ne2 _ _ _ (by decide) (by decide), store_get_ne _ _ (by decide), store_get_self])
    have hlit3 : evalExpr? config (frame imms ((∅ : Store).insert "__r" (uint256Value (fcL σ I)))) evm' (.intLit 3) =
        .ok (uint256Value (UInt256.ofNat 3)) := evalExpr_intLit_word _ 3 (by decide)
    have hassign3 : assignStorageRef? config (frame imms ((∅ : Store).insert "__r" (uint256Value (fcL σ I)))) evm'
        .storage lockRef (uint256Value (UInt256.ofNat 3)) =
        .ok (frame imms ((∅ : Store).insert "__r" (uint256Value (fcL σ I))),
          Stele.EVM.storageStore evm' I.codeOwner ⟨0⟩ (UInt256.ofNat 3)) := by
      apply assignStorageRef_storage_vyper_scalar (hbackend := rfl) (hcheck := by rfl)
        (er := { base := "nonreentrant_lock", steps := [] })
        (hleaf := Or.inl ⟨_, rfl⟩) (ty := .elem (.int (.uint ⟨256, by decide⟩))) (loc := vyperUint256Loc ⟨0⟩)
        (hbase := by simp) (her := by simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
        (hty := by show storageTypeAt? contract.storage _ = _; decide) (hloc := rfl)
      erw [storageLocStore_uint256, hs'.env]
    have hbody : ExecTransitionBody fork config contract (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅
        collectFeesTransition.body
        (.returned (frame imms ((∅ : Store).insert "__r" (uint256Value (fcL σ I))))
          (Stele.EVM.storageStore evm' I.codeOwner ⟨0⟩ (UInt256.ofNat 3)) (some [uint256Value (fcL σ I)]))
        (restrictImmutables contract imms) := by
      rw [collectFeesBody_eq]
      exact ExecFuncBody.execBlockRet (ExecBlock.consNormal (ExecStmt.requireTrue hcv)
        (ExecBlock.consNormal (ExecStmt.requireTrue hne)
          (ExecBlock.consNormal (ExecStmt.assign (hperm := Or.inr (by simpa only [storageStore_executionEnv, initState] using hperm)) hlit2 hassignL)
            (ExecBlock.consNormal (ExecStmt.internalCallReturn (callee := collectFeesCallee) (hargs _)
              collectFeesCallee_lookup rfl
              (ExecFuncBody.execBlockRet (ExecBlock.consNormal (ExecStmt.requireTrue hcaller)
                (ExecBlock.consNormal (ExecStmt.letDecl hfcRead)
                  (ExecBlock.consNormal (ExecStmt.assign (hperm := Or.inr (by simpa only [storageStore_executionEnv, initState] using hperm)) hlit0 hassignF)
                    (ExecBlock.consNormal (ExecStmt.letDecl ha0)
                      (ExecBlock.consNormal hcallStmt
                        (ExecBlock.consNormal (ExecStmt.requireTrue hok)
                          (ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton hret)))))))))))
              (ExecBlock.consNormal (ExecStmt.assign (hperm := Or.inr (by simpa only [hs'.env] using hperm)) hlit3 hassign3)
                (ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton
                  (evalVar imms _ _ "__r" _ (store_get_self _ _ _))))))))))
    exact rd8.reEquivExecutionGen hcode' hd hdec hbody ((hs'.storageWrite ⟨0⟩ (UInt256.ofNat 3)).accounts)
      (returnEquiv_of_encode (uint256ReturnEncoding _))

end Tests.Pipeline.VyperVault
