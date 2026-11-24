import Tests.Pipeline.VyperVault.Deposit
import Reasoning.ExternalCall

variable {fork : Ethereum.Fork}

/-!
# VyperVault `withdraw(uint256)`

Dispatcher bucket 3, arm entry pc 683: the guard, the reentrancy lock (slot 0: `2` while locked,
set at pc 705), `balances[msg.sender] >= amount` (pc 702), the two checked subtractions
(pc 849/877), `send(msg.sender, amount)` as a `CALL` with no data at pc 916 (bridged through
`callBridge` to Stele's `callViaEVM`), the success check at pc 917 and the unlock at pc 922.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
  Reasoning.VyperImmutables

namespace Tests.Pipeline.VyperVault

set_option maxRecDepth 2000000

abbrev lockRef : StorageRef := { base := "nonreentrant_lock", steps := [] }

theorem withdrawBody_eq : withdrawTransition.body =
    [.require (.binary .eq (.env .callvalue) (.intLit 0)),
     .require (.binary .ne (.storage lockRef) (.intLit 2)),
     .assign .storage lockRef (.intLit 2),
     .internalCall "withdraw_body" [.var "amount"] "__r",
     .assign .storage lockRef (.intLit 3)] := by rfl

/-- The internal `withdraw_body`. -/
def withdrawCallee : CallableDecl :=
  { params := [{ name := "amount", ty := .elem (.int (.uint ⟨256, by decide⟩)) }],
    returnType := [],
    body := [.require (.binary .ge (.storage balRef) (.var "amount")),
             .assign .storage balRef (.inRange (.uint ⟨256, by decide⟩) (.binary .sub (.storage balRef) (.var "amount"))),
             .assign .storage tdRef (.inRange (.uint ⟨256, by decide⟩) (.binary .sub (.storage tdRef) (.var "amount"))),
             .lowLevelCall (.env .caller) (.var "amount") (.newBytes (.intLit 0)) "__ok0" "__data0" true,
             .require (.var "__ok0"),
             .emit "Withdrawn" [.env .caller, .var "amount"]] }

theorem withdrawCallee_lookup : lookupCallable? contract "withdraw_body" = some withdrawCallee := by rfl

/-- The decoded argument store (also the callee's locals). -/
abbrev wStore (I : ExecutionEnv) : Store := (∅ : Store).insert "amount" (uint256Value (argWord I))

theorem decodeMode_uint256_ok (cd : ByteArray) (hsz36 : 36 ≤ cd.size) :
    decodeCalldataWithMode DecodeMode.vyper ["amount"] [abiUInt256] cd =
      some ((∅ : Store).insert "amount" (uint256Value (calldataWord cd 4))) := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  rw [decodeCalldataWithMode_vyperScalarWords_eq (by decide), if_neg (by rw [htlen]; omega),
    decodeScalarWords_uint256_ok htake4]
  simp [decodeCalldata.insertValues, hword4] <;> rfl

theorem decodeMode_uint256_none_short (cd : ByteArray) (hsz : 4 ≤ cd.size) (hshort : cd.size < 36) :
    decodeCalldataWithMode DecodeMode.vyper ["amount"] [abiUInt256] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  rw [decodeCalldataWithMode_vyperScalarWords_eq (by decide), if_neg (by rw [htlen]; omega),
    decodeScalarWords_uint256_none_short (by rw [List.length_drop, htlen]; omega)]

theorem withdrawDecode_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    config.externalABI.decodeCalldata? (withdrawTransition.params.map Param.name)
      (transitionSignature withdrawTransition).paramTypes I.calldata = some (wStore I) := by
  simpa [config, contract, Syntax.contractSyntax, withdrawTransition, wStore, argWord_eq] using
    decodeMode_uint256_ok I.calldata hsz36

theorem withdrawDecode_short {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    config.externalABI.decodeCalldata? (withdrawTransition.params.map Param.name)
      (transitionSignature withdrawTransition).paramTypes I.calldata = none := by
  simpa [config, contract, Syntax.contractSyntax, withdrawTransition] using
    decodeMode_uint256_none_short I.calldata hsz hshort

/-! ### Account maps and EVM states along the path -/

abbrev σL (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ ⟨0⟩ (UInt256.ofNat 2)
abbrev balL (σ : AccountMap) (I : ExecutionEnv) : UInt256 := solcSlotWordAt (balSlot I) (σL σ I) I
abbrev σB (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner (σL σ I) (balSlot I) (UInt256.sub (balL σ I) (argWord I))
abbrev tdB (σ : AccountMap) (I : ExecutionEnv) : UInt256 := solcSlotWordAt (UInt256.ofNat 2) (σB σ I) I
abbrev σT (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner (σB σ I) (UInt256.ofNat 2) (UInt256.sub (tdB σ I) (argWord I))

abbrev evmL (σ σ₀ : AccountMap) (g : Sat256) (A : Substate) (I : ExecutionEnv) : EVM.State :=
  Stele.EVM.storageStore (initState σ σ₀ g A I) I.codeOwner ⟨0⟩ (UInt256.ofNat 2)
abbrev evmB (σ σ₀ : AccountMap) (g : Sat256) (A : Substate) (I : ExecutionEnv) : EVM.State :=
  Stele.EVM.storageStore (evmL σ σ₀ g A I) I.codeOwner (balSlot I) (UInt256.sub (balL σ I) (argWord I))
abbrev evmT (σ σ₀ : AccountMap) (g : Sat256) (A : Substate) (I : ExecutionEnv) : EVM.State :=
  Stele.EVM.storageStore (evmB σ σ₀ g A I) I.codeOwner (UInt256.ofNat 2) (UInt256.sub (tdB σ I) (argWord I))

/-- The hash scratch memory (`1 ++ caller`) built over the 32-byte dispatcher memory, and again
    over itself. -/
abbrev hashMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat I.source.val).toByteArray.write 0 (vyperVaultDispatchMem 3) 32 32) 0 32
abbrev hashMem2 (I : ExecutionEnv) : ByteArray :=
  (UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat I.source.val).toByteArray.write 0 (hashMem I) 32 32) 0 32

theorem hashMem_size (I : ExecutionEnv) (hmemsize : (vyperVaultDispatchMem 3).size = 32) : (hashMem I).size = 64 := by
  have h1 : ((UInt256.ofNat I.source.val).toByteArray.write 0 (vyperVaultDispatchMem 3) 32 32).size = 64 :=
    toByteArray_write32_size_of_ge _ _ 32 32 64 hmemsize (by omega) (lt_usize _ (by decide)) rfl
  rw [byteArray_write_size_of_inBounds _ _ _ _ (by rw [toByteArray_size]) (by rw [h1]; omega), h1]

theorem keccak_hashMem (I : ExecutionEnv) (hmemsize : (vyperVaultDispatchMem 3).size = 32) :
    keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) (hashMem I) = balSlot I := by
  have h := keccakWord_hash32 (UInt256.ofNat 1) (.address I.source) (vyperVaultDispatchMem 3) hmemsize
  rw [Reasoning.Theory.keyValueToWord_address] at h
  exact h

theorem keccak_hashMem2 (I : ExecutionEnv) (hmemsize : (vyperVaultDispatchMem 3).size = 32) :
    keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) (hashMem2 I) = balSlot I := by
  unfold keccakWord
  rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl, ulit_toNat' 64 (by decide)]
  have h := wordAt0Mem_wordAt32Mem_vyperMappingSlot (UInt256.ofNat 1) (.address I.source)
    (mem := hashMem I) (by rw [hashMem_size I hmemsize])
  rw [Reasoning.Theory.keyValueToWord_address] at h
  exact h

/-- `withdraw(uint256)`: the theorem `Correct.lean` routes selector 3 to. -/
theorem vyperVaultWithdrawBody {σ σ₀ A I} {g : UInt256} (imms : Store) (hfit : immutablesFit contract imms)
    (hwf : storageWF σ I)
    (hcode : I.code = immutableLayout.deployed vyperVaultBytecode imms) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vyperVaultSelBytes 3)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I (restrictImmutables contract imms) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (vyperVaultSelBytes 3) rfl hsel
  have hcode' : I.code = vyperVaultBytecode ++ immutableLayout.suffixWords (wordsOf imms) := by
    rw [hcode, deployed_of_fit hfit]
  obtain ⟨_, _, rd⟩ := vyperVaultReachWithdrawBody (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) hcode' hsz hsize hsel
  have hd : dispatchMsg contract I.calldata = some withdrawTransition :=
    vyperVaultDispatch_withdraw (selIs_exclusive (by native_decide) hsel) (selIs_exclusive (by native_decide) hsel)
      (selIs_exclusive (by native_decide) hsel) hsel
  have hmemsize : (vyperVaultDispatchMem 3).size = 32 := by native_decide
  by_cases hshort : I.calldata.size < 36
  · have rd1 := vyperVaultBlocks.vyperVault_block_683_taken (by simp) (guard_short hsize hshort)
      (by apply D_J_contains_append_left; jump_dest) rd
    have rd2 := vyperVaultBlocks.vyperVault_block_1403 (by simp) rd1
    exact RDrev.reEquivDecodingFailed hcode' rd2 hd (withdrawDecode_short hsz hshort)
  have hsz36 : 36 ≤ I.calldata.size := by omega
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · have rd1 := vyperVaultBlocks.vyperVault_block_683_taken (by simp) (guard_wv hwv)
      (by apply D_J_contains_append_left; jump_dest) rd
    have rd2 := vyperVaultBlocks.vyperVault_block_1403 (by simp) rd1
    exact RDrev.reEquivOfDispatch hcode' hd
      (fun _ => by rw [withdrawBody_eq]; exact bodyReverts_nonPayable (by simpa [initState] using hwv)) rd2
  have rd1 := vyperVaultBlocks.vyperVault_block_683_fallthrough (by simp) (guard_ok hwv hsz36 hsize) rd
  have hdec := withdrawDecode_ok (I := I) hsz36
  have hcv : evalExpr? config (frame imms (wStore I)) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (.binary .eq (.env .callvalue) (.intLit 0)) = .ok (.bool true) :=
    evalCallvalueEq_true (by simpa [initState] using hwv)
  -- the lock
  have hlockRead : evalExpr? config (frame imms (wStore I)) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (.storage lockRef) = .ok (uint256Value (solcSlotWordAt ⟨0⟩ σ I)) := by
    rw [evalExpr_storage_vyper_uint256_backend (hbackend := rfl) (hcheck := by rfl)
        (er := { base := "nonreentrant_lock", steps := [] }) (physicalSlot := ⟨0⟩) (hbase := by simp)
        (her := by simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
        (hty := by show storageTypeAt? contract.storage _ = _; decide) (hloc := rfl),
      storageLoad_initState_ofUInt256_solcSlotWordAt]
  have hlit2 : evalExpr? config (frame imms (wStore I)) (initState σ σ₀ (Sat256.ofUInt256 g) A I) (.intLit 2) =
      .ok (uint256Value (UInt256.ofNat 2)) := evalExpr_intLit_word _ 2 (by decide)
  by_cases hlock : solcSlotWordAt ⟨0⟩ σ I = UInt256.ofNat 2
  · -- locked: the guard reverts
    obtain ⟨_, _, rd2⟩ := vyperVaultBlocks.vyperVault_block_693_taken (by simp)
      (by rw [slotWord_eq, hlock, u256_eq_refl]; decide) (by apply D_J_contains_append_left; jump_dest) rd1
    have rd3 := vyperVaultBlocks.vyperVault_block_1403 (by simp) rd2
    refine RDrev.reEquivExecutionRevert hcode' rd3 hd hdec ?_
    rw [withdrawBody_eq]
    have h2 : (solcSlotWordAt ⟨0⟩ σ I).toNat = 2 := by rw [hlock]; rfl
    exact ExecFuncBody.execBlockRevert (ExecBlock.consNormal (ExecStmt.requireTrue hcv)
      (ExecBlock.consRevert (ExecStmt.requireFalse
        (by rw [evalExpr_ne_words hlockRead hlit2, ulit_toNat' 2 (by decide), h2]; rfl))))
  obtain ⟨_, _, rd2⟩ := vyperVaultBlocks.vyperVault_block_693_fallthrough (by simp)
    (by rw [slotWord_eq]; exact u256_eq_of_ne (fun h => hlock h.symm)) rd1
  have hne : evalExpr? config (frame imms (wStore I)) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (.binary .ne (.storage lockRef) (.intLit 2)) = .ok (.bool true) := by
    rw [evalExpr_ne_words hlockRead hlit2, ulit_toNat' 2 (by decide),
      decide_eq_false (fun h => hlock (u256_inj (by rw [h]; rfl)))]
    rfl
  have hassignL : assignStorageRef? config (frame imms (wStore I)) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      .storage lockRef (uint256Value (UInt256.ofNat 2)) =
      .ok (frame imms (wStore I), evmL σ σ₀ (Sat256.ofUInt256 g) A I) := by
    apply assignStorageRef_storage_vyper_scalar (hbackend := rfl) (hcheck := by rfl)
      (er := { base := "nonreentrant_lock", steps := [] })
      (hleaf := Or.inl ⟨_, rfl⟩) (ty := .elem (.int (.uint ⟨256, by decide⟩))) (loc := vyperUint256Loc ⟨0⟩)
      (hbase := by simp) (her := by simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
      (hty := by show storageTypeAt? contract.storage _ = _; decide) (hloc := rfl)
    erw [storageLocStore_uint256]
    rfl
  by_cases hperm : I.perm = true
  swap
  · -- static mode: the lock store (pc 705) halts
    have hpf : I.perm = false := by simpa using hperm
    have r1 := rd2.push1 (UInt256.ofNat 2)
      (by append_decode(vyperVaultBytecode, (immutableLayout.suffixWords (wordsOf imms)), (⟨702⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 2), 1)))
      (by evm_ov)
    have r2 := r1.push0
      (by append_decode(vyperVaultBytecode, (immutableLayout.suffixWords (wordsOf imms)), (⟨704⟩ : UInt256), .PUSH0, none))
      (by evm_ov)
    have rs := r2.sstoreStatic hpf
      (by append_decode(vyperVaultBytecode, (immutableLayout.suffixWords (wordsOf imms)), (⟨705⟩ : UInt256), .SSTORE, none))
      (by evm_ov)
    refine RDstatic.reEquivStaticHalt hcode' rs hd hdec ?_
    rw [withdrawBody_eq]
    exact ExecFuncBody.execBlockStatic (ExecBlock.consNormal (ExecStmt.requireTrue hcv)
      (ExecBlock.consNormal (ExecStmt.requireTrue hne)
        (ExecBlock.consStatic (ExecStmt.assignStatic hlit2 hassignL (by show I.perm = false; exact hpf)))))
  -- pc 702: lock := 2, hash the caller, check the balance
  have hkec := keccak_hashMem I hmemsize
  have hkec2 := keccak_hashMem2 I hmemsize
  have hargs : ∀ evm, evalExprs? config (frame imms (wStore I)) evm [.var "amount"] =
      .ok [uint256Value (argWord I)] := fun evm => by
    rw [evalExprs?, evalVar imms _ _ "amount" _ (store_get_self _ _ _), evalExprs?]
    rfl
  have hamt : ∀ evm, evalExpr? config (frame imms (wStore I)) evm (.var "amount") = .ok (uint256Value (argWord I)) :=
    fun evm => evalVar imms _ _ "amount" _ (store_get_self _ _ _)
  have hbalRead : evalExpr? config (frame imms (wStore I)) (evmL σ σ₀ (Sat256.ofUInt256 g) A I) (.storage balRef) =
      .ok (uint256Value (balL σ I)) := by
    rw [evalExpr_storage_vyper_uint256_backend (hbackend := rfl) (hcheck := by rfl)
        (er := { base := "balances", steps := [.mindex (.address I.source)] })
        (physicalSlot := balSlot I) (hbase := by simp)
        (her := by simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, valueToKey?,
          EvalResult.seqList, EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?, envValue,
          storageStore_executionEnv, initState])
        (hty := by simp [storageTypeAt?, storageTypeStep?, contract, Syntax.contractSyntax])
        (hloc := rfl),
      storageLoad_eq_slotWord, storageStore_executionEnv, storageStore_accountMap]
    rfl
  by_cases hge : (argWord I).toNat ≤ (balL σ I).toNat
  swap
  · -- insufficient balance: `assert` reverts after the lock store
    obtain ⟨_, _, rd3⟩ := vyperVaultBlocks.vyperVault_block_702_fallthrough (by simp) hperm
      (by
        simp only [ulit_toNat' 32 (by decide), show (⟨0⟩ : UInt256).toNat = 0 from rfl]
        rw [hkec, slotWord_eq, ult_one (by show (balL σ I).toNat < (argWord I).toNat; omega)]
        decide) rd2
    have rd4 := vyperVaultBlocks.vyperVault_block_728 (by simp) rd3
    have rd5 := vyperVaultBlocks.vyperVault_block_843 (by simp) rd4
    refine RDrev.reEquivExecutionRevert hcode' rd5 hd hdec ?_
    rw [withdrawBody_eq]
    exact ExecFuncBody.execBlockRevert (ExecBlock.consNormal (ExecStmt.requireTrue hcv)
      (ExecBlock.consNormal (ExecStmt.requireTrue hne)
        (ExecBlock.consNormal (ExecStmt.assign (hperm := Or.inr (by simpa only [storageStore_executionEnv, initState] using hperm)) hlit2 hassignL)
          (ExecBlock.consRevert (ExecStmt.internalCallRevert (callee := withdrawCallee) (hargs _) withdrawCallee_lookup rfl
            (ExecFuncBody.execBlockRevert (ExecBlock.consRevert (ExecStmt.requireFalse
              (by rw [evalExpr_ge_words hbalRead (hamt _), decide_eq_false hge])))))))))
  obtain ⟨_, _, rd3⟩ := vyperVaultBlocks.vyperVault_block_702_taken (by simp) hperm
    (by
      simp only [ulit_toNat' 32 (by decide), show (⟨0⟩ : UInt256).toNat = 0 from rfl]
      rw [hkec, slotWord_eq, ult_zero hge]
      decide)
    (by apply D_J_contains_append_left; jump_dest) rd2
  simp only [vyperVaultBlocks.vyperVault_block_702_taken_memory, ulit_toNat' 32 (by decide),
    show (⟨0⟩ : UInt256).toNat = 0 from rfl] at rd3
  -- Stele: the callee's `require` and first assignment
  have hgeTrue : evalExpr? config (frame imms (wStore I)) (evmL σ σ₀ (Sat256.ofUInt256 g) A I)
      (.binary .ge (.storage balRef) (.var "amount")) = .ok (.bool true) := by
    rw [evalExpr_ge_words hbalRead (hamt _), decide_eq_true hge]
  have hsub1 := evalExpr_uint256_sub hbalRead (hamt _) hge
  have hassignB : assignStorageRef? config (frame imms (wStore I)) (evmL σ σ₀ (Sat256.ofUInt256 g) A I)
      .storage balRef (uint256Value (UInt256.sub (balL σ I) (argWord I))) =
      .ok (frame imms (wStore I), evmB σ σ₀ (Sat256.ofUInt256 g) A I) := by
    apply assignStorageRef_storage_vyper_scalar (hbackend := rfl) (hcheck := by rfl)
      (er := { base := "balances", steps := [.mindex (.address I.source)] })
      (hleaf := Or.inl ⟨_, rfl⟩) (ty := .elem (.int (.uint ⟨256, by decide⟩))) (loc := vyperUint256Loc (balSlot I))
      (hbase := by simp)
      (her := by simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, valueToKey?,
        EvalResult.seqList, EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?, envValue,
        storageStore_executionEnv, initState])
      (hty := by simp [storageTypeAt?, storageTypeStep?, contract, Syntax.contractSyntax]) (hloc := rfl)
    erw [storageLocStore_uint256, storageStore_executionEnv]
    rfl
  have htdRead : evalExpr? config (frame imms (wStore I)) (evmB σ σ₀ (Sat256.ofUInt256 g) A I) (.storage tdRef) =
      .ok (uint256Value (tdB σ I)) := by
    rw [evalExpr_storage_vyper_uint256_backend (hbackend := rfl) (hcheck := by rfl)
        (er := { base := "totalDeposits", steps := [] }) (physicalSlot := UInt256.ofNat 2) (hbase := by simp)
        (her := by simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
        (hty := by show storageTypeAt? contract.storage _ = _; decide) (hloc := rfl),
      storageLoad_eq_slotWord, storageStore_executionEnv, storageStore_executionEnv,
      storageStore_accountMap, storageStore_accountMap]
    rfl
  -- pc 849: the balance subtraction never underflows
  obtain ⟨_, _, rd4⟩ := vyperVaultBlocks.vyperVault_block_849_fallthrough (by simp)
    (by
      simp only [ulit_toNat' 32 (by decide), show (⟨0⟩ : UInt256).toNat = 0 from rfl]
      rw [hkec2, slotWord_eq]
      exact ugt_zero (by
        show (UInt256.sub (balL σ I) (argWord I)).toNat ≤ (balL σ I).toNat
        rw [usub_toNat hge]; omega)) rd3
  simp only [vyperVaultBlocks.vyperVault_block_849_fallthrough_stack,
    vyperVaultBlocks.vyperVault_block_849_fallthrough_memory,
    ulit_toNat' 32 (by decide), show (⟨0⟩ : UInt256).toNat = 0 from rfl] at rd4
  rw [hkec2, slotWord_eq] at rd4
  -- pc 877: store the balance, read `totalDeposits`, check the subtraction
  have hamtlt : (argWord I).toNat < UInt256.size := (argWord I).val.isLt
  by_cases htd : (argWord I).toNat ≤ (tdB σ I).toNat
  swap
  · obtain ⟨_, _, rd5⟩ := vyperVaultBlocks.vyperVault_block_877_taken (by simp) hperm
      (by
        rw [slotWord_eq]
        rw [ugt_one (by
          show (tdB σ I).toNat < (UInt256.sub (tdB σ I) (argWord I)).toNat
          rw [usub_toNat_underflow (by omega)]; omega)]
        decide)
      (by apply D_J_contains_append_left; jump_dest) rd4
    have rd6 := vyperVaultBlocks.vyperVault_block_1403 (by simp [vyperVaultBlocks.vyperVault_block_877_taken_stack]) rd5
    refine RDrev.reEquivExecutionRevert hcode' rd6 hd hdec ?_
    rw [withdrawBody_eq]
    exact ExecFuncBody.execBlockRevert (ExecBlock.consNormal (ExecStmt.requireTrue hcv)
      (ExecBlock.consNormal (ExecStmt.requireTrue hne)
        (ExecBlock.consNormal (ExecStmt.assign (hperm := Or.inr (by simpa only [storageStore_executionEnv, initState] using hperm)) hlit2 hassignL)
          (ExecBlock.consRevert (ExecStmt.internalCallRevert (callee := withdrawCallee) (hargs _) withdrawCallee_lookup rfl
            (ExecFuncBody.execBlockRevert (ExecBlock.consNormal (ExecStmt.requireTrue hgeTrue)
              (ExecBlock.consNormal (ExecStmt.assign (hperm := Or.inr (by simpa only [storageStore_executionEnv, initState] using hperm)) hsub1 hassignB)
                (ExecBlock.consRevert (ExecStmt.assignExprRevert
                  (evalExpr_uint256_sub_underflow htdRead (hamt _) (by omega))))))))))))
  obtain ⟨_, _, rd5⟩ := vyperVaultBlocks.vyperVault_block_877_fallthrough (by simp) hperm
    (by
      rw [slotWord_eq]
      exact ugt_zero (by
        show (UInt256.sub (tdB σ I) (argWord I)).toNat ≤ (tdB σ I).toNat
        rw [usub_toNat htd]; omega)) rd4
  simp only [vyperVaultBlocks.vyperVault_block_877_fallthrough_stack] at rd5
  rw [slotWord_eq] at rd5
  obtain ⟨_, _, rd6⟩ := vyperVaultBlocks.vyperVault_block_900 (by simp) hperm rd5
  simp only [vyperVaultBlocks.vyperVault_block_900_stack] at rd6
  -- Stele: the second assignment
  have hsub2 := evalExpr_uint256_sub htdRead (hamt _) htd
  have hassignT : assignStorageRef? config (frame imms (wStore I)) (evmB σ σ₀ (Sat256.ofUInt256 g) A I)
      .storage tdRef (uint256Value (UInt256.sub (tdB σ I) (argWord I))) =
      .ok (frame imms (wStore I), evmT σ σ₀ (Sat256.ofUInt256 g) A I) := by
    apply assignStorageRef_storage_vyper_scalar (hbackend := rfl) (hcheck := by rfl)
      (er := { base := "totalDeposits", steps := [] })
      (hleaf := Or.inl ⟨_, rfl⟩) (ty := .elem (.int (.uint ⟨256, by decide⟩))) (loc := vyperUint256Loc (UInt256.ofNat 2))
      (hbase := by simp) (her := by simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
      (hty := by show storageTypeAt? contract.storage _ = _; decide) (hloc := rfl)
    erw [storageLocStore_uint256, storageStore_executionEnv, storageStore_executionEnv]
    rfl
  -- the `CALL` (pc 916): bridged to Stele's `callViaEVM`
  have hs : SourceState (initState σ σ₀ (Sat256.ofUInt256 g) A I) I (σT σ I) (evmT σ σ₀ (Sat256.ofUInt256 g) A I) :=
    ((SourceState.init.storageWrite ⟨0⟩ (UInt256.ofNat 2)).storageWrite (balSlot I)
      (UInt256.sub (balL σ I) (argWord I))).storageWrite (UInt256.ofNat 2) (UInt256.sub (tdB σ I) (argWord I))
  obtain ⟨evm', σ', z, out, _, _, hcall, hs', rd7, _⟩ := callBridge rd6 hs hperm
    (by append_decode(vyperVaultBytecode, (immutableLayout.suffixWords (wordsOf imms)), (⟨916⟩ : UInt256), .CALL, none))
    (show (hashMem2 I).readWithPadding 0 0 = ByteArray.empty from byteArray_readWithPadding_zero _ _)
    (by show ByteArray.empty.size ≤ _; exact Nat.zero_le _) (by simp)
  have rd8 := RD.normalizePC (pc' := UInt256.ofNat 917) rd7 (by native_decide)
  have hcallStmt : ExecStmt fork config (frame imms (wStore I)) (evmT σ σ₀ (Sat256.ofUInt256 g) A I)
      (.lowLevelCall (.env .caller) (.var "amount") (.newBytes (.intLit 0)) "__ok0" "__data0" true)
      (.ok { frame imms (wStore I) with
          locals := ((wStore I).insert "__ok0" (.bool z)).insert "__data0" (.bytes out) } evm') :=
    lowLevelCallSource (hperm := Or.inr (by simpa only [hs.env] using hperm))
      (by
        rw [evalExpr_caller, accountAddress_roundtrip]
        simp only [storageStore_executionEnv]
        rfl)
      (hamt _) (evalExpr_newBytes_zero _) hcall
  cases z with
  | false =>
    -- the transfer failed: `send` reverts
    have rd9 := vyperVaultBlocks.vyperVault_block_917_taken (by simp) (by decide)
      (by apply D_J_contains_append_left; jump_dest) rd8
    have rd10 := vyperVaultBlocks.vyperVault_block_1403 (by simp [vyperVaultBlocks.vyperVault_block_917_taken_stack]) rd9
    refine RDrev.reEquivExecutionRevert hcode' rd10 hd hdec ?_
    rw [withdrawBody_eq]
    exact ExecFuncBody.execBlockRevert (ExecBlock.consNormal (ExecStmt.requireTrue hcv)
      (ExecBlock.consNormal (ExecStmt.requireTrue hne)
        (ExecBlock.consNormal (ExecStmt.assign (hperm := Or.inr (by simpa only [storageStore_executionEnv, initState] using hperm)) hlit2 hassignL)
          (ExecBlock.consRevert (ExecStmt.internalCallRevert (callee := withdrawCallee) (hargs _) withdrawCallee_lookup rfl
            (ExecFuncBody.execBlockRevert (ExecBlock.consNormal (ExecStmt.requireTrue hgeTrue)
              (ExecBlock.consNormal (ExecStmt.assign (hperm := Or.inr (by simpa only [storageStore_executionEnv, initState] using hperm)) hsub1 hassignB)
                (ExecBlock.consNormal (ExecStmt.assign (hperm := Or.inr (by simpa only [storageStore_executionEnv, initState] using hperm)) hsub2 hassignT)
                  (ExecBlock.consNormal hcallStmt
                    (ExecBlock.consRevert (ExecStmt.requireFalse
                      (evalVar imms _ _ "__ok0" _ (by rw [store_get_ne _ _ (by decide), store_get_self]))))))))))))))
  | true =>
    have rd9 := vyperVaultBlocks.vyperVault_block_917_fallthrough (by simp) (by decide) rd8
    simp only [vyperVaultBlocks.vyperVault_block_917_fallthrough_stack] at rd9
    have rd10 := vyperVaultBlocks.vyperVault_block_922 (by simp) hperm rd9
    have hok : evalExpr? config (frame imms (((wStore I).insert "__ok0" (.bool true)).insert "__data0" (.bytes out))) evm'
        (.var "__ok0") = .ok (.bool true) :=
      evalVar imms _ _ "__ok0" _ (by rw [store_get_ne _ _ (by decide), store_get_self])
    have hemit : evalExprs? config (frame imms (((wStore I).insert "__ok0" (.bool true)).insert "__data0" (.bytes out))) evm'
        [.env .caller, .var "amount"] = .ok [.address evm'.executionEnv.source, uint256Value (argWord I)] := by
      rw [evalExprs?, evalExpr_caller, evalExprs?,
        evalVar imms _ _ "amount" _ (by rw [store_get_ne2 _ _ _ (by decide) (by decide), store_get_self]), evalExprs?]
      rfl
    have hlit3 : evalExpr? config (frame imms ((wStore I).insert "__r" .unit)) evm' (.intLit 3) =
        .ok (uint256Value (UInt256.ofNat 3)) := evalExpr_intLit_word _ 3 (by decide)
    have hassign3 : assignStorageRef? config (frame imms ((wStore I).insert "__r" .unit)) evm' .storage lockRef
        (uint256Value (UInt256.ofNat 3)) =
        .ok (frame imms ((wStore I).insert "__r" .unit), Stele.EVM.storageStore evm' I.codeOwner ⟨0⟩ (UInt256.ofNat 3)) := by
      apply assignStorageRef_storage_vyper_scalar (hbackend := rfl) (hcheck := by rfl)
        (er := { base := "nonreentrant_lock", steps := [] })
        (hleaf := Or.inl ⟨_, rfl⟩) (ty := .elem (.int (.uint ⟨256, by decide⟩))) (loc := vyperUint256Loc ⟨0⟩)
        (hbase := by simp) (her := by simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
        (hty := by show storageTypeAt? contract.storage _ = _; decide) (hloc := rfl)
      erw [storageLocStore_uint256, hs'.env]
    have hbody : ExecTransitionBody fork config contract (initState σ σ₀ (Sat256.ofUInt256 g) A I) (wStore I)
        withdrawTransition.body
        (.returned (frame imms ((wStore I).insert "__r" .unit))
          (Stele.EVM.storageStore evm' I.codeOwner ⟨0⟩ (UInt256.ofNat 3)) none)
        (restrictImmutables contract imms) := by
      rw [withdrawBody_eq]
      exact ExecFuncBody.execBlockOK (ExecBlock.consNormal (ExecStmt.requireTrue hcv)
        (ExecBlock.consNormal (ExecStmt.requireTrue hne)
          (ExecBlock.consNormal (ExecStmt.assign (hperm := Or.inr (by simpa only [storageStore_executionEnv, initState] using hperm)) hlit2 hassignL)
            (ExecBlock.consNormal (ExecStmt.internalCallReturn (callee := withdrawCallee) (hargs _) withdrawCallee_lookup rfl
              (ExecFuncBody.execBlockOK (ExecBlock.consNormal (ExecStmt.requireTrue hgeTrue)
                (ExecBlock.consNormal (ExecStmt.assign (hperm := Or.inr (by simpa only [storageStore_executionEnv, initState] using hperm)) hsub1 hassignB)
                  (ExecBlock.consNormal (ExecStmt.assign (hperm := Or.inr (by simpa only [storageStore_executionEnv, initState] using hperm)) hsub2 hassignT)
                    (ExecBlock.consNormal hcallStmt
                      (ExecBlock.consNormal (ExecStmt.requireTrue hok)
                        (ExecBlock.consNormal (ExecStmt.emit (hperm := by simpa only [hs'.env] using hperm) hemit) ExecBlock.nil))))))))
              (ExecBlock.consNormal (ExecStmt.assign (hperm := Or.inr (by simpa only [hs'.env] using hperm)) hlit3 hassign3) ExecBlock.nil)))))
    exact rd10.reEquivExecutionGen hcode' hd hdec hbody ((hs'.storageWrite ⟨0⟩ (UInt256.ofNat 3)).accounts)
      (returnEquiv.fallthrough rfl rfl (by native_decide))

end Tests.Pipeline.VyperVault
