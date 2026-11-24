import Tests.Pipeline.VyperVault.Helpers

variable {fork : Ethereum.Fork}

/-!
# VyperVault `setPaused(bool)`

Dispatcher bucket 10, arm entry pc 984: the guard, the `bool` validation (`arg >> 1 == 0`), the
owner check against the immutable `OWNER` (pc 1005), then `SSTORE` of the raw word into slot 4
(pc 1145) or the `assert` revert payload (pc 1024).  In static mode the `SSTORE` halts, matching
the spec's static violation.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
  Reasoning.VyperImmutables

namespace Tests.Pipeline.VyperVault

set_option maxRecDepth 2000000

theorem setPausedBody_eq : setPausedTransition.body =
    [.require (.binary .eq (.env .callvalue) (.intLit 0)),
     .require (.binary .eq (.env .caller) (.immutable "OWNER")),
     .assign .storage { base := "paused", steps := [] } (.var "flag")] := by rfl

/-- The decoded argument store: a validated word `0`/`1` decodes to its `Bool`. -/
abbrev setPausedStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "flag" (.bool (decide ((argWord I).toNat = 1)))

theorem decodeMode_bool_ok (cd : ByteArray) (hsz36 : 36 ≤ cd.size)
    (hlt : (calldataWord cd 4).toNat < 2) :
    decodeCalldataWithMode DecodeMode.vyper ["flag"] [.elem .bool] cd =
      some ((∅ : Store).insert "flag" (.bool (decide ((calldataWord cd 4).toNat = 1)))) := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  rw [decodeCalldataWithMode_vyperScalarWords_eq (by decide), if_neg (by rw [htlen]; omega)]
  simp only [decodeScalarWords?]
  rcases (by omega : (calldataWord cd 4).toNat = 0 ∨ (calldataWord cd 4).toNat = 1) with h0 | h1
  · rw [decodeScalarWord_bool_ok_zero (start := 0) (by simpa using htake4)
      (by rw [List.drop_zero, hword4]; exact uint256_toNat_eq_zero h0)]
    simp [decodeScalarWords?, decodeCalldata.insertValues, h0]
  · rw [decodeScalarWord_bool_ok_one (start := 0) (by simpa using htake4)
      (by rw [List.drop_zero, hword4]; exact u256_inj (by rw [h1]; rfl))]
    simp [decodeScalarWords?, decodeCalldata.insertValues, h1]

theorem decodeMode_bool_none (cd : ByteArray) (hsz36 : 36 ≤ cd.size)
    (hnlt : ¬ (calldataWord cd 4).toNat < 2) :
    decodeCalldataWithMode DecodeMode.vyper ["flag"] [.elem .bool] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  rw [decodeCalldataWithMode_vyperScalarWords_eq (by decide), if_neg (by rw [htlen]; omega)]
  simp only [decodeScalarWords?]
  rw [decodeScalarWord_bool_none_noncanon (start := 0) (by simpa using htake4)
    (by rw [List.drop_zero, hword4]; intro h; apply hnlt; rw [h]; decide)
    (by rw [List.drop_zero, hword4]; intro h; apply hnlt; rw [h]; decide)]
  rfl

theorem setPausedDecode_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size)
    (hlt : (argWord I).toNat < 2) :
    config.externalABI.decodeCalldata? (setPausedTransition.params.map Param.name)
      (transitionSignature setPausedTransition).paramTypes I.calldata = some (setPausedStore I) := by
  rw [argWord_eq] at hlt
  simpa [config, contract, Syntax.contractSyntax, setPausedTransition, setPausedStore, argWord_eq] using
    decodeMode_bool_ok I.calldata hsz36 hlt

theorem setPausedDecode_none {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size)
    (hnlt : ¬ (argWord I).toNat < 2) :
    config.externalABI.decodeCalldata? (setPausedTransition.params.map Param.name)
      (transitionSignature setPausedTransition).paramTypes I.calldata = none := by
  rw [argWord_eq] at hnlt
  simpa [config, contract, Syntax.contractSyntax, setPausedTransition] using
    decodeMode_bool_none I.calldata hsz36 hnlt

theorem setPausedDecode_short {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size)
    (hshort : I.calldata.size < 36) :
    config.externalABI.decodeCalldata? (setPausedTransition.params.map Param.name)
      (transitionSignature setPausedTransition).paramTypes I.calldata = none := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have hshort' : ¬ ((I.calldata.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  simp only [config, contract, Syntax.contractSyntax, setPausedTransition]
  show decodeCalldataWithMode DecodeMode.vyper ["flag"] [.elem .bool] I.calldata = none
  rw [decodeCalldataWithMode_vyperScalarWords_eq (by decide), if_neg (by rw [htlen]; omega)]
  simp only [decodeScalarWords?]
  rw [decodeScalarWord_bool_none_short (start := 0) (by simpa using hshort')]
  rfl

/-- `setPaused(bool)`: the theorem `Correct.lean` routes selector 1 to. -/
theorem vyperVaultSetPausedBody {σ σ₀ A I} {g : UInt256} (imms : Store) (hfit : immutablesFit contract imms)
    (hwf : storageWF σ I)
    (hcode : I.code = immutableLayout.deployed vyperVaultBytecode imms) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vyperVaultSelBytes 1)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I (restrictImmutables contract imms) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (vyperVaultSelBytes 1) rfl hsel
  have hcode' : I.code = vyperVaultBytecode ++ immutableLayout.suffixWords (wordsOf imms) := by
    rw [hcode, deployed_of_fit hfit]
  obtain ⟨a, hget⟩ := owner_of_fit hfit
  obtain ⟨_, _, rd⟩ := vyperVaultReachSetPausedBody (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) hcode' hsz hsize hsel
  have hd : dispatchMsg contract I.calldata = some setPausedTransition :=
    vyperVaultDispatch_setPaused (selIs_exclusive (by native_decide) hsel) hsel
  have hmemsize : (vyperVaultDispatchMem 10).size = 32 := by native_decide
  by_cases hshort : I.calldata.size < 36
  · have rd1 := vyperVaultBlocks.vyperVault_block_984_taken (by simp) (guard_short hsize hshort)
      (by apply D_J_contains_append_left; jump_dest) rd
    have rd2 := vyperVaultBlocks.vyperVault_block_1403 (by simp) rd1
    exact RDrev.reEquivDecodingFailed hcode' rd2 hd (setPausedDecode_short hsz hshort)
  have hsz36 : 36 ≤ I.calldata.size := by omega
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · have rd1 := vyperVaultBlocks.vyperVault_block_984_taken (by simp) (guard_wv hwv)
      (by apply D_J_contains_append_left; jump_dest) rd
    have rd2 := vyperVaultBlocks.vyperVault_block_1403 (by simp) rd1
    exact RDrev.reEquivOfDispatch hcode' hd
      (fun _ => by rw [setPausedBody_eq]; exact bodyReverts_nonPayable (by simpa [initState] using hwv)) rd2
  have rd1 := vyperVaultBlocks.vyperVault_block_984_fallthrough (by simp) (guard_ok hwv hsz36 hsize) rd
  by_cases hlt : (argWord I).toNat < 2
  swap
  · -- not a bool word: the validation reverts, the spec does not decode
    have rd2 := vyperVaultBlocks.vyperVault_block_994_taken (by simp)
      (by intro h; exact hlt (u256_lt_two_of_shiftRight1_zero _ h))
      (by apply D_J_contains_append_left; jump_dest) rd1
    have rd3 := vyperVaultBlocks.vyperVault_block_1403
      (by simp [vyperVaultBlocks.vyperVault_block_994_taken_stack]) rd2
    exact RDrev.reEquivDecodingFailed hcode' rd3 hd (setPausedDecode_none hsz36 hlt)
  have rd2 := vyperVaultBlocks.vyperVault_block_994_fallthrough (by simp)
    (u256_shiftRight1_zero_of_lt _ hlt) rd1
  simp only [vyperVaultBlocks.vyperVault_block_994_fallthrough_stack] at rd2
  have hdec := setPausedDecode_ok hsz36 hlt
  have hcv : evalExpr? config (frame imms (setPausedStore I)) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (.binary .eq (.env .callvalue) (.intLit 0)) = .ok (.bool true) :=
    evalCallvalueEq_true (by simpa [initState] using hwv)
  have hcaller := evalCallerEqOwner (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hget
    (setPausedStore I)
  by_cases hown : I.source = a
  swap
  · -- not the owner: `assert` reverts
    have rd3 := vyperVaultBlocks.vyperVault_block_1005_fallthrough (immWords := wordsOf imms) (by simp)
      (by rw [wordsOf_OWNER hget]; exact isZero_xor_eq_zero_of_ne (fun h => hown (ofNat_addr_inj h))) rd2
    have rd4 := vyperVaultBlocks.vyperVault_block_1024
      (by simp [vyperVaultBlocks.vyperVault_block_1005_fallthrough_stack]) rd3
    have rd5 := vyperVaultBlocks.vyperVault_block_1139
      (by simp [vyperVaultBlocks.vyperVault_block_1005_fallthrough_stack]) rd4
    refine RDrev.reEquivExecutionRevert hcode' rd5 hd hdec ?_
    rw [setPausedBody_eq]
    rw [decide_eq_false hown] at hcaller
    exact ExecFuncBody.execBlockRevert ((ABlock.start.requireStep hcv).requireRevert hcaller)
  rw [decide_eq_true hown] at hcaller
  have rd3 := vyperVaultBlocks.vyperVault_block_1005_taken (immWords := wordsOf imms) (by simp)
    (by rw [wordsOf_OWNER hget]; exact isZero_xor_ne_zero_of_eq (by rw [hown]; rfl))
    (by apply D_J_contains_append_left; jump_dest) rd2
  simp only [vyperVaultBlocks.vyperVault_block_1005_taken_stack] at rd3
  -- the word stored is the validated argument
  have hmem : memLoad (UInt256.ofNat 64) (vyperVaultBlocks.vyperVault_block_1005_taken_memory
      (immWords := wordsOf imms) (mem := vyperVaultDispatchMem 10) (x0 := argWord I)) = argWord I := by
    unfold vyperVaultBlocks.vyperVault_block_1005_taken_memory
    rw [memLoad64_write0 _ _ (by rw [toByteArray_size]) (argMem_size 10 _ hmemsize),
      memLoad_argMem 10 _ hmemsize]
  have hflag : evalExpr? config (frame imms (setPausedStore I)) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (.var "flag") = .ok (.bool (decide ((argWord I).toNat = 1))) :=
    evalVar imms _ _ "flag" _ (store_get_self _ _ _)
  have hassign : assignStorageRef? config (frame imms (setPausedStore I))
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) .storage { base := "paused", steps := [] }
      (.bool (decide ((argWord I).toNat = 1))) =
      .ok (frame imms (setPausedStore I),
        Stele.EVM.storageStore (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          (initState σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner (UInt256.ofNat 4) (argWord I)) := by
    apply assignStorageRef_storage_vyper_scalar_value (hbackend := rfl) (hcheck := by rfl)
      (er := { base := "paused", steps := [] })
      (hleaf := Or.inl ⟨_, rfl⟩) (ty := .elem .bool) (loc := vyperWordLoc (UInt256.ofNat 4) .bool)
      (hbase := by simp [setPausedStore])
      (her := by simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
      (hty := by show storageTypeAt? contract.storage _ = _; decide) (hloc := rfl)
    rw [storageLocStore_vyperWord_bool, bool_toUInt256_decide _ hlt]
  by_cases hperm : I.perm = true
  · have rd4 := vyperVaultBlocks.vyperVault_block_1145 (by simp) hperm rd3
    rw [hmem] at rd4
    have hbody : ExecTransitionBody fork config contract (initState σ σ₀ (Sat256.ofUInt256 g) A I) (setPausedStore I)
        setPausedTransition.body
        (.returned (frame imms (setPausedStore I))
          (Stele.EVM.storageStore (initState σ σ₀ (Sat256.ofUInt256 g) A I)
            (initState σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner (UInt256.ofNat 4) (argWord I)) none)
        (restrictImmutables contract imms) := by
      rw [setPausedBody_eq]
      exact ExecFuncBody.execBlockOK (ExecBlock.consNormal (ExecStmt.requireTrue hcv)
        (ExecBlock.consNormal (ExecStmt.requireTrue hcaller)
          (ExecBlock.consNormal (ExecStmt.assign (hperm := by first | assumption | exact Or.inr ‹_› | exact Or.inl rfl) hflag hassign) ExecBlock.nil)))
    exact rd4.reEquivExecutionGen hcode' hd hdec hbody (by rw [storageStore_accountMap]; rfl)
      (returnEquiv.fallthrough rfl rfl (by native_decide))
  · have hpf : I.perm = false := by simpa using hperm
    have r1 := rd3.jumpdest
      (by append_decode(vyperVaultBytecode, (immutableLayout.suffixWords (wordsOf imms)), (⟨1145⟩ : UInt256), .JUMPDEST, none))
      (by evm_ov)
    have r2 := r1.push1 (UInt256.ofNat 64)
      (by append_decode(vyperVaultBytecode, (immutableLayout.suffixWords (wordsOf imms)), (⟨1146⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 64), 1)))
      (by evm_ov)
    have r3 := RD.genMload r2
      (by append_decode(vyperVaultBytecode, (immutableLayout.suffixWords (wordsOf imms)), (⟨1148⟩ : UInt256), .MLOAD, none))
      (by evm_ov)
    have r4 := r3.push1 (UInt256.ofNat 4)
      (by append_decode(vyperVaultBytecode, (immutableLayout.suffixWords (wordsOf imms)), (⟨1149⟩ : UInt256), .Push .PUSH1, some ((UInt256.ofNat 4), 1)))
      (by evm_ov)
    have rs := r4.sstoreStatic hpf
      (by append_decode(vyperVaultBytecode, (immutableLayout.suffixWords (wordsOf imms)), (⟨1151⟩ : UInt256), .SSTORE, none))
      (by evm_ov)
    refine RDstatic.reEquivStaticHalt hcode' rs hd hdec ?_
    rw [setPausedBody_eq]
    exact ExecFuncBody.execBlockStatic (ExecBlock.consNormal (ExecStmt.requireTrue hcv)
      (ExecBlock.consNormal (ExecStmt.requireTrue hcaller)
        (ExecBlock.consStatic (ExecStmt.assignStatic hflag hassign (by show I.perm = false; exact hpf)))))

end Tests.Pipeline.VyperVault
