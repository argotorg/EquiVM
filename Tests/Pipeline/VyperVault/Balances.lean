import Tests.Pipeline.VyperVault.Helpers

variable {fork : Ethereum.Fork}

/-!
# VyperVault `balances(address)`

Dispatcher bucket 8, arm entry pc 1223: the `calldatasize`/`callvalue` guard, the address
validation, then `keccak256(1 ++ arg)`, `SLOAD` and `RETURN`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
  Reasoning.VyperImmutables

namespace Tests.Pipeline.VyperVault

set_option maxRecDepth 2000000

theorem balancesBody_eq : balancesTransition.body =
    [.require (.binary .eq (.env .callvalue) (.intLit 0)),
     .return [.storage { base := "balances", steps := [.mindex (.var "arg0")] }]] := by rfl

/-- The decoded argument store. -/
abbrev balancesStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "arg0" (.address (AccountAddress.ofNat (argWord I).toNat))

theorem balancesDecode_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size)
    (hcanon : (argWord I).toNat < EVM.addressModulus) :
    config.externalABI.decodeCalldata? (balancesTransition.params.map Param.name)
      (transitionSignature balancesTransition).paramTypes I.calldata = some (balancesStore I) := by
  rw [argWord_eq] at hcanon
  simpa [config, contract, Syntax.contractSyntax, balancesTransition, balancesStore, argWord_eq] using
    decodeCalldataWithMode_vyper_address_ok (cd := I.calldata) (x := "arg0") hsz36 hcanon

theorem balancesDecode_short {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size)
    (hshort : I.calldata.size < 36) :
    config.externalABI.decodeCalldata? (balancesTransition.params.map Param.name)
      (transitionSignature balancesTransition).paramTypes I.calldata = none := by
  simpa [config, contract, Syntax.contractSyntax, balancesTransition] using
    decodeCalldataWithMode_vyper_address_none_short (cd := I.calldata) (x := "arg0") hsz hshort

theorem balancesDecode_noncanon {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size)
    (hnc : ¬ (argWord I).toNat < EVM.addressModulus) :
    config.externalABI.decodeCalldata? (balancesTransition.params.map Param.name)
      (transitionSignature balancesTransition).paramTypes I.calldata = none := by
  rw [argWord_eq] at hnc
  simpa [config, contract, Syntax.contractSyntax, balancesTransition] using
    decodeCalldataWithMode_vyper_address_none_noncanon (cd := I.calldata) (x := "arg0") hsz36 hnc

/-- `balances(address)`: the theorem `Correct.lean` routes selector 2 to. -/
theorem vyperVaultBalancesBody {σ σ₀ A I} {g : UInt256} (imms : Store) (hfit : immutablesFit contract imms)
    (hwf : storageWF σ I)
    (hcode : I.code = immutableLayout.deployed vyperVaultBytecode imms) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vyperVaultSelBytes 2)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I (restrictImmutables contract imms) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (vyperVaultSelBytes 2) rfl hsel
  have hcode' : I.code = vyperVaultBytecode ++ immutableLayout.suffixWords (wordsOf imms) := by
    rw [hcode, deployed_of_fit hfit]
  obtain ⟨_, _, rd⟩ := vyperVaultReachBalancesBody (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) hcode' hsz hsize hsel
  have hd : dispatchMsg contract I.calldata = some balancesTransition :=
    vyperVaultDispatch_balances (selIs_exclusive (by native_decide) hsel)
      (selIs_exclusive (by native_decide) hsel) hsel
  have hmemsize : (vyperVaultDispatchMem 8).size = 32 := by native_decide
  by_cases hshort : I.calldata.size < 36
  · -- short calldata: the guard reverts, the spec does not decode
    have rd1 := vyperVaultBlocks.vyperVault_block_1223_taken (by simp) (guard_short hsize hshort)
      (by apply D_J_contains_append_left; jump_dest) rd
    have rd2 := vyperVaultBlocks.vyperVault_block_1403 (by simp) rd1
    exact RDrev.reEquivDecodingFailed hcode' rd2 hd (balancesDecode_short hsz hshort)
  have hsz36 : 36 ≤ I.calldata.size := by omega
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · have rd1 := vyperVaultBlocks.vyperVault_block_1223_taken (by simp) (guard_wv hwv)
      (by apply D_J_contains_append_left; jump_dest) rd
    have rd2 := vyperVaultBlocks.vyperVault_block_1403 (by simp) rd1
    exact RDrev.reEquivOfDispatch hcode' hd
      (fun _ => by rw [balancesBody_eq]; exact bodyReverts_nonPayable (by simpa [initState] using hwv)) rd2
  have rd1 := vyperVaultBlocks.vyperVault_block_1223_fallthrough (by simp) (guard_ok hwv hsz36 hsize) rd
  by_cases hcanon : (argWord I).toNat < EVM.addressModulus
  swap
  · -- a non-canonical address word: the validation reverts, the spec does not decode
    have rd2 := vyperVaultBlocks.vyperVault_block_1233_taken (by simp)
      (by
        intro h
        exact hcanon (u256_lt_addressModulus_of_shiftRight160_zero _ h))
      (by apply D_J_contains_append_left; jump_dest) rd1
    have rd3 := vyperVaultBlocks.vyperVault_block_1403
      (by simp [vyperVaultBlocks.vyperVault_block_1233_taken_stack]) rd2
    exact RDrev.reEquivDecodingFailed hcode' rd3 hd (balancesDecode_noncanon hsz36 hcanon)
  have rd2 := vyperVaultBlocks.vyperVault_block_1233_fallthrough (by simp)
    (u256_shiftRight160_zero_of_lt _ hcanon) rd1
  have rd3 := vyperVaultBlocks.vyperVault_block_1244 (by simp) rd2
  simp only [vyperVaultBlocks.vyperVault_block_1233_fallthrough_stack] at rd3
  -- the scratch memory is `wordAt0Mem 1 (wordAt32Mem arg argMem)`, hashing to the mapping slot
  have hkec : keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64)
      ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 64)
        ((uInt256OfByteArray (I.calldata.readBytes (UInt256.ofNat 4).toNat 32)).toByteArray.write 0
          (vyperVaultDispatchMem 8) (UInt256.ofNat 64).toNat 32)).toByteArray.write 0
        ((uInt256OfByteArray (I.calldata.readBytes (UInt256.ofNat 4).toNat 32)).toByteArray.write 0
          (vyperVaultDispatchMem 8) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 32).toNat 32)
        (⟨0⟩ : UInt256).toNat 32) =
      vyperMappingSlot (UInt256.ofNat 1) (.address (AccountAddress.ofNat (argWord I).toNat)) :=
    keccak_argMem 8 (argWord I) hmemsize hcanon
  have hhashsize : ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 64)
        ((uInt256OfByteArray (I.calldata.readBytes (UInt256.ofNat 4).toNat 32)).toByteArray.write 0
          (vyperVaultDispatchMem 8) (UInt256.ofNat 64).toNat 32)).toByteArray.write 0
        ((uInt256OfByteArray (I.calldata.readBytes (UInt256.ofNat 4).toNat 32)).toByteArray.write 0
          (vyperVaultDispatchMem 8) (UInt256.ofNat 64).toNat 32) 32 32)
        (⟨0⟩ : UInt256).toNat 32).size = 96 :=
    wordAt0Mem_size_96 _ (wordAt32Mem_size_96 _ (argMem_size 8 _ hmemsize))
  rw [hkec, slotWord_eq, ulit_toNat' 96 (by decide), ulit_toNat' 32 (by decide),
    toByteArray_write_read_back_of_gap _ _ 96 (by rw [hhashsize]; exact lt_usize _ (by decide))] at rd3
  have hbody : ExecTransitionBody fork config contract (initState σ σ₀ (Sat256.ofUInt256 g) A I) (balancesStore I)
      balancesTransition.body
      (.returned (frame imms (balancesStore I)) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (some [.int (Int.ofNat (solcSlotWordAt
          (vyperMappingSlot (UInt256.ofNat 1) (.address (AccountAddress.ofNat (argWord I).toNat))) σ I).toNat)]))
      (restrictImmutables contract imms) := by
    rw [balancesBody_eq]
    refine ExecFuncBody.execBlockRet
      ((ABlock.start.requireStep (evalCallvalueEq_true (by simpa [initState] using hwv))).returns ?_)
    have her : evalStorageRef config (frame imms (balancesStore I)) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        { base := "balances", steps := [.mindex (.var "arg0")] } =
        .ok { base := "balances", steps := [.mindex (.address (AccountAddress.ofNat (argWord I).toNat))] } := by
      simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, balancesStore, valueToKey?,
        EvalResult.seqList, EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?]
    rw [evalExpr_storage_vyper_uint256_backend (hbackend := rfl) (hcheck := by rfl)
        (physicalSlot := vyperMappingSlot (UInt256.ofNat 1) (.address (AccountAddress.ofNat (argWord I).toNat)))
        (hbase := by simp [balancesStore]) (her := her)
        (hty := by simp [storageTypeAt?, storageTypeStep?, contract, Syntax.contractSyntax])
        (hloc := rfl),
      storageLoad_initState_ofUInt256_solcSlotWordAt]
  exact rd3.reEquivExecution hcode' hd (balancesDecode_ok hsz36 hcanon) hbody
    (returnEquiv_of_encode (uint256ReturnEncoding _))

end Tests.Pipeline.VyperVault
