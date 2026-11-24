import Tests.Pipeline.VyperVault.Helpers

variable {fork : Ethereum.Fork}

/-!
# VyperVault `available(address)`

Dispatcher bucket 7, arm entry pc 1282: the guard, the address validation, `balances[account]`
(pc 1303), `SELFBALANCE` (pc 1321, stepped by hand: the summary generator stops at it) and the
branchless `min` at pc 1322.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
  Reasoning.VyperImmutables

namespace Tests.Pipeline.VyperVault

set_option maxRecDepth 2000000

theorem availableBody_eq : availableTransition.body =
    [.require (.binary .eq (.env .callvalue) (.intLit 0)),
     .letDecl "__v0" (some (.elem (.int (.uint ⟨256, by decide⟩))))
       (.storage { base := "balances", steps := [.mindex (.var "account")] }),
     .letDecl "__v1" (some (.elem (.int (.uint ⟨256, by decide⟩)))) (.env .selfbalance),
     .return [.ite (.binary .lt (.var "__v0") (.var "__v1")) (.var "__v0") (.var "__v1")]] := by rfl

/-- The decoded argument store. -/
abbrev availableStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "account" (.address (AccountAddress.ofNat (argWord I).toNat))

theorem availableDecode_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size)
    (hcanon : (argWord I).toNat < EVM.addressModulus) :
    config.externalABI.decodeCalldata? (availableTransition.params.map Param.name)
      (transitionSignature availableTransition).paramTypes I.calldata = some (availableStore I) := by
  rw [argWord_eq] at hcanon
  simpa [config, contract, Syntax.contractSyntax, availableTransition, availableStore, argWord_eq] using
    decodeCalldataWithMode_vyper_address_ok (cd := I.calldata) (x := "account") hsz36 hcanon

theorem availableDecode_short {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size)
    (hshort : I.calldata.size < 36) :
    config.externalABI.decodeCalldata? (availableTransition.params.map Param.name)
      (transitionSignature availableTransition).paramTypes I.calldata = none := by
  simpa [config, contract, Syntax.contractSyntax, availableTransition] using
    decodeCalldataWithMode_vyper_address_none_short (cd := I.calldata) (x := "account") hsz hshort

theorem availableDecode_noncanon {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size)
    (hnc : ¬ (argWord I).toNat < EVM.addressModulus) :
    config.externalABI.decodeCalldata? (availableTransition.params.map Param.name)
      (transitionSignature availableTransition).paramTypes I.calldata = none := by
  rw [argWord_eq] at hnc
  simpa [config, contract, Syntax.contractSyntax, availableTransition] using
    decodeCalldataWithMode_vyper_address_none_noncanon (cd := I.calldata) (x := "account") hsz36 hnc

/-- `available(address)`: the theorem `Correct.lean` routes selector 0 to. -/
theorem vyperVaultAvailableBody {σ σ₀ A I} {g : UInt256} (imms : Store) (hfit : immutablesFit contract imms)
    (hwf : storageWF σ I)
    (hcode : I.code = immutableLayout.deployed vyperVaultBytecode imms) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vyperVaultSelBytes 0)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I (restrictImmutables contract imms) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (vyperVaultSelBytes 0) rfl hsel
  have hcode' : I.code = vyperVaultBytecode ++ immutableLayout.suffixWords (wordsOf imms) := by
    rw [hcode, deployed_of_fit hfit]
  obtain ⟨_, _, rd⟩ := vyperVaultReachAvailableBody (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) hcode' hsz hsize hsel
  have hd : dispatchMsg contract I.calldata = some availableTransition := vyperVaultDispatch_available hsel
  have hmemsize : (vyperVaultDispatchMem 7).size = 32 := by native_decide
  by_cases hshort : I.calldata.size < 36
  · have rd1 := vyperVaultBlocks.vyperVault_block_1282_taken (by simp) (guard_short hsize hshort)
      (by apply D_J_contains_append_left; jump_dest) rd
    have rd2 := vyperVaultBlocks.vyperVault_block_1403 (by simp) rd1
    exact RDrev.reEquivDecodingFailed hcode' rd2 hd (availableDecode_short hsz hshort)
  have hsz36 : 36 ≤ I.calldata.size := by omega
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · have rd1 := vyperVaultBlocks.vyperVault_block_1282_taken (by simp) (guard_wv hwv)
      (by apply D_J_contains_append_left; jump_dest) rd
    have rd2 := vyperVaultBlocks.vyperVault_block_1403 (by simp) rd1
    exact RDrev.reEquivOfDispatch hcode' hd
      (fun _ => by rw [availableBody_eq]; exact bodyReverts_nonPayable (by simpa [initState] using hwv)) rd2
  have rd1 := vyperVaultBlocks.vyperVault_block_1282_fallthrough (by simp) (guard_ok hwv hsz36 hsize) rd
  by_cases hcanon : (argWord I).toNat < EVM.addressModulus
  swap
  · have rd2 := vyperVaultBlocks.vyperVault_block_1292_taken (by simp)
      (by
        intro h
        exact hcanon (u256_lt_addressModulus_of_shiftRight160_zero _ h))
      (by apply D_J_contains_append_left; jump_dest) rd1
    have rd3 := vyperVaultBlocks.vyperVault_block_1403
      (by simp [vyperVaultBlocks.vyperVault_block_1292_taken_stack]) rd2
    exact RDrev.reEquivDecodingFailed hcode' rd3 hd (availableDecode_noncanon hsz36 hcanon)
  have rd2 := vyperVaultBlocks.vyperVault_block_1292_fallthrough (by simp)
    (u256_shiftRight160_zero_of_lt _ hcanon) rd1
  simp only [vyperVaultBlocks.vyperVault_block_1292_fallthrough_stack] at rd2
  obtain ⟨_, _, rd3⟩ := vyperVaultBlocks.vyperVault_block_1303 (by simp) rd2
  simp only [vyperVaultBlocks.vyperVault_block_1303_stack] at rd3
  -- SELFBALANCE at pc 1321, by hand
  have rd4 := RD.normalizePC (pc' := UInt256.ofNat 1322)
    (rd3.selfbalance
      (by append_decode(vyperVaultBytecode, immutableLayout.suffixWords (wordsOf imms),
        (⟨1321⟩ : UInt256), .SELFBALANCE, none))
      (by simp))
    (by native_decide)
  have rd5 := vyperVaultBlocks.vyperVault_block_1322 (by simp) rd4
  -- the scratch memory hashes to the mapping slot
  have hkec : keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64)
      ((UInt256.ofNat 1).toByteArray.write 0 ((memLoad (UInt256.ofNat 64)
        ((uInt256OfByteArray (I.calldata.readBytes (UInt256.ofNat 4).toNat 32)).toByteArray.write 0
          (vyperVaultDispatchMem 7) (UInt256.ofNat 64).toNat 32)).toByteArray.write 0
        ((uInt256OfByteArray (I.calldata.readBytes (UInt256.ofNat 4).toNat 32)).toByteArray.write 0
          (vyperVaultDispatchMem 7) (UInt256.ofNat 64).toNat 32) (UInt256.ofNat 32).toNat 32)
        (⟨0⟩ : UInt256).toNat 32) =
      vyperMappingSlot (UInt256.ofNat 1) (.address (AccountAddress.ofNat (argWord I).toNat)) :=
    keccak_argMem 7 (argWord I) hmemsize hcanon
  have hmemsz : (vyperVaultBlocks.vyperVault_block_1303_memory (mem := vyperVaultDispatchMem 7)
      (x0 := uInt256OfByteArray (I.calldata.readBytes (UInt256.ofNat 4).toNat 32))).size = 96 :=
    wordAt0Mem_size_96 _ (wordAt32Mem_size_96 _ (argMem_size 7 _ hmemsize))
  rw [hkec, slotWord_eq, branchlessMin, ulit_toNat' 96 (by decide), ulit_toNat' 32 (by decide),
    toByteArray_write_read_back_of_gap _ _ 96 (by rw [hmemsz]; exact lt_usize _ (by decide))] at rd5
  -- the Stele body
  set bal := solcSlotWordAt (vyperMappingSlot (UInt256.ofNat 1)
    (.address (AccountAddress.ofNat (argWord I).toNat))) σ I with hbal
  set sb := selfBalanceWord σ I with hsb
  set L1 := (availableStore I).insert "__v0" (.int (Int.ofNat bal.toNat)) with hL1
  set L2 := L1.insert "__v1" (.int (Int.ofNat sb.toNat)) with hL2
  have hget0 : L2.get? "__v0" = some (.int (Int.ofNat bal.toNat)) := by
    rw [hL2, store_get_ne _ _ (by decide), hL1, store_get_self]
  have hget1 : L2.get? "__v1" = some (.int (Int.ofNat sb.toNat)) := by
    rw [hL2, store_get_self]
  have hbody : ExecTransitionBody fork config contract (initState σ σ₀ (Sat256.ofUInt256 g) A I) (availableStore I)
      availableTransition.body
      (.returned (frame imms L2) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (some [.int (Int.ofNat (if bal.toNat < sb.toNat then bal else sb).toNat)]))
      (restrictImmutables contract imms) := by
    rw [availableBody_eq]
    refine ExecFuncBody.execBlockRet
      ((((ABlock.start.requireStep (evalCallvalueEq_true (by simpa [initState] using hwv))).letStep
        (value := .int (Int.ofNat bal.toNat)) ?_).letStep (value := .int (Int.ofNat sb.toNat)) ?_).returns ?_)
    · have her : evalStorageRef config (frame imms (availableStore I)) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          { base := "balances", steps := [.mindex (.var "account")] } =
          .ok { base := "balances", steps := [.mindex (.address (AccountAddress.ofNat (argWord I).toNat))] } := by
        simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, availableStore, valueToKey?,
          EvalResult.seqList, EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?]
      rw [evalExpr_storage_vyper_uint256_backend (hbackend := rfl) (hcheck := by rfl)
          (physicalSlot := vyperMappingSlot (UInt256.ofNat 1) (.address (AccountAddress.ofNat (argWord I).toNat)))
          (hbase := by simp [availableStore]) (her := her)
          (hty := by simp [storageTypeAt?, storageTypeStep?, contract, Syntax.contractSyntax])
          (hloc := rfl),
        storageLoad_initState_ofUInt256_solcSlotWordAt]
    · exact evalSelfbalance imms _
    · refine evalIte imms L2 _ (evalLtVars imms L2 _ "__v0" "__v1" bal sb hget0 hget1) ?_ ?_
      · intro hb
        rw [if_pos (by simpa using hb)]
        exact evalVar imms L2 _ "__v0" _ hget0
      · intro hb
        rw [if_neg (by simpa using hb)]
        exact evalVar imms L2 _ "__v1" _ hget1
  exact rd5.reEquivExecution hcode' hd (availableDecode_ok hsz36 hcanon) hbody
    (returnEquiv_of_encode (uint256ReturnEncoding _))

end Tests.Pipeline.VyperVault
