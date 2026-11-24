import Tests.Pipeline.VyperRegistry.Helpers

variable {fork : Ethereum.Fork}

/-!
# Registry `ids(uint256)`

Dispatcher bucket 8, arm entry pc 1498: the guard, the index check `arg0 < len(ids)` (pc 1508,
the backend's index check), and the data word at slot `3 + arg0`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
  Reasoning.VyperBounded

namespace Tests.Pipeline.VyperRegistry

set_option maxRecDepth 2000000

abbrev idsRef : StorageRef := { base := "ids", steps := [.aindex (.var "arg0")] }

theorem idsBody_eq : idsTransition.body =
    [.require (.binary .eq (.env .callvalue) (.intLit 0)), .return [.storage idsRef]] := by rfl

abbrev idsStore (I : ExecutionEnv) : Store := (∅ : Store).insert "arg0" (uint256Value (argWord I))

theorem idsDecode_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    config.externalABI.decodeCalldata? (idsTransition.params.map Param.name)
      (transitionSignature idsTransition).paramTypes I.calldata = some (idsStore I) := by
  simpa [config, contract, Syntax.contractSyntax, idsTransition, idsStore, argWord_eq] using
    decodeMode_uint256_ok "arg0" I.calldata hsz36

theorem idsDecode_short {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    config.externalABI.decodeCalldata? (idsTransition.params.map Param.name)
      (transitionSignature idsTransition).paramTypes I.calldata = none := by
  simpa [config, contract, Syntax.contractSyntax, idsTransition] using
    decodeMode_uint256_none_short "arg0" I.calldata hsz hshort

/-- `ids(uint256)`: the theorem `Correct.lean` routes selector 11 to. -/
theorem registryIdsBody {σ σ₀ A I} {g : UInt256} (_hwf : storageWF σ I)
    (hcode : I.code = registryBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (registrySelBytes 11)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (registrySelBytes 11) rfl hsel
  obtain ⟨_, _, rd⟩ := registryReachIdsBody (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) hcode hsz hsize hsel
  have hd : dispatchMsg contract I.calldata = some idsTransition :=
    registryDispatch_ids (selIs_exclusive (by native_decide) hsel) (selIs_exclusive (by native_decide) hsel)
      (selIs_exclusive (by native_decide) hsel) (selIs_exclusive (by native_decide) hsel)
      (selIs_exclusive (by native_decide) hsel) (selIs_exclusive (by native_decide) hsel)
      (selIs_exclusive (by native_decide) hsel) (selIs_exclusive (by native_decide) hsel)
      (selIs_exclusive (by native_decide) hsel) (selIs_exclusive (by native_decide) hsel)
      (selIs_exclusive (by native_decide) hsel) hsel
  have hmemsize : (registryDispatchMem 8).size = 32 := dispatchMem_size 8 (by decide)
  by_cases hshort : I.calldata.size < 36
  · have rd1 := registryBlocks.registry_block_1498_taken (by simp) (guard_short hsize hshort) (by jump_dest) rd
    have rd2 := registryBlocks.registry_block_1661 (by simp) rd1
    exact RDrev.reEquivDecodingFailed hcode rd2 hd (idsDecode_short hsz hshort)
  have hsz36 : 36 ≤ I.calldata.size := by omega
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · have rd1 := registryBlocks.registry_block_1498_taken (by simp) (guard_wv hwv) (by jump_dest) rd
    have rd2 := registryBlocks.registry_block_1661 (by simp) rd1
    exact RDrev.reEquivOfDispatch hcode hd
      (fun _ => by rw [idsBody_eq]; exact bodyReverts_nonPayable (by simpa [initState] using hwv)) rd2
  have rd1 := registryBlocks.registry_block_1498_fallthrough (by simp) (guard_ok hwv hsz36 hsize) rd
  have hdec := idsDecode_ok (I := I) hsz36
  have hcv : evalExpr? config (frame (idsStore I)) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (.binary .eq (.env .callvalue) (.intLit 0)) = .ok (.bool true) :=
    evalCallvalueEq_true (by simpa [initState] using hwv)
  have hlen := idsLength_initState (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
  have hidx : evalExpr? config (frame (idsStore I)) (initState σ σ₀ (Sat256.ofUInt256 g) A I) (.var "arg0") =
      .ok (.int (Int.ofNat (argWord I).toNat)) :=
    evalVar _ _ "arg0" _ (store_get_self _ _ _)
  by_cases hlt : (argWord I).toNat < (solcSlotWordAt (UInt256.ofNat 2) σ I).toNat
  · obtain ⟨_, _, rd2⟩ := registryBlocks.registry_block_1508_fallthrough (by simp)
      (by rw [slotWord_eq, ult_one hlt]; decide) rd1
    simp only [registryBlocks.registry_block_1508_fallthrough_stack] at rd2
    have rd3 := registryBlocks.registry_block_1521 (by simp) rd2
    rw [ulit_toNat' 64 (by decide), ulit_toNat' 32 (by decide),
      toByteArray_write_read_back_of_gap _ (registryDispatchMem 8) 64
        (by rw [hmemsize]; exact lt_usize _ (by decide)), slotWord_eq] at rd3
    have hbody : ExecTransitionBody fork config contract (initState σ σ₀ (Sat256.ofUInt256 g) A I) (idsStore I)
        idsTransition.body
        (.returned (frame (idsStore I)) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          (some [uint256Value (solcSlotWordAt (UInt256.ofNat 3 + argWord I) σ I)])) := by
      rw [idsBody_eq]
      refine ExecFuncBody.execBlockRet ((ABlock.start.requireStep hcv).returns ?_)
      rw [evalExpr_storage_vyper_uint256_backend (hbackend := rfl)
          (er := { base := "ids", steps := [.aindex (.int (Int.ofNat (argWord I).toNat))] })
          (physicalSlot := UInt256.ofNat 2 + UInt256.ofNat 1 +
            UInt256.ofNat ((keyValueToWord (.int (Int.ofNat (argWord I).toNat))).toNat * 1)) (hbase := by simp)
          (her := evalStorageRef_aindex_ok hidx (by show storageTypeAt? contract.storage _ = _; decide) ⟨_, rfl⟩ hlen hlt)
          (hty := rfl)
          (hcheck := vyperCheckRef_aindex_ok (hbounds := rfl) (hanchor := rfl)
            (by rw [storageLoad_initState_ofUInt256_solcSlotWordAt]; exact hlt))
          (hloc := rfl),
        storageLoad_initState_ofUInt256_solcSlotWordAt, idsSlot_eq]
    exact rd3.reEquivExecution hcode hd hdec hbody (returnEquiv_of_encode (uint256ReturnEncoding _))
  · obtain ⟨_, _, rd2⟩ := registryBlocks.registry_block_1508_taken (by simp)
      (by rw [slotWord_eq, ult_zero (by show (solcSlotWordAt (UInt256.ofNat 2) σ I).toNat ≤ (argWord I).toNat; omega)]; decide)
      (by jump_dest) rd1
    have rd3 := registryBlocks.registry_block_1661 (by simp [registryBlocks.registry_block_1508_taken_stack]) rd2
    refine RDrev.reEquivExecutionRevert hcode rd3 hd hdec ?_
    rw [idsBody_eq]
    exact ExecFuncBody.execBlockRevert (ExecBlock.consNormal (ExecStmt.requireTrue hcv)
      (ExecBlock.consRevert (ExecStmt.returnRevert (by
        rw [evalExprs?, evalExpr_storage_revert (by simp)
          (evalStorageRef_aindex_revert hidx (by show storageTypeAt? contract.storage _ = _; decide) ⟨_, rfl⟩ hlen (by omega))]
        rfl))))

end Tests.Pipeline.VyperRegistry
