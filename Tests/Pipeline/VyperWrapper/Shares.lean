import Tests.Pipeline.VyperWrapper.Helpers

variable {fork : Ethereum.Fork}

/-!
# Wrapper `shares(address)`

Dispatcher bucket 2, arm entry pc 1681: the guard, the address validation, then
`keccak256(1 ++ arg)`, `SLOAD` into offset 96 and `RETURN`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
open Reasoning.VyperImmutables

namespace Tests.Pipeline.VyperWrapper

set_option maxRecDepth 2000000

theorem sharesBody_eq : sharesTransition.body =
    [.require (.binary .eq (.env .callvalue) (.intLit 0)),
     .return [.storage { base := "shares", steps := [.mindex (.var "arg0")] }]] := by rfl

abbrev sharesStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "arg0" (.address (AccountAddress.ofNat (argWord I).toNat))

theorem sharesDecode_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size)
    (hcanon : (argWord I).toNat < EVM.addressModulus) :
    config.externalABI.decodeCalldata? (sharesTransition.params.map Param.name)
      (transitionSignature sharesTransition).paramTypes I.calldata = some (sharesStore I) := by
  rw [argWord_eq] at hcanon
  simpa [config, contract, Syntax.contractSyntax, sharesTransition, sharesStore, argWord_eq] using
    decodeCalldataWithMode_vyper_address_ok (cd := I.calldata) (x := "arg0") hsz36 hcanon

theorem sharesDecode_short {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    config.externalABI.decodeCalldata? (sharesTransition.params.map Param.name)
      (transitionSignature sharesTransition).paramTypes I.calldata = none := by
  simpa [config, contract, Syntax.contractSyntax, sharesTransition] using
    decodeCalldataWithMode_vyper_address_none_short (cd := I.calldata) (x := "arg0") hsz hshort

theorem sharesDecode_noncanon {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size)
    (hnc : ¬ (argWord I).toNat < EVM.addressModulus) :
    config.externalABI.decodeCalldata? (sharesTransition.params.map Param.name)
      (transitionSignature sharesTransition).paramTypes I.calldata = none := by
  rw [argWord_eq] at hnc
  simpa [config, contract, Syntax.contractSyntax, sharesTransition] using
    decodeCalldataWithMode_vyper_address_none_noncanon (cd := I.calldata) (x := "arg0") hsz36 hnc

/-- The argument at offset 64 over the dispatcher memory, and the hash scratch over it. -/
abbrev shM1 (I : ExecutionEnv) : ByteArray := (argWord I).toByteArray.write 0 (wrapperDispatchMem 2) 64 32
abbrev shH (I : ExecutionEnv) : ByteArray :=
  (UInt256.ofNat 1).toByteArray.write 0 ((argWord I).toByteArray.write 0 (shM1 I) 32 32) 0 32

theorem shM1_size (I : ExecutionEnv) : (shM1 I).size = 96 :=
  toByteArray_write32_size_of_ge _ _ 64 32 96 (dispatchMem_size 2 (by decide)) (by omega) (lt_usize _ (by decide)) rfl

theorem shH_size (I : ExecutionEnv) : (shH I).size = 96 := by
  have h1 : ((argWord I).toByteArray.write 0 (shM1 I) 32 32).size = 96 := by
    rw [byteArray_write_size_of_inBounds _ _ _ _ (by rw [toByteArray_size]) (by rw [shM1_size] <;> omega)]
    exact shM1_size I
  rw [byteArray_write_size_of_inBounds _ _ _ _ (by rw [toByteArray_size]) (by rw [h1] <;> omega)]
  exact h1

/-- `shares(address)`: the theorem `Correct.lean` routes selector 4 to. -/
theorem wrapperSharesBody {σ σ₀ A I} {g : UInt256} (imms : Store) (hfit : immutablesFit contract imms)
    (hwf : storageWF σ I)
    (hcode : I.code = immutableLayout.deployed wrapperBytecode imms) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (wrapperSelBytes 4)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I (restrictImmutables contract imms) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (wrapperSelBytes 4) rfl hsel
  have hcode' : I.code = wrapperBytecode ++ immutableLayout.suffixWords (wordsOf imms) := by
    rw [hcode, deployed_of_fit hfit]
  obtain ⟨_, _, rd⟩ := wrapperReachSharesBody (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) hcode' hsz hsize hsel
  have hd : dispatchMsg contract I.calldata = some sharesTransition :=
    wrapperDispatch_shares (selIs_exclusive (by native_decide) hsel) (selIs_exclusive (by native_decide) hsel)
      (selIs_exclusive (by native_decide) hsel) (selIs_exclusive (by native_decide) hsel) hsel
  by_cases hshort : I.calldata.size < 36
  · have rd1 := wrapperBlocks.wrapper_block_1681_taken (by simp) (guard_short hsize hshort)
      (by apply D_J_contains_append_left; jump_dest) rd
    have rd2 := wrapperBlocks.wrapper_block_1760 (by simp) rd1
    exact RDrev.reEquivDecodingFailed hcode' rd2 hd (sharesDecode_short hsz hshort)
  have hsz36 : 36 ≤ I.calldata.size := by omega
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · have rd1 := wrapperBlocks.wrapper_block_1681_taken (by simp) (guard_wv hwv)
      (by apply D_J_contains_append_left; jump_dest) rd
    have rd2 := wrapperBlocks.wrapper_block_1760 (by simp) rd1
    exact RDrev.reEquivOfDispatch hcode' hd
      (fun _ => by rw [sharesBody_eq]; exact bodyReverts_nonPayable (by simpa [initState] using hwv)) rd2
  have rd1 := wrapperBlocks.wrapper_block_1681_fallthrough (by simp) (guard_ok hwv hsz36 hsize) rd
  by_cases hcanon : (argWord I).toNat < EVM.addressModulus
  swap
  · have rd2 := wrapperBlocks.wrapper_block_1691_taken (by simp)
      (by intro h; exact hcanon (u256_lt_addressModulus_of_shiftRight160_zero _ h))
      (by apply D_J_contains_append_left; jump_dest) rd1
    have rd3 := wrapperBlocks.wrapper_block_1760 (by simp [wrapperBlocks.wrapper_block_1691_taken_stack]) rd2
    exact RDrev.reEquivDecodingFailed hcode' rd3 hd (sharesDecode_noncanon hsz36 hcanon)
  have rd2 := wrapperBlocks.wrapper_block_1691_fallthrough (by simp) (u256_shiftRight160_zero_of_lt _ hcanon) rd1
  simp only [wrapperBlocks.wrapper_block_1691_fallthrough_stack] at rd2
  have rd3 := wrapperBlocks.wrapper_block_1702 (by simp) rd2
  simp only [ulit_toNat' 64 (by decide), ulit_toNat' 32 (by decide), ulit_toNat' 96 (by decide),
    show (⟨0⟩ : UInt256).toNat = 0 from rfl] at rd3
  rw [memLoad_write_back _ _ 64 (by decide) (by rw [dispatchMem_size 2 (by decide)]; exact lt_usize _ (by decide)),
    keccak_addr_over (shM1 I) (by rw [shM1_size]; omega) (argWord I) hcanon, slotWord_eq,
    toByteArray_write_read_back_of_gap _ (shH I) 96 (by rw [shH_size]; exact lt_usize _ (by decide))] at rd3
  have hbody : ExecTransitionBody fork config contract (initState σ σ₀ (Sat256.ofUInt256 g) A I) (sharesStore I)
      sharesTransition.body
      (.returned (frame imms (sharesStore I)) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (some [uint256Value (solcSlotWordAt (sharesSlot (AccountAddress.ofNat (argWord I).toNat)) σ I)]))
      (restrictImmutables contract imms) := by
    rw [sharesBody_eq]
    refine ExecFuncBody.execBlockRet
      ((ABlock.start.requireStep (evalCallvalueEq_true (by simpa [initState] using hwv))).returns ?_)
    have her : evalStorageRef config (frame imms (sharesStore I)) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        { base := "shares", steps := [.mindex (.var "arg0")] } =
        .ok { base := "shares", steps := [.mindex (.address (AccountAddress.ofNat (argWord I).toNat))] } := by
      simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, sharesStore, valueToKey?,
        EvalResult.seqList, EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?]
    rw [evalExpr_storage_vyper_uint256_backend (hbackend := rfl) (hcheck := by rfl)
        (physicalSlot := sharesSlot (AccountAddress.ofNat (argWord I).toNat))
        (hbase := by simp [sharesStore]) (her := her)
        (hty := by simp [storageTypeAt?, storageTypeStep?, contract, Syntax.contractSyntax])
        (hloc := rfl),
      storageLoad_initState_ofUInt256_solcSlotWordAt]
  exact rd3.reEquivExecution hcode' hd (sharesDecode_ok hsz36 hcanon) hbody
    (returnEquiv_of_encode (uint256ReturnEncoding _))

end Tests.Pipeline.VyperWrapper
