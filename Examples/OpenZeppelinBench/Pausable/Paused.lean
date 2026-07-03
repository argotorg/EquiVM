import Examples.OpenZeppelinBench.Pausable.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace OpenZeppelinBench.Pausable

/-! ## `paused()` -/

abbrev pausedReturnWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.isZero (UInt256.isZero (pausedWord σ I))

theorem pausablePausedBodyReturns (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hlocals : locals.get? "_paused" = none) :
    ExecTransitionBody config contract evm locals pausedTransition.body
      (.returned { contract := contract, locals := locals } evm
        (some [(wordToElem .bool
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) ⟨255⟩))])) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      have her : evalStorageRef config { contract := contract, locals := locals } evm pausedRef =
          .ok { base := "_paused", steps := [] } := by
        simp [evalStorageRef, evalStorageRefSteps, pausedRef, EvalResult.bind, pure, bind]
      have hty : storageTypeAt? contract.storage
          ({ base := "_paused", steps := [] } : EvaledStorageRef) = some (.elem .bool) := by
        decide
      rw [evalExpr_storage_scalar (t := .bool) (hbase := hlocals) (her := her)
        (hty := hty) (hloc := by rfl), pausableStorageLocLoad_bool_offset0])

theorem pausableX_paused {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD pausableBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨99⟩ [pausableSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret pausableBenchBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (pausedReturnWord σ I)) := by
  obtain ⟨_, _, rd99⟩ := hreach
  have rd101 := evm_run rd99 with [jumpdest, push0]
  obtain ⟨_, _, rd102₀⟩ := rd101.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd102⟩ :
      ∃ k C, RD pausableBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨102⟩
        [pausedRawWord σ I, pausableSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [pausedRawWord, initState] using rd102₀⟩
  have rd105₀ := evm_run rd102 with [push1 ⟨255⟩, and]
  have hmask : UInt256.land ⟨255⟩ (pausedRawWord σ I) = pausedWord σ I := by
    rw [Reasoning.Theory.u256_land_comm]
    rfl
  have rd105 := rd105₀
  rw [hmask] at rd105
  exact evm_run rd105 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost
      solcFreePtrMem_mload64
      (by decide) (by evm_ov),
    swap1, iszero, iszero, dup2,
    raw mstore 6 (solcReturnMem (pausedReturnWord σ I)) (UInt256.ofNat 5)
      (by decide) mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]
        rfl)
      (by decide) (by evm_ov),
    push1 ⟨32⟩, add, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by decide)
      mem_cost
      (solcReturnMem_mload64 (pausedReturnWord σ I))
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray (pausedReturnWord σ I)) (by decide)
      mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show (UInt256.sub ((⟨32⟩ : UInt256) + ⟨128⟩) ⟨128⟩).toNat = 32 from by decide]
        simpa using solcReturnMem_read128 (pausedReturnWord σ I))
      (by evm_ov)]

theorem pausablePausedSelector_size {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x5c, 0x97, 0x5a, 0xbb]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x5c, 0x97, 0x5a, 0xbb]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem pausableDispatch_paused {cd : ByteArray}
    (hsel : ((⟨#[0x5c, 0x97, 0x5a, 0xbb]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg contract cd = some pausedTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0x5c, 0x97, 0x5a, 0xbb]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [guardedWhenNotPausedTransition, guardedWhenPausedTransition, pauseTransition])
    (post := [unpauseTransition]) rfl rfl ?_
    (by rw [selectorOf, pausedSelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · rw [selectorOf, guardedWhenNotPausedSelectorBytes, hcd]; decide
  · rw [selectorOf, guardedWhenPausedSelectorBytes, hcd]; decide
  · rw [selectorOf, pauseSelectorBytes, hcd]; decide

theorem pausableDecode_paused {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldata (pausedTransition.params.map Param.name)
      (transitionSignature pausedTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldata [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem pausablePausedBody {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = pausableBenchBytecode) (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x5c, 0x97, 0x5a, 0xbb]⟩)
    (hreach : ∃ k C, RD pausableBenchBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨99⟩
      [pausableSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := pausablePausedSelector_size hsel
  have hd := pausableDispatch_paused (cd := I.calldata) hsel
  have hdec := pausableDecode_paused (I := I) hsz
  have hword : pausedRawWord σ_evm I = pausedRawWord σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨0⟩ ⟨0⟩
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        pausedTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(wordToElem .bool (pausedWord σ_solm I))])) := by
    simpa [pausedRawWord, pausedWord, initState, Solm.EVM.storageLoad, State.lookupAccount] using
      pausablePausedBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (by simp only [initState]; exact hwv) (by simp)
  have hretVal :
      (some [wordToElem .bool (pausedWord σ_solm I)] : Option (List Value)) =
        some [wordToElem .bool (pausedWord σ_evm I)] := by
    simp [pausedWord, hword.symm]
  have henc :
      returnEquiv (UInt256.toByteArray (pausedReturnWord σ_evm I))
        (some [wordToElem .bool (pausedWord σ_evm I)]) pausedTransition.returnType := by
    simpa [pausedTransition] using
      returnEquiv_of_encode (abit := boolTy) (rv := wordToElem .bool (pausedWord σ_evm I))
        (o := UInt256.toByteArray (pausedReturnWord σ_evm I))
        (by simpa [pausedWord, pausedReturnWord] using
          boolWordReturnEncoding (pausedRawWord σ_evm I))
  exact (pausableX_paused (g := Sat256.ofUInt256 g) hreach)
    |>.reEquivExecutionTransport hcode hd hdec hbody
      hretVal hAccounts henc

end OpenZeppelinBench.Pausable
