import Benchmarks.CompoundIII.CometRewards.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.CompoundIII.CometRewards

/-! ## `governor()` getter -/

def governorWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)

abbrev governorReturnWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (governorWord σ I) solcAddrMask

abbrev calldataFrame (evm : EVM.State) (locals : Store) : Frame :=
  Frame.mk contract (locals.insert "__calldata" (.bytes evm.executionEnv.calldata))

theorem cometRewardsGovernorBodyReturns (evm : EVM.State) (locals : Store)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hlocals : locals.get? "governor" = none) :
    ExecTransitionBody config contract evm locals governorTransition.body
      (.returned (calldataFrame evm locals) evm
        (some [(.address (AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
            solcAddrMask).toNat))])) := by
  refine ExecFuncBody.execBlockRet ?_
  simpa [governorTransition, externalEntryGuard, nonpayable, calldataSizeGuard] using
    (((ABlock.start.requireStep (evalCallvalueEq_true hwv)).letStep (by
      simp [evalExpr?, envValue, pure])).requireStep
        (cometRewardsCalldataGuard_true evm locals hsize)).returns (by
      have her : evalStorageRef config
          (calldataFrame evm locals)
          evm governorRef = .ok { base := "governor", steps := [] } := by
        simp [evalStorageRef, evalStorageRefSteps, governorRef, EvalResult.bind, pure, bind]
      have hty : storageTypeAt? contract.storage
          ({ base := "governor", steps := [] } : EvaledStorageRef) = some (.elem .address) := by
        decide
      rw [evalExpr_storage_scalar (t := .address)
        (hbase := by
          change (locals.insert "__calldata" (.bytes evm.executionEnv.calldata)).get?
              "governor" = none
          rw [store_get_ne locals (k := "__calldata") (a := "governor")
            (.bytes evm.executionEnv.calldata) (by decide)]
          exact hlocals)
        (her := her)
        (hty := hty) (hloc := by rfl), cometRewardsStorageLocLoad_address_offset0])

theorem cometRewardsGovernorBodyRevertsHuge (evm : EVM.State) (locals : Store)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hbig : 2 ^ 255 + 4 ≤ evm.executionEnv.calldata.size) :
    ExecTransitionBody config contract evm locals governorTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [governorTransition, externalEntryGuard, nonpayable, calldataSizeGuard] using
    (((ABlock.start.requireStep (evalCallvalueEq_true hwv)).letStep (by
      simp [evalExpr?, envValue, pure])).requireRevert
        (cometRewardsCalldataGuard_false evm locals hbig))

theorem cometRewardsGovernorSelector_size {I : ExecutionEnv}
    (hsel : selIs I (cometRewardsSelBytes 1)) :
    4 ≤ I.calldata.size :=
  calldata_size_ge_of_selIs I (cometRewardsSelBytes 1) rfl hsel

theorem cometRewardsDispatch_governor {cd : ByteArray}
    (hsel : (cometRewardsSelBytes 1 == cd.extract 0 4) = true) :
    dispatchMsg contract cd = some governorTransition := by
  have hcd : cd.extract 0 4 = cometRewardsSelBytes 1 :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [claimTransition, claimToTransition, getRewardOwedTransition])
    (post := [rewardConfigTransition, rewardsClaimedTransition, setRewardConfigTransition,
      setRewardConfigWithMultiplierTransition, setRewardsClaimedTransition,
      transferGovernorTransition, withdrawTokenTransition])
    rfl rfl ?_ (by rw [selectorOf, governorSelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · rw [selectorOf, claimSelectorBytes, hcd]
    decide
  · rw [selectorOf, claimToSelectorBytes, hcd]
    decide
  · rw [selectorOf, getRewardOwedSelectorBytes, hcd]
    decide

theorem cometRewardsDecode_governor {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (governorTransition.params.map Param.name)
      (transitionSignature governorTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldataWithMode_empty_ok hsz

theorem cometRewardsGovernorCalldataCheckOk {I : ExecutionEnv}
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4) :
    UInt256.slt
        ((UInt256.ofNat I.calldata.size) + (UInt256.lnot (⟨3⟩ : UInt256)))
        ⟨0⟩ = ⟨0⟩ := by
  change UInt256.slt
      (UInt256.add (UInt256.ofNat I.calldata.size) (UInt256.lnot (⟨3⟩ : UInt256)))
      ⟨0⟩ = ⟨0⟩
  rw [cometRewardsCalldataSizeAddNot3_eq_sub4 hsz hsize]
  simpa using
    solcCalldataStaticLenCheckOk (sz := I.calldata.size) (words := 0)
      (by omega) hhi hsize

theorem cometRewardsGovernorCalldataCheckHuge {I : ExecutionEnv}
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    UInt256.slt
        ((UInt256.ofNat I.calldata.size) + (UInt256.lnot (⟨3⟩ : UInt256)))
        ⟨0⟩ = ⟨1⟩ := by
  change UInt256.slt
      (UInt256.add (UInt256.ofNat I.calldata.size) (UInt256.lnot (⟨3⟩ : UInt256)))
      ⟨0⟩ = ⟨1⟩
  rw [cometRewardsCalldataSizeAddNot3_eq_sub4 hsz hsize]
  simpa using
    solcCalldataStaticLenCheckHuge (sz := I.calldata.size) (words := 0)
      hbig hsize (by norm_num)

theorem cometRewardsX_governor {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) governorPc
      (dispatchArmMidStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    RDret cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (governorReturnWord σ I)) := by
  have hslt := cometRewardsGovernorCalldataCheckOk (I := I) hsz hsize hhi
  obtain ⟨_, _, rd2717⟩ := hreach
  have rd2726 := evm_run rd2717 with [
    jumpdest, pop, pop, pop, callvalue]
  rw [hwv] at rd2726
  have rd2732 := evm_run rd2726 with [
    push2 ⟨670⟩, jumpiNT (by decide),
    dup2, push1 ⟨3⟩, not, calldatasize, add, slt]
  rw [hslt] at rd2732
  have rd2738 := evm_run rd2732 with [
    push2 ⟨670⟩, jumpiNT (by decide), swap1]
  obtain ⟨_, _, rd2739⟩ := rd2738.sload (by decide) (by evm_ov)
  have rd2754 := evm_run rd2739 with [
    swap1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, swap1, swap2, and, dup2,
    raw mstore 6 (solcReturnMem (governorReturnWord σ I)) (UInt256.ofNat 5)
      (by decide) mem_cost
      (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
            solcAddrMask from by decide]
        rfl)
      (by decide) (by evm_ov),
    push1 ⟨32⟩, swap1]
  exact evm_run rd2754 with [
    raw ret 0 (UInt256.toByteArray (governorReturnWord σ I)) (by decide)
      mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show (⟨32⟩ : UInt256).toNat = 32 from by decide]
        exact solcReturnMem_read128 (governorReturnWord σ I))
      (by evm_ov)]

theorem cometRewardsX_governor_huge {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) governorPc
      (dispatchArmMidStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt := cometRewardsGovernorCalldataCheckHuge (I := I) hsz hsize hbig
  obtain ⟨_, _, rd2717⟩ := hreach
  have rd2726 := evm_run rd2717 with [
    jumpdest, pop, pop, pop, callvalue]
  rw [hwv] at rd2726
  have rd2732 := evm_run rd2726 with [
    push2 ⟨670⟩, jumpiNT (by decide),
    dup2, push1 ⟨3⟩, not, calldatasize, add, slt]
  rw [hslt] at rd2732
  exact evm_run rd2732 with [
    push2 ⟨670⟩, jumpiT (by decide) (by native_decide),
    jumpdest, pop, dup1,
    raw rev 0 (by decide) mem_cost (by evm_ov)]

/-- `governor()` body, reached at pc 2717. -/
theorem cometRewardsGovernorBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = cometRewardsBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (cometRewardsSelBytes 1))
    (hreach : ∃ k C, RD cometRewardsBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) governorPc
      (dispatchArmMidStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have _hperm : I.perm = true := hperm
  have hsz := cometRewardsGovernorSelector_size hsel
  have hd := cometRewardsDispatch_governor (cd := I.calldata) hsel
  have hdec := cometRewardsDecode_governor (I := I) hsz
  by_cases hhi : I.calldata.size < 2 ^ 255 + 4
  · have hword : governorWord σ_evm I = governorWord σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨0⟩ ⟨0⟩
    have hbody :
        ExecTransitionBody config contract
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
          governorTransition.body
          (.returned
            (calldataFrame (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅)
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            (some [(.address (AccountAddress.ofNat (governorReturnWord σ_solm I).toNat))])) := by
      simpa [governorWord, governorReturnWord, initState, Solm.EVM.storageLoad,
        State.lookupAccount] using
        cometRewardsGovernorBodyReturns
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
          (by simp only [initState]; exact hwv)
          (by simp only [initState]; exact hhi)
          (by simp)
    exact (cometRewardsX_governor (g := Sat256.ofUInt256 g) hwv hsz hsize hhi hreach)
      |>.reEquivExecutionTransport hcode hd hdec hbody
        (by simp [governorReturnWord, hword]) hAccounts
        (returnEquiv_of_encode
          (solcAddressReturnEncoding (addrTy := addr) rfl (governorWord σ_evm I)))
  · have hbig : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
    have hbody :
        ExecTransitionBody config contract
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
          governorTransition.body .reverted := by
      exact cometRewardsGovernorBodyRevertsHuge
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (by simp only [initState]; exact hwv)
        (by simp only [initState]; exact hbig)
    exact (cometRewardsX_governor_huge (g := Sat256.ofUInt256 g) hwv hsz hsize hbig hreach)
      |>.reEquivExecutionRevert hcode hd hdec hbody

end Benchmarks.CompoundIII.CometRewards
