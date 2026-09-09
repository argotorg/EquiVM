import Benchmarks.Auction.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Auction

theorem auctionDispatch_duration {I : ExecutionEnv} (hsel : selIs I (auctionSelBytes 0)) :
    dispatchMsg auctionContract I.calldata = some durationGetter := by
  apply dispatchMsg_eq_some_of_split (hfallback := by rfl)
    (pre := [initializeTransition, createBidTransition, settleAndCreateTransition,
      settleAuctionTransition, pauseTransition, unpauseTransition, setTimeBufferTransition,
      setReservePriceTransition, setMinBidIncTransition, transferOwnershipTransition,
      renounceOwnershipTransition, ownerGetter, pausedGetter, nounsGetter, wethGetter,
      timeBufferGetter, reservePriceGetter, minBidIncGetter])
    (post := [auctionGetter])
    (ti := durationGetter)
    (htr := by rfl)
  · intro t ht
    have hcd : I.calldata.extract 0 4 = auctionSelBytes 0 := (byteArray_eq_of_beq hsel).symm
    simp at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp [selectorOf, initializeSelectorBytes, createBidSelectorBytes,
        settleAndCreateSelectorBytes, settleAuctionSelectorBytes, pauseSelectorBytes,
        unpauseSelectorBytes, setTimeBufferSelectorBytes, setReservePriceSelectorBytes,
        setMinBidIncSelectorBytes, transferOwnershipSelectorBytes, renounceOwnershipSelectorBytes,
        ownerSelectorBytes, pausedSelectorBytes, nounsSelectorBytes, wethSelectorBytes,
        timeBufferSelectorBytes, reservePriceSelectorBytes, minBidIncSelectorBytes, hcd,
        auctionSelBytes]
      native_decide
  · rw [selectorOf, durationSelectorBytes]
    simpa [selIs, auctionSelBytes] using hsel

theorem auctionDecode_duration {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode auctionConfig.abiDecodeMode (durationGetter.params.map Param.name)
      (transitionSignature durationGetter).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode auctionConfig.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem auctionReachDurationBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = auctionBytecode)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (auctionSelBytes 0)) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨287⟩
      [auctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsel' : ((⟨#[0x0f, 0xb5, 0xa6, 0xb4]⟩ : ByteArray) == I.calldata.extract 0 4) = true := by
    simpa [selIs, auctionSelBytes] using hsel
  have hword : auctionSelWord I = ⟨0x0fb5a6b4⟩ :=
    auctionSelWord_eq_of_beq I hsz 0x0f 0xb5 0xa6 0xb4 ⟨0x0fb5a6b4⟩
      (by native_decide) hsel'
  obtain ⟨_, _, hsplit⟩ := auctionReachRootSplit (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz hsize
  have hroot : UInt256.gt (armSelNat auctionBytecode auctionSplitPc) (auctionSelWord I) ≠
      ⟨0⟩ := by
    rw [hword]
    native_decide
  have h157 := auctionSelectorSplitTakenTo hsplit auctionSplitWellFormed hroot
      auctionRootSplitTargetPc
    (by jump_dest) (by simp)
  have h158 := h157.jumpdest (by native_decide) (by simp)
  have hlower : UInt256.gt (armSelNat auctionBytecode auctionLowerSplitPc) (auctionSelWord I) ≠
      ⟨0⟩ := by
    rw [hword]
    native_decide
  have h227 := auctionSelectorSplitTakenTo h158 auctionLowerSplitWellFormed hlower
      auctionLowerSplitTargetPc
    (by jump_dest) (by simp)
  have h228 := h227.jumpdest (by native_decide) (by simp)
  have htake :
      UInt256.eq
        (armSelNat auctionBytecode (nthArmPc auctionBytecode auctionLowerLowFirstArmPc 0))
        (auctionSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have hrd := h228.selectorArmTakenAuto (auctionLowerLowArmsWellFormed 0 (by omega)) htake
    (by jump_dest) (by simp)
  exact ⟨_, _, by
    simpa [auctionLowerLowFirstArmPc, nthArmPc, armTgt, pushAt] using hrd⟩

theorem auctionX_duration_callvalue_ne {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨287⟩
      [auctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd287⟩ := hreach
  exact evm_run rd287 with [
    jumpdest, callvalue, dup1, iszero, push2 ⟨298⟩,
    jumpiNT (isZero_eq_zero_of_ne hwv),
    push0, dup1, raw rev 0 (by native_decide) mem_cost (by evm_ov)]

theorem auctionX_duration {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨287⟩
      [auctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hwv : I.weiValue = ⟨0⟩) :
    RDret auctionBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (auctionSlotWord ⟨206⟩ σ I)) := by
  obtain ⟨_, _, rd287⟩ := hreach
  have rd305 := evm_run rd287 with [
    jumpdest, callvalue, dup1, iszero, push2 ⟨298⟩,
    jumpiT (by rw [hwv]; decide) (by jump_dest),
    jumpdest, pop, push2 ⟨308⟩, push1 ⟨206⟩]
  obtain ⟨_, _, rd306⟩ := rd305.sload (by native_decide) (by evm_ov)
  have rd308 := evm_run rd306 with [dup2, jump (by jump_dest)]
  have rd318 := evm_run rd308 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost
      solcFreePtrMem_mload64
      (by decide) (by evm_ov),
    swap1, dup2,
    raw mstore 6 (solcReturnMem (auctionSlotWord ⟨206⟩ σ I)) (UInt256.ofNat 5) (by native_decide)
      mem_cost
      (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]; rfl)
      (by decide) (by evm_ov),
    push1 ⟨32⟩, add]
  exact evm_run rd318 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by native_decide)
      mem_cost
      (solcReturnMem_mload64 (auctionSlotWord ⟨206⟩ σ I))
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray (auctionSlotWord ⟨206⟩ σ I)) (by native_decide)
      mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show (UInt256.sub ((⟨32⟩ : UInt256) + ⟨128⟩) ⟨128⟩).toNat = 32 from by decide,
          solcReturnMem_read128])
      (by evm_ov)]

theorem auctionDurationBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (_hcode : I.code = auctionBytecode)
    (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (_hsel : selIs I (auctionSelBytes 0))
    (_hAccounts : accountMapEquiv σ_evm σ_solm) :
    RuntimeCase (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) g := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (auctionSelBytes 0) rfl _hsel
  have hdispatch := auctionDispatch_duration _hsel
  have hdecode := auctionDecode_duration (I := I) hsz
  have hreach := auctionReachDurationBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    _hcode hsz _hsize _hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · have hword : auctionSlotWord ⟨206⟩ σ_evm I = auctionSlotWord ⟨206⟩ σ_solm I :=
      accountMapEquiv_storage_findD _hAccounts I.codeOwner ⟨206⟩ ⟨0⟩
    have hval :
        some [Value.int (Int.ofNat (auctionSlotWord ⟨206⟩ σ_solm I).toNat)] =
          some [Value.int (Int.ofNat (auctionSlotWord ⟨206⟩ σ_evm I).toNat)] := by
      rw [hword]
    have hbody :
        ExecTransitionBody auctionConfig auctionContract
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ durationGetter.body
          (.returned { contract := auctionContract, locals := ∅ }
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            (some [(.int (Int.ofNat (auctionSlotWord ⟨206⟩ σ_solm I).toNat))])) := by
      simpa [durationGetter, auctionSlotWord, initState, Solm.EVM.storageLoad,
        State.lookupAccount] using
        auctionUint256GetterBodyReturns
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
          (ref := durationRef) (er := ({ base := "duration", steps := [] } : EvaledStorageRef))
          (slot := ⟨206⟩)
          (by simp only [initState]; exact hwv) (by simp [durationRef])
          (by simp [evalStorageRef, evalStorageRefSteps, durationRef, EvalResult.bind, pure, bind])
          (by decide) (by rfl)
    have henc :
        returnEquiv (UInt256.toByteArray (auctionSlotWord ⟨206⟩ σ_evm I))
          (some [(.int (Int.ofNat (auctionSlotWord ⟨206⟩ σ_evm I).toNat))])
          durationGetter.returnType := by
      rw [durationGetter]
      exact returnEquiv_of_encode
        (by simpa [uint256] using uint256ReturnEncoding (auctionSlotWord ⟨206⟩ σ_evm I))
    exact (auctionX_duration hreach hwv).reEquivExecutionTransport _hcode hdispatch hdecode
      hbody hval _hAccounts henc
  · have hbody :
        ExecTransitionBody auctionConfig auctionContract
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ durationGetter.body
          .reverted := by
      simpa [durationGetter, nonpayable] using
        bodyReverts_nonPayable (cfg := auctionConfig) (contract := auctionContract)
          (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (locals := ∅)
          (rest := [.return [(.storage durationRef)]]) (by simpa only [initState] using hwv)
    exact (auctionX_duration_callvalue_ne hreach hwv).reEquivExecutionRevert _hcode hdispatch
      hdecode hbody

end Auction
