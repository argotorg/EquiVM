import Benchmarks.Auction.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Auction

theorem auctionDispatch_paused {I : ExecutionEnv} (hsel : selIs I (auctionSelBytes 5)) :
    dispatchMsg auctionContract I.calldata = some pausedGetter := by
  apply dispatchMsg_eq_some_of_split (hfallback := by rfl)
    (pre := [initializeTransition, createBidTransition, settleAndCreateTransition,
      settleAuctionTransition, pauseTransition, unpauseTransition, setTimeBufferTransition,
      setReservePriceTransition, setMinBidIncTransition, transferOwnershipTransition,
      renounceOwnershipTransition, ownerGetter])
    (post := [nounsGetter, wethGetter, timeBufferGetter, reservePriceGetter, minBidIncGetter,
      durationGetter, auctionGetter])
    (ti := pausedGetter)
    (htr := by rfl)
  · intro t ht
    have hcd : I.calldata.extract 0 4 = auctionSelBytes 5 := (byteArray_eq_of_beq hsel).symm
    simp at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl
    all_goals
      simp [selectorOf, initializeSelectorBytes, createBidSelectorBytes,
        settleAndCreateSelectorBytes, settleAuctionSelectorBytes, pauseSelectorBytes,
        unpauseSelectorBytes, setTimeBufferSelectorBytes, setReservePriceSelectorBytes,
        setMinBidIncSelectorBytes, transferOwnershipSelectorBytes, renounceOwnershipSelectorBytes,
        ownerSelectorBytes, hcd, auctionSelBytes]
      native_decide
  · rw [selectorOf, pausedSelectorBytes]
    simpa [selIs, auctionSelBytes] using hsel

theorem auctionDecode_paused {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode auctionConfig.abiDecodeMode (pausedGetter.params.map Param.name)
      (transitionSignature pausedGetter).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode auctionConfig.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem auctionReachPausedBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = auctionBytecode)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (auctionSelBytes 5)) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨466⟩
      [auctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsel' : ((⟨#[0x5c, 0x97, 0x5a, 0xbb]⟩ : ByteArray) == I.calldata.extract 0 4) = true := by
    simpa [selIs, auctionSelBytes] using hsel
  have hword : auctionSelWord I = ⟨0x5c975abb⟩ :=
    auctionSelWord_eq_of_beq I hsz 0x5c 0x97 0x5a 0xbb ⟨0x5c975abb⟩
      (by decide) hsel'
  obtain ⟨_, _, hsplit⟩ := auctionReachRootSplit (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz hsize
  have hroot : UInt256.gt (armSelNat auctionBytecode auctionSplitPc) (auctionSelWord I) ≠
      ⟨0⟩ := by
    rw [hword]
    decide
  have h157 := RD.selectorSplitTakenAuto hsplit auctionSplitWellFormed hroot
    (by jump_dest) (by simp)
  have h158 := h157.jumpdest (by decide) (by simp)
  have hlower : UInt256.gt (armSelNat auctionBytecode auctionLowerSplitPc) (auctionSelWord I) =
      ⟨0⟩ := by
    rw [hword]
    decide
  have h169 := RD.selectorSplitNotTakenAuto h158 auctionLowerSplitWellFormed hlower (by simp)
  have htake :
      UInt256.eq
        (armSelNat auctionBytecode (nthArmPc auctionBytecode auctionLowerMidFirstArmPc 0))
        (auctionSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    decide
  have hrd := h169.selectorArmTakenAuto (auctionLowerMidArmsWellFormed 0 (by omega)) htake
    (by jump_dest) (by simp)
  exact ⟨_, _, by
    simpa [auctionLowerMidFirstArmPc, nthArmPc, armTgt, pushAt] using hrd⟩

theorem auctionX_paused_callvalue_ne {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨466⟩
      [auctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd466⟩ := hreach
  exact evm_run rd466 with [
    jumpdest, callvalue, dup1, iszero, push2 ⟨477⟩,
    jumpiNT (isZero_eq_zero_of_ne hwv),
    push0, dup1, raw rev 0 (by decide) mem_cost (by evm_ov)]

theorem auctionX_paused {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨466⟩
      [auctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hwv : I.weiValue = ⟨0⟩) :
    RDret auctionBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (UInt256.isZero (UInt256.isZero (auctionPausedWord σ I)))) := by
  obtain ⟨_, _, rd466⟩ := hreach
  have rd481 := evm_run rd466 with [
    jumpdest, callvalue, dup1, iszero, push2 ⟨477⟩,
    jumpiT (by rw [hwv]; decide) (by jump_dest),
    jumpdest, pop, push1 ⟨51⟩]
  obtain ⟨_, _, rd482⟩ := rd481.sload (by decide) (by evm_ov)
  have rd496 := evm_run rd482 with [
    push1 ⟨255⟩, and, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    swap1, iszero, iszero, dup2,
    raw mstore 6
      (solcReturnMem
        (UInt256.isZero (UInt256.isZero (UInt256.land ⟨255⟩ (auctionSlotWord ⟨51⟩ σ I)))))
      (UInt256.ofNat 5) (by decide)
      mem_cost
      (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]; rfl)
      (by decide) (by evm_ov),
    push1 ⟨32⟩, add, push2 ⟨318⟩, jump (by jump_dest)]
  have hret := evm_run rd496 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by decide)
      mem_cost (solcReturnMem_mload64
        (UInt256.isZero (UInt256.isZero (UInt256.land ⟨255⟩ (auctionSlotWord ⟨51⟩ σ I)))))
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0
      (UInt256.toByteArray
        (UInt256.isZero (UInt256.isZero (UInt256.land ⟨255⟩ (auctionSlotWord ⟨51⟩ σ I)))))
      (by decide)
      mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show (UInt256.sub ((⟨32⟩ : UInt256) + ⟨128⟩) ⟨128⟩).toNat = 32 from by decide,
          solcReturnMem_read128])
      (by evm_ov)]
  have hmask : UInt256.land ⟨255⟩ (auctionSlotWord ⟨51⟩ σ I) = auctionPausedWord σ I := by
    rw [auctionPausedWord, u256_land_comm]
  simpa [hmask] using hret

theorem auctionPausedBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (_hcode : I.code = auctionBytecode)
    (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (_hsel : selIs I (auctionSelBytes 5))
    (_hAccounts : accountMapEquiv σ_evm σ_solm) :
    RuntimeCase (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) g := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (auctionSelBytes 5) rfl _hsel
  have hdispatch := auctionDispatch_paused _hsel
  have hdecode := auctionDecode_paused (I := I) hsz
  have hreach := auctionReachPausedBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    _hcode hsz _hsize _hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · have hword : auctionPausedWord σ_evm I = auctionPausedWord σ_solm I := by
      unfold auctionPausedWord auctionSlotWord
      rw [accountMapEquiv_storage_findD _hAccounts I.codeOwner ⟨51⟩ ⟨0⟩]
    have hval :
        some [wordToElem .bool (auctionPausedWord σ_solm I)] =
          some [wordToElem .bool (auctionPausedWord σ_evm I)] := by
      rw [hword]
    have hbody :
        ExecTransitionBody auctionConfig auctionContract
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ pausedGetter.body
          (.returned { contract := auctionContract, locals := ∅ }
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            (some [wordToElem .bool (auctionPausedWord σ_solm I)])) := by
      simpa [pausedGetter, auctionPausedWord, auctionSlotWord, initState,
        Solm.EVM.storageLoad, State.lookupAccount] using
        auctionBoolGetterBodyReturns
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
          (ref := pausedRef) (er := ({ base := "_paused", steps := [] } : EvaledStorageRef))
          (slot := ⟨51⟩)
          (by simp only [initState]; exact hwv) (by simp [pausedRef])
          (by simp [evalStorageRef, evalStorageRefSteps, pausedRef, EvalResult.bind, pure, bind])
          (by decide) (by rfl)
    have henc :
        returnEquiv (UInt256.toByteArray (UInt256.isZero (UInt256.isZero (auctionPausedWord σ_evm I))))
          (some [wordToElem .bool (auctionPausedWord σ_evm I)])
          pausedGetter.returnType := by
      rw [pausedGetter]
      exact returnEquiv_of_encode
        (by simpa [boolTy, auctionPausedWord] using
          boolWordReturnEncoding (auctionSlotWord ⟨51⟩ σ_evm I))
    exact (auctionX_paused hreach hwv).reEquivExecutionTransport _hcode hdispatch hdecode
      hbody hval _hAccounts henc
  · have hbody :
        ExecTransitionBody auctionConfig auctionContract
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ pausedGetter.body
          .reverted := by
      simpa [pausedGetter, nonpayable] using
        bodyReverts_nonPayable (cfg := auctionConfig) (contract := auctionContract)
          (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (locals := ∅)
          (rest := [.return [(.storage pausedRef)]]) (by simpa [initState] using hwv)
    exact (auctionX_paused_callvalue_ne hreach hwv).reEquivExecutionRevert _hcode
      hdispatch hdecode hbody

end Auction
