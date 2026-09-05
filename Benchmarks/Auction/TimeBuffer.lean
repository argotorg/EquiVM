import Benchmarks.Auction.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Auction

theorem auctionDispatch_timeBuffer {I : ExecutionEnv} (hsel : selIs I (auctionSelBytes 17)) :
    dispatchMsg auctionContract I.calldata = some timeBufferGetter := by
  apply dispatchMsg_eq_some_of_split (hfallback := by rfl)
    (pre := [initializeTransition, createBidTransition, settleAndCreateTransition,
      settleAuctionTransition, pauseTransition, unpauseTransition, setTimeBufferTransition,
      setReservePriceTransition, setMinBidIncTransition, transferOwnershipTransition,
      renounceOwnershipTransition, ownerGetter, pausedGetter, nounsGetter, wethGetter])
    (post := [reservePriceGetter, minBidIncGetter, durationGetter, auctionGetter])
    (ti := timeBufferGetter)
    (htr := by rfl)
  · intro t ht
    have hcd : I.calldata.extract 0 4 = auctionSelBytes 17 := (byteArray_eq_of_beq hsel).symm
    simp at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl
    all_goals
      simp [selectorOf, initializeSelectorBytes, createBidSelectorBytes,
        settleAndCreateSelectorBytes, settleAuctionSelectorBytes, pauseSelectorBytes,
        unpauseSelectorBytes, setTimeBufferSelectorBytes, setReservePriceSelectorBytes,
        setMinBidIncSelectorBytes, transferOwnershipSelectorBytes, renounceOwnershipSelectorBytes,
        ownerSelectorBytes, pausedSelectorBytes, nounsSelectorBytes, wethSelectorBytes, hcd,
        auctionSelBytes]
      native_decide
  · rw [selectorOf, timeBufferSelectorBytes]
    simpa [selIs, auctionSelBytes] using hsel

theorem auctionDecode_timeBuffer {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode auctionConfig.abiDecodeMode (timeBufferGetter.params.map Param.name)
      (transitionSignature timeBufferGetter).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode auctionConfig.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem auctionReachTimeBufferBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = auctionBytecode)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (auctionSelBytes 17)) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨880⟩
      [auctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsel' : ((⟨#[0xec, 0x91, 0xf2, 0xa4]⟩ : ByteArray) == I.calldata.extract 0 4) = true := by
    simpa [selIs, auctionSelBytes] using hsel
  have hword : auctionSelWord I = ⟨0xec91f2a4⟩ :=
    auctionSelWord_eq_of_beq I hsz 0xec 0x91 0xf2 0xa4 ⟨0xec91f2a4⟩
      (by decide) hsel'
  obtain ⟨kS, CS, hsplit⟩ := auctionReachRootSplit (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz hsize
  have hroot : UInt256.gt (armSelNat auctionBytecode auctionSplitPc) (auctionSelWord I) = ⟨0⟩ := by
    rw [hword]
    decide
  have h29 := RD.selectorSplitNotTakenAuto hsplit auctionSplitWellFormed hroot (by simp)
  have hupper : UInt256.gt (armSelNat auctionBytecode auctionUpperSplitPc) (auctionSelWord I) =
      ⟨0⟩ := by
    rw [hword]
    decide
  have h40 := RD.selectorSplitNotTakenAuto h29 auctionUpperSplitWellFormed hupper (by simp)
  have h40' : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I)
      auctionUpperMidFirstArmPc [auctionSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
    refine Exists.intro (kS + 5 + 5) ?_
    refine Exists.intro (CS + 22 + 22) ?_
    simpa [auctionUpperMidFirstArmPc, auctionUpperSplitPc, auctionSplitPc, selArmNextPc,
      armTgtWidth] using h40
  obtain ⟨_, _, h40rd⟩ := h40'
  have heq0 : ∀ j, j < 2 →
      UInt256.eq (armSelNat auctionBytecode
        (nthArmPc auctionBytecode auctionUpperMidFirstArmPc j)) (auctionSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · rw [hword]
      decide
    · rw [hword]
      decide
  have htake :
      UInt256.eq
        (armSelNat auctionBytecode (nthArmPc auctionBytecode auctionUpperMidFirstArmPc 2))
        (auctionSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    decide
  exact RD.dispatchTo (code := auctionBytecode) (ee := I) (g := g)
    (s0 := initState cA gh bl σ σ₀ g A I) (selWord := auctionSelWord I)
    (mem := solcFreePtrMem) (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    (acc := (cA, σ)) ⟨880⟩ 2 h40rd
    (fun j hj => auctionUpperMidArmsWellFormed j (by omega)) heq0 htake
    (by jump_dest)
    (by native_decide)
    (by simp)

theorem auctionX_timeBuffer_callvalue_ne {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨880⟩
      [auctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd880⟩ := hreach
  exact evm_run rd880 with [
    jumpdest, callvalue, dup1, iszero, push2 ⟨891⟩,
    jumpiNT (isZero_eq_zero_of_ne hwv),
    push0, dup1, raw rev 0 (by decide) mem_cost (by evm_ov)]

theorem auctionX_timeBuffer {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨880⟩
      [auctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hwv : I.weiValue = ⟨0⟩) :
    RDret auctionBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (auctionSlotWord ⟨203⟩ σ I)) := by
  obtain ⟨_, _, rd880⟩ := hreach
  have rd898 := evm_run rd880 with [
    jumpdest, callvalue, dup1, iszero, push2 ⟨891⟩,
    jumpiT (by rw [hwv]; decide) (by jump_dest),
    jumpdest, pop, push2 ⟨308⟩, push1 ⟨203⟩]
  obtain ⟨_, _, rd899⟩ := rd898.sload (by decide) (by evm_ov)
  have rd308 := evm_run rd899 with [dup2, jump (by jump_dest)]
  have rd318 := evm_run rd308 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    swap1, dup2,
    raw mstore 6 (solcReturnMem (auctionSlotWord ⟨203⟩ σ I)) (UInt256.ofNat 5) (by decide)
      mem_cost
      (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]; rfl)
      (by decide) (by evm_ov),
    push1 ⟨32⟩, add]
  exact evm_run rd318 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by decide)
      mem_cost (solcReturnMem_mload64 (auctionSlotWord ⟨203⟩ σ I))
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray (auctionSlotWord ⟨203⟩ σ I)) (by decide)
      mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show (UInt256.sub ((⟨32⟩ : UInt256) + ⟨128⟩) ⟨128⟩).toNat = 32 from by decide,
          solcReturnMem_read128])
      (by evm_ov)]

theorem auctionTimeBufferBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (_hcode : I.code = auctionBytecode)
    (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (_hsel : selIs I (auctionSelBytes 17))
    (_hAccounts : accountMapEquiv σ_evm σ_solm) :
    RuntimeCase (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) g := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (auctionSelBytes 17) rfl _hsel
  have hdispatch := auctionDispatch_timeBuffer _hsel
  have hdecode := auctionDecode_timeBuffer (I := I) hsz
  have hreach := auctionReachTimeBufferBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    _hcode hsz _hsize _hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · have hword : auctionSlotWord ⟨203⟩ σ_evm I = auctionSlotWord ⟨203⟩ σ_solm I :=
      accountMapEquiv_storage_findD _hAccounts I.codeOwner ⟨203⟩ ⟨0⟩
    have hval :
        some [Value.int (Int.ofNat (auctionSlotWord ⟨203⟩ σ_solm I).toNat)] =
          some [Value.int (Int.ofNat (auctionSlotWord ⟨203⟩ σ_evm I).toNat)] := by
      rw [hword]
    have hbody :
        ExecTransitionBody auctionConfig auctionContract
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ timeBufferGetter.body
          (.returned { contract := auctionContract, locals := ∅ }
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            (some [(.int (Int.ofNat (auctionSlotWord ⟨203⟩ σ_solm I).toNat))])) := by
      simpa [timeBufferGetter, auctionSlotWord, initState, Solm.EVM.storageLoad,
        State.lookupAccount] using
        auctionUint256GetterBodyReturns
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
          (ref := timeBufferRef) (er := ({ base := "timeBuffer", steps := [] } : EvaledStorageRef))
          (slot := ⟨203⟩)
          (by simp only [initState]; exact hwv) (by simp [timeBufferRef])
          (by simp [evalStorageRef, evalStorageRefSteps, timeBufferRef, EvalResult.bind, pure, bind])
          (by decide) (by rfl)
    have henc :
        returnEquiv (UInt256.toByteArray (auctionSlotWord ⟨203⟩ σ_evm I))
          (some [(.int (Int.ofNat (auctionSlotWord ⟨203⟩ σ_evm I).toNat))])
          timeBufferGetter.returnType := by
      rw [timeBufferGetter]
      exact returnEquiv_of_encode
        (by simpa [uint256] using uint256ReturnEncoding (auctionSlotWord ⟨203⟩ σ_evm I))
    exact (auctionX_timeBuffer hreach hwv).reEquivExecutionTransport _hcode hdispatch hdecode
      hbody hval _hAccounts henc
  · have hbody :
        ExecTransitionBody auctionConfig auctionContract
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ timeBufferGetter.body
          .reverted := by
      simpa [timeBufferGetter, nonpayable] using
        bodyReverts_nonPayable (cfg := auctionConfig) (contract := auctionContract)
          (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (locals := ∅)
          (rest := [.return [(.storage timeBufferRef)]]) (by simpa [initState] using hwv)
    exact (auctionX_timeBuffer_callvalue_ne hreach hwv).reEquivExecutionRevert _hcode
      hdispatch hdecode hbody

end Auction
