import Benchmarks.Auction.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Auction

theorem auctionDispatch_nouns {I : ExecutionEnv} (hsel : selIs I (auctionSelBytes 1)) :
    dispatchMsg auctionContract I.calldata = some nounsGetter := by
  apply dispatchMsg_eq_some_of_split (hfallback := by rfl)
    (pre := [initializeTransition, createBidTransition, settleAndCreateTransition,
      settleAuctionTransition, pauseTransition, unpauseTransition, setTimeBufferTransition,
      setReservePriceTransition, setMinBidIncTransition, transferOwnershipTransition,
      renounceOwnershipTransition, ownerGetter, pausedGetter])
    (post := [wethGetter, timeBufferGetter, reservePriceGetter, minBidIncGetter, durationGetter,
      auctionGetter])
    (ti := nounsGetter)
    (htr := by rfl)
  · intro t ht
    have hcd : I.calldata.extract 0 4 = auctionSelBytes 1 := (byteArray_eq_of_beq hsel).symm
    simp at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl
    all_goals
      simp [selectorOf, initializeSelectorBytes, createBidSelectorBytes,
        settleAndCreateSelectorBytes, settleAuctionSelectorBytes, pauseSelectorBytes,
        unpauseSelectorBytes, setTimeBufferSelectorBytes, setReservePriceSelectorBytes,
        setMinBidIncSelectorBytes, transferOwnershipSelectorBytes, renounceOwnershipSelectorBytes,
        ownerSelectorBytes, pausedSelectorBytes, hcd, auctionSelBytes]
      native_decide
  · rw [selectorOf, nounsSelectorBytes]
    simpa [selIs, auctionSelBytes] using hsel

theorem auctionDecode_nouns {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode auctionConfig.abiDecodeMode (nounsGetter.params.map Param.name)
      (transitionSignature nounsGetter).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode auctionConfig.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem auctionReachNounsBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = auctionBytecode)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (auctionSelBytes 1)) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨327⟩
      [auctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsel' : ((⟨#[0x2d, 0xe4, 0x5f, 0x18]⟩ : ByteArray) == I.calldata.extract 0 4) = true := by
    simpa [selIs, auctionSelBytes] using hsel
  have hword : auctionSelWord I = ⟨0x2de45f18⟩ :=
    auctionSelWord_eq_of_beq I hsz 0x2d 0xe4 0x5f 0x18 ⟨0x2de45f18⟩
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
  have heq0 : ∀ j, j < 1 →
      UInt256.eq (armSelNat auctionBytecode
        (nthArmPc auctionBytecode auctionLowerLowFirstArmPc j)) (auctionSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    rw [hword]
    native_decide
  have htake :
      UInt256.eq
        (armSelNat auctionBytecode (nthArmPc auctionBytecode auctionLowerLowFirstArmPc 1))
        (auctionSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact RD.dispatchTo (code := auctionBytecode) (ee := I) (g := g)
    (s0 := initState cA gh bl σ σ₀ g A I) (selWord := auctionSelWord I)
    (mem := solcFreePtrMem) (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    (acc := (cA, σ)) ⟨327⟩ 1 h228
    (fun j hj => auctionLowerLowArmsWellFormed j (by omega)) heq0 htake
    (by jump_dest)
    (by native_decide)
    (by simp)

theorem auctionX_nouns_callvalue_ne {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨327⟩
      [auctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd327⟩ := hreach
  exact evm_run rd327 with [
    jumpdest, callvalue, dup1, iszero, push2 ⟨338⟩,
    jumpiNT (isZero_eq_zero_of_ne hwv),
    push0, dup1, raw rev 0 (by native_decide) mem_cost (by evm_ov)]

theorem auctionX_nouns {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨327⟩
      [auctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hwv : I.weiValue = ⟨0⟩) :
    RDret auctionBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (UInt256.land (auctionSlotWord ⟨201⟩ σ I) solcAddrMask)) := by
  obtain ⟨_, _, rd327⟩ := hreach
  have rd342 := evm_run rd327 with [
    jumpdest, callvalue, dup1, iszero, push2 ⟨338⟩,
    jumpiT (by rw [hwv]; decide) (by jump_dest),
    jumpdest, pop, push1 ⟨201⟩]
  obtain ⟨_, _, rd343⟩ := rd342.sload (by native_decide) (by evm_ov)
  have rd358 := evm_run rd343 with [
    push2 ⟨358⟩, swap1, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and,
    dup2, jump (by jump_dest)]
  have rd318 := evm_run rd358 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, swap1, swap2, and, dup2,
    raw mstore 6
      (solcReturnMem
        (UInt256.land (UInt256.land solcAddrMask (auctionSlotWord ⟨201⟩ σ I)) solcAddrMask))
      (UInt256.ofNat 5) (by native_decide)
      mem_cost
      (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]; rfl)
      (by decide) (by evm_ov),
    push1 ⟨32⟩, add, push2 ⟨318⟩, jump (by jump_dest)]
  have hret := evm_run rd318 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by native_decide)
      mem_cost
      (solcReturnMem_mload64
        (UInt256.land (UInt256.land solcAddrMask (auctionSlotWord ⟨201⟩ σ I)) solcAddrMask))
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0
      (UInt256.toByteArray
        (UInt256.land (UInt256.land solcAddrMask (auctionSlotWord ⟨201⟩ σ I)) solcAddrMask))
      (by native_decide)
      mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show (UInt256.sub ((⟨32⟩ : UInt256) + ⟨128⟩) ⟨128⟩).toNat = 32 from by decide,
          solcReturnMem_read128])
      (by evm_ov)]
  have hclean :
      UInt256.land (UInt256.land solcAddrMask (auctionSlotWord ⟨201⟩ σ I)) solcAddrMask =
        UInt256.land (auctionSlotWord ⟨201⟩ σ I) solcAddrMask := by
    rw [u256_land_comm solcAddrMask (auctionSlotWord ⟨201⟩ σ I)]
    exact solcAddrMask_clean (solcAddrMask_result_canonical (auctionSlotWord ⟨201⟩ σ I))
  simpa [hclean] using hret

theorem auctionNounsBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (_hcode : I.code = auctionBytecode)
    (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (_hsel : selIs I (auctionSelBytes 1))
    (_hAccounts : accountMapEquiv σ_evm σ_solm) :
    RuntimeCase (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) g := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (auctionSelBytes 1) rfl _hsel
  have hdispatch := auctionDispatch_nouns _hsel
  have hdecode := auctionDecode_nouns (I := I) hsz
  have hreach := auctionReachNounsBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    _hcode hsz _hsize _hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · have hword : auctionSlotWord ⟨201⟩ σ_evm I = auctionSlotWord ⟨201⟩ σ_solm I :=
      accountMapEquiv_storage_findD _hAccounts I.codeOwner ⟨201⟩ ⟨0⟩
    have hval :
        some [Value.address (AccountAddress.ofNat
            (UInt256.land (auctionSlotWord ⟨201⟩ σ_solm I) solcAddrMask).toNat)] =
          some [Value.address (AccountAddress.ofNat
            (UInt256.land (auctionSlotWord ⟨201⟩ σ_evm I) solcAddrMask).toNat)] := by
      rw [hword]
    have hbody :
        ExecTransitionBody auctionConfig auctionContract
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ nounsGetter.body
          (.returned { contract := auctionContract, locals := ∅ }
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            (some [(.address (AccountAddress.ofNat
              (UInt256.land (auctionSlotWord ⟨201⟩ σ_solm I) solcAddrMask).toNat))])) := by
      simpa [nounsGetter, auctionSlotWord, initState, Solm.EVM.storageLoad, State.lookupAccount]
        using
        auctionAddressGetterBodyReturns
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
          (ref := nounsRef) (er := ({ base := "nouns", steps := [] } : EvaledStorageRef))
          (slot := ⟨201⟩)
          (by simp only [initState]; exact hwv) (by simp [nounsRef])
          (by simp [evalStorageRef, evalStorageRefSteps, nounsRef, EvalResult.bind, pure, bind])
          (by decide) (by rfl)
    have henc :
        returnEquiv (UInt256.toByteArray
            (UInt256.land (auctionSlotWord ⟨201⟩ σ_evm I) solcAddrMask))
          (some [(.address (AccountAddress.ofNat
            (UInt256.land (auctionSlotWord ⟨201⟩ σ_evm I) solcAddrMask).toNat))])
          nounsGetter.returnType := by
      rw [nounsGetter]
      exact returnEquiv_of_encode
        (solcAddressReturnEncoding (addrTy := addr) rfl (auctionSlotWord ⟨201⟩ σ_evm I))
    exact (auctionX_nouns hreach hwv).reEquivExecutionTransport _hcode hdispatch hdecode
      hbody hval _hAccounts henc
  · have hbody :
        ExecTransitionBody auctionConfig auctionContract
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ nounsGetter.body
          .reverted := by
      simpa [nounsGetter, nonpayable] using
        bodyReverts_nonPayable (cfg := auctionConfig) (contract := auctionContract)
          (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (locals := ∅)
          (rest := [.return [(.storage nounsRef)]]) (by simpa only [initState] using hwv)
    exact (auctionX_nouns_callvalue_ne hreach hwv).reEquivExecutionRevert _hcode
      hdispatch hdecode hbody

end Auction
