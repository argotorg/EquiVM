import Benchmarks.Auction.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Auction

def auctionMinBidWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (auctionSlotWord ⟨205⟩ σ I) ⟨255⟩

theorem auctionMinBidWord_lt (σ : AccountMap) (I : ExecutionEnv) :
    (auctionMinBidWord σ I).toNat < EVM.twoPow 8 := by
  unfold auctionMinBidWord
  rw [uland_toNat]
  have h255 : (⟨255⟩ : UInt256).toNat = 255 := by decide
  rw [h255, show EVM.twoPow 8 = 256 from by decide]
  exact lt_of_le_of_lt Nat.and_le_right (by norm_num)

theorem auction_land255_double (x : UInt256) :
    UInt256.land (UInt256.land ⟨255⟩ x) ⟨255⟩ = UInt256.land x ⟨255⟩ := by
  apply u256_inj
  have h255 : (⟨255⟩ : UInt256).toNat = 255 := by decide
  rw [uland_toNat, uland_toNat, uland_toNat, h255]
  rw [Nat.and_comm 255 x.toNat, Nat.and_assoc, Nat.and_self]

theorem auctionDispatch_minBidIncrementPercentage {I : ExecutionEnv}
    (hsel : selIs I (auctionSelBytes 14)) :
    dispatchMsg auctionContract I.calldata = some minBidIncGetter := by
  apply dispatchMsg_eq_some_of_split (hfallback := by rfl)
    (pre := [initializeTransition, createBidTransition, settleAndCreateTransition,
      settleAuctionTransition, pauseTransition, unpauseTransition, setTimeBufferTransition,
      setReservePriceTransition, setMinBidIncTransition, transferOwnershipTransition,
      renounceOwnershipTransition, ownerGetter, pausedGetter, nounsGetter, wethGetter,
      timeBufferGetter, reservePriceGetter])
    (post := [durationGetter, auctionGetter])
    (ti := minBidIncGetter)
    (htr := by rfl)
  · intro t ht
    have hcd : I.calldata.extract 0 4 = auctionSelBytes 14 := (byteArray_eq_of_beq hsel).symm
    simp at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp [selectorOf, initializeSelectorBytes, createBidSelectorBytes,
        settleAndCreateSelectorBytes, settleAuctionSelectorBytes, pauseSelectorBytes,
        unpauseSelectorBytes, setTimeBufferSelectorBytes, setReservePriceSelectorBytes,
        setMinBidIncSelectorBytes, transferOwnershipSelectorBytes, renounceOwnershipSelectorBytes,
        ownerSelectorBytes, pausedSelectorBytes, nounsSelectorBytes, wethSelectorBytes,
        timeBufferSelectorBytes, reservePriceSelectorBytes, hcd, auctionSelBytes]
      native_decide
  · rw [selectorOf, minBidIncSelectorBytes]
    simpa [selIs, auctionSelBytes] using hsel

theorem auctionDecode_minBidIncrementPercentage {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode auctionConfig.abiDecodeMode (minBidIncGetter.params.map Param.name)
      (transitionSignature minBidIncGetter).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode auctionConfig.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem auctionReachMinBidIncrementPercentageBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = auctionBytecode)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (auctionSelBytes 14)) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨785⟩
      [auctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsel' : ((⟨#[0xb2, 0x96, 0x02, 0x4d]⟩ : ByteArray) == I.calldata.extract 0 4) = true := by
    simpa [selIs, auctionSelBytes] using hsel
  have hword : auctionSelWord I = ⟨0xb296024d⟩ :=
    auctionSelWord_eq_of_beq I hsz 0xb2 0x96 0x02 0x4d ⟨0xb296024d⟩
      (by decide) hsel'
  obtain ⟨_, _, hsplit⟩ := auctionReachRootSplit (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz hsize
  have hroot : UInt256.gt (armSelNat auctionBytecode auctionSplitPc) (auctionSelWord I) = ⟨0⟩ := by
    rw [hword]
    decide
  have h29 := RD.selectorSplitNotTakenAuto hsplit auctionSplitWellFormed hroot (by simp)
  have hupper : UInt256.gt (armSelNat auctionBytecode auctionUpperSplitPc) (auctionSelWord I) ≠
      ⟨0⟩ := by
    rw [hword]
    decide
  have h98 := RD.selectorSplitTakenAuto h29 auctionUpperSplitWellFormed hupper
    (by jump_dest) (by simp)
  have h99 := h98.jumpdest (by decide) (by simp)
  have heq0 : ∀ j, j < 4 →
      UInt256.eq (armSelNat auctionBytecode
        (nthArmPc auctionBytecode auctionUpperLowFirstArmPc j)) (auctionSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> decide
  have htake :
      UInt256.eq
        (armSelNat auctionBytecode (nthArmPc auctionBytecode auctionUpperLowFirstArmPc 4))
        (auctionSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    decide
  exact RD.dispatchTo (code := auctionBytecode) (ee := I) (g := g)
    (s0 := initState cA gh bl σ σ₀ g A I) (selWord := auctionSelWord I)
    (mem := solcFreePtrMem) (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    (acc := (cA, σ)) ⟨785⟩ 4 h99
    (fun j hj => auctionUpperLowArmsWellFormed j (by omega)) heq0 htake
    (by jump_dest)
    (by native_decide)
    (by simp)

theorem auctionX_minBidIncrementPercentage_callvalue_ne {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨785⟩
      [auctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd785⟩ := hreach
  exact evm_run rd785 with [
    jumpdest, callvalue, dup1, iszero, push2 ⟨796⟩,
    jumpiNT (isZero_eq_zero_of_ne hwv),
    push0, dup1, raw rev 0 (by decide) mem_cost (by evm_ov)]

theorem auctionX_minBidIncrementPercentage {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨785⟩
      [auctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hwv : I.weiValue = ⟨0⟩) :
    RDret auctionBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (auctionMinBidWord σ I)) := by
  obtain ⟨_, _, rd785⟩ := hreach
  have rd800 := evm_run rd785 with [
    jumpdest, callvalue, dup1, iszero, push2 ⟨796⟩,
    jumpiT (by rw [hwv]; decide) (by jump_dest),
    jumpdest, pop, push1 ⟨205⟩]
  obtain ⟨_, _, rd801⟩ := rd800.sload (by decide) (by evm_ov)
  have rd810 := evm_run rd801 with [
    push2 ⟨810⟩, swap1, push1 ⟨255⟩, and, dup2, jump (by jump_dest)]
  have rd824 := evm_run rd810 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    push1 ⟨255⟩, swap1, swap2, and, dup2,
    raw mstore 6
      (solcReturnMem
        (UInt256.land (UInt256.land ⟨255⟩ (auctionSlotWord ⟨205⟩ σ I)) ⟨255⟩))
      (UInt256.ofNat 5) (by decide)
      mem_cost
      (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]; rfl)
      (by decide) (by evm_ov),
    push1 ⟨32⟩, add, push2 ⟨318⟩, jump (by jump_dest)]
  have hret := evm_run rd824 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by decide)
      mem_cost (solcReturnMem_mload64
        (UInt256.land (UInt256.land ⟨255⟩ (auctionSlotWord ⟨205⟩ σ I)) ⟨255⟩))
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0
      (UInt256.toByteArray
        (UInt256.land (UInt256.land ⟨255⟩ (auctionSlotWord ⟨205⟩ σ I)) ⟨255⟩))
      (by decide)
      mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show (UInt256.sub ((⟨32⟩ : UInt256) + ⟨128⟩) ⟨128⟩).toNat = 32 from by decide,
          solcReturnMem_read128])
      (by evm_ov)]
  simpa [auctionMinBidWord, auction_land255_double] using hret

theorem auctionMinBidIncrementPercentageBodyCore {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (_hcode : I.code = auctionBytecode)
    (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (_hsel : selIs I (auctionSelBytes 14))
    (_hAccounts : accountMapEquiv σ_evm σ_solm) :
    RuntimeCase (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) g := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (auctionSelBytes 14) rfl _hsel
  have hdispatch := auctionDispatch_minBidIncrementPercentage _hsel
  have hdecode := auctionDecode_minBidIncrementPercentage (I := I) hsz
  have hreach := auctionReachMinBidIncrementPercentageBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    _hcode hsz _hsize _hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · have hword : auctionMinBidWord σ_evm I = auctionMinBidWord σ_solm I := by
      unfold auctionMinBidWord
      unfold auctionSlotWord
      rw [accountMapEquiv_storage_findD _hAccounts I.codeOwner ⟨205⟩ ⟨0⟩]
    have hval :
        some [Value.int (Int.ofNat (auctionMinBidWord σ_solm I).toNat)] =
          some [Value.int (Int.ofNat (auctionMinBidWord σ_evm I).toNat)] := by
      rw [hword]
    have hbody :
        ExecTransitionBody auctionConfig auctionContract
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ minBidIncGetter.body
          (.returned { contract := auctionContract, locals := ∅ }
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            (some [(.int (Int.ofNat (auctionMinBidWord σ_solm I).toNat))])) := by
      simpa [minBidIncGetter, auctionMinBidWord, auctionSlotWord, initState,
        Solm.EVM.storageLoad, State.lookupAccount] using
        auctionUint8GetterBodyReturns
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
          (ref := minBidIncRef)
          (er := ({ base := "minBidIncrementPercentage", steps := [] } : EvaledStorageRef))
          (slot := ⟨205⟩)
          (by simp only [initState]; exact hwv) (by simp [minBidIncRef])
          (by simp [evalStorageRef, evalStorageRefSteps, minBidIncRef, EvalResult.bind, pure, bind])
          (by decide) (by rfl)
    have henc :
        returnEquiv (UInt256.toByteArray (auctionMinBidWord σ_evm I))
          (some [(.int (Int.ofNat (auctionMinBidWord σ_evm I).toNat))])
          minBidIncGetter.returnType := by
      rw [minBidIncGetter]
      exact returnEquiv_of_encode
        (by simpa [uint8, uint8Int] using
          uint8ReturnEncoding (auctionMinBidWord σ_evm I) (auctionMinBidWord_lt σ_evm I))
    exact (auctionX_minBidIncrementPercentage hreach hwv).reEquivExecutionTransport _hcode
      hdispatch hdecode hbody hval _hAccounts henc
  · have hbody :
        ExecTransitionBody auctionConfig auctionContract
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ minBidIncGetter.body
          .reverted := by
      simpa [minBidIncGetter, nonpayable] using
        bodyReverts_nonPayable (cfg := auctionConfig) (contract := auctionContract)
          (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (locals := ∅)
          (rest := [.return [(.storage minBidIncRef)]]) (by simpa [initState] using hwv)
    exact (auctionX_minBidIncrementPercentage_callvalue_ne hreach hwv).reEquivExecutionRevert
      _hcode hdispatch hdecode hbody

end Auction
