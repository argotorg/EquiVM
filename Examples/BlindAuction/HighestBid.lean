import Examples.BlindAuction.Storage
import Reasoning.Refinement
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace BlindAuction

/-! ## `highestBid()` getter -/

def highestBidWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨6⟩ ⟨0⟩)

theorem blindAuctionHighestBidBodyReturns (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hlocals : locals.get? "highestBid" = none) :
    ExecTransitionBody blindAuctionConfig blindAuctionContract evm locals highestBidGetter.body
      (.returned { contract := blindAuctionContract, locals := locals } evm
        (some (.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩).toNat)))) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      have her : evalStorageRef blindAuctionConfig
          { contract := blindAuctionContract, locals := locals } evm highestBidRef =
          .ok { base := "highestBid", steps := [] } := by
        simp [evalStorageRef, evalStorageRefSteps, highestBidRef, EvalResult.bind, pure, bind]
      have hty : storageTypeAt? blindAuctionContract.storage
          ({ base := "highestBid", steps := [] } : EvaledStorageRef) =
          some (.elem (.int uint256Int)) := by
        decide
      rw [evalExpr_storage_scalar (t := .int uint256Int) (hbase := hlocals) (her := her)
        (hty := hty) (hloc := blindAuctionConfig_storage_highestBid),
        blindAuctionStorageLocLoad_uint256])

theorem blindAuctionX_highestBid {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hreach : ∃ k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨489⟩ [blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret blindAuctionBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (highestBidWord σ I)) := by
  obtain ⟨_, _, rd489⟩ := hreach
  have rd507 := evm_run rd489 with [
    jumpdest, callvalue, dup1, iszero, push2 ⟨500⟩,
    jumpiT (by rw [hwv]; decide) (by jump_dest),
    jumpdest, pop, push2 ⟨373⟩, push1 ⟨6⟩ ]
  obtain ⟨_, _, rd508₀⟩ := rd507.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd508⟩ :
      ∃ k C, RD blindAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨508⟩
        [highestBidWord σ I, ⟨373⟩, blindAuctionSelWord I] solcFreePtrMem
        (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [highestBidWord, initState] using rd508₀⟩
  have rd373 := evm_run rd508 with [
    dup2, jump (by jump_dest) ]
  obtain ⟨_, _, rd206⟩ := blindAuctionRoutineEncodeWord373
    (val := highestBidWord σ I) (ret := ⟨373⟩) (R := [blindAuctionSelWord I])
    rd373 (by simp only [List.length_singleton]; omega)
  exact blindAuctionReturnOneWord206 (R := [⟨373⟩, blindAuctionSelWord I]) rd206
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem blindAuctionX_highestBid_nonpayable {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue ≠ ⟨0⟩)
    (hreach : ∃ k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨489⟩ [blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev blindAuctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd489⟩ := hreach
  have rd497 := evm_run rd489 with [
    jumpdest, callvalue, dup1, iszero, push2 ⟨500⟩,
    jumpiNT (isZero_eq_zero_of_ne hwv)]
  exact rd497.revertStub (by decide) (by decide) (by decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem blindAuctionHighestBidSelector_size {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0xd5, 0x7b, 0xde, 0x79]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0xd5, 0x7b, 0xde, 0x79]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem blindAuctionDispatch_highestBid {cd : ByteArray}
    (hsel : ((⟨#[0xd5, 0x7b, 0xde, 0x79]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg blindAuctionContract cd = some highestBidGetter := by
  have hcd : cd.extract 0 4 = (⟨#[0xd5, 0x7b, 0xde, 0x79]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [bidTransition, revealTransition, withdrawTransition, auctionEndTransition,
      beneficiaryGetter, biddingEndGetter, revealEndGetter, endedGetter, highestBidderGetter])
    (post := [bidsGetter])
    rfl rfl ?_ (by rw [selectorOf, blindAuctionHighestBidSelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [selectorOf, blindAuctionBidSelectorBytes, hcd]; decide
  · rw [selectorOf, blindAuctionRevealSelectorBytes, hcd]; decide
  · rw [selectorOf, blindAuctionWithdrawSelectorBytes, hcd]; decide
  · rw [selectorOf, blindAuctionAuctionEndSelectorBytes, hcd]; decide
  · rw [selectorOf, blindAuctionBeneficiarySelectorBytes, hcd]; decide
  · rw [selectorOf, blindAuctionBiddingEndSelectorBytes, hcd]; decide
  · rw [selectorOf, blindAuctionRevealEndSelectorBytes, hcd]; decide
  · rw [selectorOf, blindAuctionEndedSelectorBytes, hcd]; decide
  · rw [selectorOf, blindAuctionHighestBidderSelectorBytes, hcd]; decide

theorem blindAuctionDecode_highestBid {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldata (highestBidGetter.params.map Param.name)
      (transitionSignature highestBidGetter).paramTypes I.calldata = some ∅ := by
  show decodeCalldata [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

/-- `highestBid()` getter body (pc 489) refines its transition. -/
theorem blindAuctionHighestBidBodyCore {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = blindAuctionBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hsel : selIs I ⟨#[0xd5, 0x7b, 0xde, 0x79]⟩)
    (hreach : ∃ k C, RD blindAuctionBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨489⟩
      [blindAuctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm)
      k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
 :
    runtimeEquivalenceFor blindAuctionConfig blindAuctionContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have _hsize : I.calldata.size < UInt256.size := hsize
  have _hperm : I.perm = true := hperm

  have hsz := blindAuctionHighestBidSelector_size hsel
  have hd := blindAuctionDispatch_highestBid (cd := I.calldata) hsel
  have hdec := blindAuctionDecode_highestBid (I := I) hsz
  by_cases hwv : I.weiValue = ⟨0⟩
  · have hword : highestBidWord σ_evm I = highestBidWord σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨6⟩ ⟨0⟩
    have hbody :
        ExecTransitionBody blindAuctionConfig blindAuctionContract
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
          highestBidGetter.body
          (.returned { contract := blindAuctionContract, locals := ∅ }
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            (some (.int (Int.ofNat (highestBidWord σ_solm I).toNat)))) := by
      simpa [highestBidWord, initState, Solm.EVM.storageLoad, State.lookupAccount] using
        blindAuctionHighestBidBodyReturns
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
          (by simp only [initState]; exact hwv) (by simp)
    exact (blindAuctionX_highestBid (g := Sat256.ofUInt256 g) hwv hreach)
      |>.reEquivExecutionTransport hcode hd hdec hbody (by rw [hword]) hAccounts
        (returnEquiv_of_encode (uint256ReturnEncoding (highestBidWord σ_evm I)))
  · have hbody :
        ExecTransitionBody blindAuctionConfig blindAuctionContract
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
          highestBidGetter.body .reverted := by
      simpa [highestBidGetter, initState] using
        (bodyReverts_nonPayable (cfg := blindAuctionConfig) (contract := blindAuctionContract)
          (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (locals := (∅ : Store))
          (rest := [.return (.storage highestBidRef)])
          (by simp only [initState]; exact hwv))
    exact (blindAuctionX_highestBid_nonpayable (g := Sat256.ofUInt256 g) hwv hreach)
      |>.reEquivExecutionRevert hcode hd hdec hbody

end BlindAuction
