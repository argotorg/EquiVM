import Examples.BlindAuction.Storage
import Reasoning.Refinement
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace BlindAuction

/-! ## `biddingEnd()` getter -/

def biddingEndWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)

theorem blindAuctionBiddingEndBodyReturns (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hlocals : locals.get? "biddingEnd" = none) :
    ExecTransitionBody blindAuctionConfig blindAuctionContract evm locals biddingEndGetter.body
      (.returned { contract := blindAuctionContract, locals := locals } evm
        (some [(.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat))])) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      have her : evalStorageRef blindAuctionConfig
          { contract := blindAuctionContract, locals := locals } evm biddingEndRef =
          .ok { base := "biddingEnd", steps := [] } := by
        simp [evalStorageRef, evalStorageRefSteps, biddingEndRef, EvalResult.bind, pure, bind]
      have hty : storageTypeAt? blindAuctionContract.storage
          ({ base := "biddingEnd", steps := [] } : EvaledStorageRef) =
          some (.elem (.int uint256Int)) := by
        decide
      rw [evalExpr_storage_scalar (t := .int uint256Int) (hbase := hlocals) (her := her)
        (hty := hty) (hloc := blindAuctionConfig_storage_biddingEnd)]
      rw [blindAuctionStorageLocLoad_uint256])

theorem blindAuctionX_biddingEnd {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hreach : ∃ k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨352⟩ [blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret blindAuctionBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (biddingEndWord σ I)) := by
  obtain ⟨_, _, rd352⟩ := hreach
  have rd370 := evm_run rd352 with [
    jumpdest, callvalue, dup1, iszero, push2 ⟨363⟩,
    jumpiT (by rw [hwv]; decide) (by jump_dest),
    jumpdest, pop, push2 ⟨373⟩, push1 ⟨1⟩]
  obtain ⟨_, _, rd371₀⟩ := rd370.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd371⟩ :
      ∃ k C, RD blindAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨371⟩
        [biddingEndWord σ I, ⟨373⟩, blindAuctionSelWord I] solcFreePtrMem
        (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [biddingEndWord, initState] using rd371₀⟩
  have rd373 := evm_run rd371 with [
    dup2, jump (by jump_dest)]
  obtain ⟨_, _, rd206⟩ := blindAuctionRoutineEncodeWord373
    (val := biddingEndWord σ I) (ret := ⟨373⟩) (R := [blindAuctionSelWord I])
    rd373 (by simp only [List.length_singleton]; omega)
  exact blindAuctionReturnOneWord206 (R := [⟨373⟩, blindAuctionSelWord I]) rd206
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem blindAuctionX_biddingEnd_nonpayable {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue ≠ ⟨0⟩)
    (hreach : ∃ k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨352⟩ [blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev blindAuctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd352⟩ := hreach
  have rd360 := evm_run rd352 with [
    jumpdest, callvalue, dup1, iszero, push2 ⟨363⟩,
    jumpiNT (isZero_eq_zero_of_ne hwv)]
  exact rd360.revertStub (by decide) (by decide) (by decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem blindAuctionBiddingEndSelector_size {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x42, 0x3b, 0x21, 0x7f]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x42, 0x3b, 0x21, 0x7f]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem blindAuctionDispatch_biddingEnd {cd : ByteArray}
    (hsel : ((⟨#[0x42, 0x3b, 0x21, 0x7f]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg blindAuctionContract cd = some biddingEndGetter := by
  have hcd : cd.extract 0 4 = (⟨#[0x42, 0x3b, 0x21, 0x7f]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [bidTransition, revealTransition, withdrawTransition, auctionEndTransition,
      beneficiaryGetter])
    (post := [revealEndGetter, endedGetter, highestBidderGetter, highestBidGetter, bidsGetter])
    rfl rfl ?_ (by rw [selectorOf, blindAuctionBiddingEndSelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · rw [selectorOf, blindAuctionBidSelectorBytes, hcd]; decide
  · rw [selectorOf, blindAuctionRevealSelectorBytes, hcd]; decide
  · rw [selectorOf, blindAuctionWithdrawSelectorBytes, hcd]; decide
  · rw [selectorOf, blindAuctionAuctionEndSelectorBytes, hcd]; decide
  · rw [selectorOf, blindAuctionBeneficiarySelectorBytes, hcd]; decide

theorem blindAuctionDecode_biddingEnd {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldata (biddingEndGetter.params.map Param.name)
      (transitionSignature biddingEndGetter).paramTypes I.calldata = some ∅ := by
  show decodeCalldata [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

/-- `biddingEnd()` getter body (pc 352) refines its transition. -/
theorem blindAuctionBiddingEndBodyCore {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = blindAuctionBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hsel : selIs I ⟨#[0x42, 0x3b, 0x21, 0x7f]⟩)
    (hreach : ∃ k C, RD blindAuctionBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨352⟩
      [blindAuctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm)
      k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
 :
    runtimeEquivalenceFor blindAuctionConfig blindAuctionContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have _hsize : I.calldata.size < UInt256.size := hsize
  have _hperm : I.perm = true := hperm

  have hsz := blindAuctionBiddingEndSelector_size hsel
  have hd := blindAuctionDispatch_biddingEnd (cd := I.calldata) hsel
  have hdec := blindAuctionDecode_biddingEnd (I := I) hsz
  by_cases hwv : I.weiValue = ⟨0⟩
  · have hword : biddingEndWord σ_evm I = biddingEndWord σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨1⟩ ⟨0⟩
    have hbody :
        ExecTransitionBody blindAuctionConfig blindAuctionContract
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
          biddingEndGetter.body
          (.returned { contract := blindAuctionContract, locals := ∅ }
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            (some [(.int (Int.ofNat (biddingEndWord σ_solm I).toNat))])) := by
      simpa [biddingEndWord, initState, Solm.EVM.storageLoad, State.lookupAccount] using
        blindAuctionBiddingEndBodyReturns
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
          (by simp only [initState]; exact hwv) (by simp)
    exact (blindAuctionX_biddingEnd (g := Sat256.ofUInt256 g) hwv hreach)
      |>.reEquivExecutionTransport hcode hd hdec hbody (by rw [hword]) hAccounts
        (returnEquiv_of_encode (uint256ReturnEncoding (biddingEndWord σ_evm I)))
  · have hbody :
        ExecTransitionBody blindAuctionConfig blindAuctionContract
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
          biddingEndGetter.body .reverted := by
      simpa [biddingEndGetter, initState] using
        (bodyReverts_nonPayable (cfg := blindAuctionConfig) (contract := blindAuctionContract)
          (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (locals := (∅ : Store))
          (rest := [.return [(.storage biddingEndRef)]])
          (by simp only [initState]; exact hwv))
    exact (blindAuctionX_biddingEnd_nonpayable (g := Sat256.ofUInt256 g) hwv hreach)
      |>.reEquivExecutionRevert hcode hd hdec hbody

end BlindAuction
