import Examples.BlindAuction.Storage
import Reasoning.Refinement
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace BlindAuction

def blindAuctionRevealEndWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)

theorem blindAuctionRevealEndBodyReturns (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hlocals : locals.get? "revealEnd" = none) :
    ExecTransitionBody blindAuctionConfig blindAuctionContract evm locals revealEndGetter.body
      (.returned { contract := blindAuctionContract, locals := locals } evm
        (some (.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩).toNat)))) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      have her : evalStorageRef blindAuctionConfig
          { contract := blindAuctionContract, locals := locals } evm revealEndRef =
          .ok { base := "revealEnd", steps := [] } := by
        simp [evalStorageRef, evalStorageRefSteps, revealEndRef, EvalResult.bind, pure, bind]
      have hty : storageTypeAt? blindAuctionContract.storage
          ({ base := "revealEnd", steps := [] } : EvaledStorageRef) =
          some (.elem (.int uint256Int)) := by
        decide
      rw [evalExpr_storage_scalar (t := .int uint256Int) (hbase := hlocals) (her := her)
        (hty := hty) (hloc := blindAuctionConfig_storage_revealEnd)]
      rw [blindAuctionStorageLocLoad_uint256])

theorem blindAuctionX_revealEnd {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hreach : ∃ k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨468⟩ [blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret blindAuctionBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (blindAuctionRevealEndWord σ I)) := by
  obtain ⟨_, _, rd468⟩ := hreach
  have rd486 := evm_run rd468 with [
    jumpdest, callvalue, dup1, iszero, push2 ⟨479⟩,
    jumpiT (by rw [hwv]; decide) (by jump_dest),
    jumpdest, pop, push2 ⟨373⟩, push1 ⟨2⟩]
  obtain ⟨_, _, rd487₀⟩ := rd486.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd487⟩ :
      ∃ k C, RD blindAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨487⟩
        [blindAuctionRevealEndWord σ I, ⟨373⟩, blindAuctionSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [blindAuctionRevealEndWord, initState] using rd487₀⟩
  have rd373 := evm_run rd487 with [
    dup2, jump (by jump_dest)]
  obtain ⟨_, _, rd206⟩ := blindAuctionRoutineEncodeWord373
    (val := blindAuctionRevealEndWord σ I) (ret := ⟨373⟩) (R := [blindAuctionSelWord I])
    rd373 (by simp only [List.length_singleton]; omega)
  exact blindAuctionReturnOneWord206 (R := [⟨373⟩, blindAuctionSelWord I]) rd206
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem blindAuctionX_revealEnd_nonpayable {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue ≠ ⟨0⟩)
    (hreach : ∃ k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨468⟩ [blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev blindAuctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd468⟩ := hreach
  have rd476 := evm_run rd468 with [
    jumpdest, callvalue, dup1, iszero, push2 ⟨479⟩,
    jumpiNT (isZero_eq_zero_of_ne hwv)]
  exact rd476.revertStub (by decide) (by decide) (by decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem blindAuctionRevealEndSelector_size {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0xa6, 0xe6, 0x64, 0x77]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0xa6, 0xe6, 0x64, 0x77]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem blindAuctionDispatch_revealEnd {cd : ByteArray}
    (hsel : ((⟨#[0xa6, 0xe6, 0x64, 0x77]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg blindAuctionContract cd = some revealEndGetter := by
  have hcd : cd.extract 0 4 = (⟨#[0xa6, 0xe6, 0x64, 0x77]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [bidTransition, revealTransition, withdrawTransition, auctionEndTransition,
      beneficiaryGetter, biddingEndGetter])
    (post := [endedGetter, highestBidderGetter, highestBidGetter, bidsGetter])
    rfl ?_ (by rw [selectorOf, blindAuctionRevealEndSelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [selectorOf, blindAuctionBidSelectorBytes, hcd]; decide
  · rw [selectorOf, blindAuctionRevealSelectorBytes, hcd]; decide
  · rw [selectorOf, blindAuctionWithdrawSelectorBytes, hcd]; decide
  · rw [selectorOf, blindAuctionAuctionEndSelectorBytes, hcd]; decide
  · rw [selectorOf, blindAuctionBeneficiarySelectorBytes, hcd]; decide
  · rw [selectorOf, blindAuctionBiddingEndSelectorBytes, hcd]; decide

theorem blindAuctionDecode_revealEnd {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldata (revealEndGetter.params.map Param.name)
      (transitionSignature revealEndGetter).paramTypes I.calldata = some ∅ := by
  show decodeCalldata [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

/-- `revealEnd()` getter body (pc 468) refines its transition. -/
theorem blindAuctionRevealEndBodyCore {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = blindAuctionBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hsel : selIs I ⟨#[0xa6, 0xe6, 0x64, 0x77]⟩)
    (hreach : ∃ k C, RD blindAuctionBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨468⟩
      [blindAuctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm)
      k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
 :
    runtimeEquivalenceFor blindAuctionConfig blindAuctionContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have _hsize : I.calldata.size < UInt256.size := hsize
  have _hperm : I.perm = true := hperm

  have hsz := blindAuctionRevealEndSelector_size hsel
  have hd := blindAuctionDispatch_revealEnd (cd := I.calldata) hsel
  have hdec := blindAuctionDecode_revealEnd (I := I) hsz
  by_cases hwv : I.weiValue = ⟨0⟩
  · have hword : blindAuctionRevealEndWord σ_evm I = blindAuctionRevealEndWord σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨2⟩ ⟨0⟩
    have hbody :
        ExecTransitionBody blindAuctionConfig blindAuctionContract
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
          revealEndGetter.body
          (.returned { contract := blindAuctionContract, locals := ∅ }
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            (some (.int (Int.ofNat (blindAuctionRevealEndWord σ_solm I).toNat)))) := by
      simpa [blindAuctionRevealEndWord, initState, Solm.EVM.storageLoad, State.lookupAccount] using
        blindAuctionRevealEndBodyReturns
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
          (by simp only [initState]; exact hwv) (by simp)
    exact (blindAuctionX_revealEnd (g := Sat256.ofUInt256 g) hwv hreach)
      |>.reEquivExecutionTransport hcode hd hdec hbody (by rw [hword]) hAccounts
        (returnEquiv_of_encode (uint256ReturnEncoding (blindAuctionRevealEndWord σ_evm I)))
  · have hbody :
        ExecTransitionBody blindAuctionConfig blindAuctionContract
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
          revealEndGetter.body .reverted := by
      simpa [revealEndGetter, initState] using
        (bodyReverts_nonPayable (cfg := blindAuctionConfig) (contract := blindAuctionContract)
          (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (locals := (∅ : Store))
          (rest := [.return (.storage revealEndRef)])
          (by simp only [initState]; exact hwv))
    exact (blindAuctionX_revealEnd_nonpayable (g := Sat256.ofUInt256 g) hwv hreach)
      |>.reEquivExecutionRevert hcode hd hdec hbody

end BlindAuction
