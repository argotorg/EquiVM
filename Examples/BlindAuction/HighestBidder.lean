import Examples.BlindAuction.Storage
import Reasoning.SolmBody
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Digits.Lemmas

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace BlindAuction

/-! ## `highestBidder()` getter -/

def highestBidderWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨5⟩ ⟨0⟩)

abbrev highestBidderReturnWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (highestBidderWord σ I) solcAddrMask

theorem blindAuctionHighestBidderBodyReturns (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hlocals : locals.get? "highestBidder" = none) :
    ExecTransitionBody blindAuctionConfig blindAuctionContract evm locals highestBidderGetter.body
      (.returned { contract := blindAuctionContract, locals := locals } evm
        (some [(.address (AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩)
            solcAddrMask).toNat))])) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      have her : evalStorageRef blindAuctionConfig
          { contract := blindAuctionContract, locals := locals } evm highestBidderRef =
          .ok { base := "highestBidder", steps := [] } := by
        simp [evalStorageRef, evalStorageRefSteps, highestBidderRef, EvalResult.bind, pure, bind]
      have hty : storageTypeAt? blindAuctionContract.storage
          ({ base := "highestBidder", steps := [] } : EvaledStorageRef) =
          some (.elem .address) := by
        decide
      rw [evalExpr_storage_scalar (t := .address) (hbase := hlocals) (her := her)
        (hty := hty) (hloc := blindAuctionConfig_storage_highestBidder),
        blindAuctionStorageLocLoad_address_offset0])

theorem blindAuctionX_highestBidder {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hreach : ∃ k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨418⟩ [blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret blindAuctionBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (highestBidderReturnWord σ I)) := by
  obtain ⟨_, _, rd418⟩ := hreach
  have rd431 := evm_run rd418 with [
    jumpdest, callvalue, dup1, iszero, push2 ⟨429⟩,
    jumpiT (by rw [hwv]; decide) (by jump_dest),
    jumpdest, pop, push1 ⟨5⟩]
  obtain ⟨_, _, rd434₀⟩ := rd431.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd434⟩ :
      ∃ k C, RD blindAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨434⟩
        [highestBidderWord σ I, blindAuctionSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [highestBidderWord, initState] using rd434₀⟩
  have rd308 := evm_run rd434 with [
    push2 ⟨308⟩, swap1, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩,
    shl, sub, and, dup2, jump (by jump_dest)]
  obtain ⟨_, _, rd206⟩ := blindAuctionRoutineEncodeAddress308
    (val := UInt256.land solcAddrMask (highestBidderWord σ I)) (ret := ⟨308⟩)
    (R := [blindAuctionSelWord I]) rd308 (by simp only [List.length_singleton]; omega)
  have hval : UInt256.land solcAddrMask (highestBidderWord σ I) =
      UInt256.land (highestBidderWord σ I) solcAddrMask :=
    Reasoning.Theory.u256_land_comm solcAddrMask (highestBidderWord σ I)
  have hclean :
      UInt256.land (UInt256.land solcAddrMask (highestBidderWord σ I)) solcAddrMask =
        UInt256.land (highestBidderWord σ I) solcAddrMask := by
    rw [hval]
    exact solcAddrMask_clean (solcAddrMask_result_canonical (highestBidderWord σ I))
  have hret := blindAuctionReturnOneWord206
    (R := [⟨308⟩, blindAuctionSelWord I]) rd206
    (by simp only [List.length_cons, List.length_nil]; omega)
  simpa [highestBidderReturnWord, hclean] using hret

theorem blindAuctionX_highestBidder_nonpayable {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue ≠ ⟨0⟩)
    (hreach : ∃ k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨418⟩ [blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev blindAuctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd418⟩ := hreach
  have rd426 := evm_run rd418 with [
    jumpdest, callvalue, dup1, iszero, push2 ⟨429⟩,
    jumpiNT (isZero_eq_zero_of_ne hwv)]
  exact rd426.revertStub (by decide) (by decide) (by decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem blindAuctionHighestBidderSelector_size {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x91, 0xf9, 0x01, 0x57]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x91, 0xf9, 0x01, 0x57]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem blindAuctionDispatch_highestBidder {cd : ByteArray}
    (hsel : ((⟨#[0x91, 0xf9, 0x01, 0x57]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg blindAuctionContract cd = some highestBidderGetter := by
  have hcd : cd.extract 0 4 = (⟨#[0x91, 0xf9, 0x01, 0x57]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [bidTransition, revealTransition, withdrawTransition, auctionEndTransition,
      beneficiaryGetter, biddingEndGetter, revealEndGetter, endedGetter])
    (post := [highestBidGetter, bidsGetter])
    rfl rfl ?_ (by rw [selectorOf, blindAuctionHighestBidderSelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [selectorOf, blindAuctionBidSelectorBytes, hcd]; decide
  · rw [selectorOf, blindAuctionRevealSelectorBytes, hcd]; decide
  · rw [selectorOf, blindAuctionWithdrawSelectorBytes, hcd]; decide
  · rw [selectorOf, blindAuctionAuctionEndSelectorBytes, hcd]; decide
  · rw [selectorOf, blindAuctionBeneficiarySelectorBytes, hcd]; decide
  · rw [selectorOf, blindAuctionBiddingEndSelectorBytes, hcd]; decide
  · rw [selectorOf, blindAuctionRevealEndSelectorBytes, hcd]; decide
  · rw [selectorOf, blindAuctionEndedSelectorBytes, hcd]; decide

theorem blindAuctionDecode_highestBidder {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldata (highestBidderGetter.params.map Param.name)
      (transitionSignature highestBidderGetter).paramTypes I.calldata = some ∅ := by
  show decodeCalldata [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

/-- `highestBidder()` getter body (pc 418) refines its transition. -/
theorem blindAuctionHighestBidderBodyCore {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = blindAuctionBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hsel : selIs I ⟨#[0x91, 0xf9, 0x01, 0x57]⟩)
    (hreach : ∃ k C, RD blindAuctionBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨418⟩
      [blindAuctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm)
      k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
 :
    runtimeEquivalenceFor blindAuctionConfig blindAuctionContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have _hsize : I.calldata.size < UInt256.size := hsize
  have _hperm : I.perm = true := hperm

  have hsz := blindAuctionHighestBidderSelector_size hsel
  have hd := blindAuctionDispatch_highestBidder (cd := I.calldata) hsel
  have hdec := blindAuctionDecode_highestBidder (I := I) hsz
  by_cases hwv : I.weiValue = ⟨0⟩
  · have hword : highestBidderWord σ_evm I = highestBidderWord σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨5⟩ ⟨0⟩
    have hbody :
        ExecTransitionBody blindAuctionConfig blindAuctionContract
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
          highestBidderGetter.body
          (.returned { contract := blindAuctionContract, locals := ∅ }
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            (some [(.address (AccountAddress.ofNat (highestBidderReturnWord σ_solm I).toNat))])) := by
      simpa [highestBidderWord, highestBidderReturnWord, initState, Solm.EVM.storageLoad,
        State.lookupAccount] using blindAuctionHighestBidderBodyReturns
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
          (by simp only [initState]; exact hwv) (by simp)
    exact (blindAuctionX_highestBidder (g := Sat256.ofUInt256 g) hwv hreach)
      |>.reEquivExecutionTransport hcode hd hdec hbody
        (by simp [highestBidderReturnWord, hword]) hAccounts
        (returnEquiv_of_encode (solcAddressReturnEncoding (addrTy := addr) rfl (highestBidderWord σ_evm I)))
  · have hbody :
        ExecTransitionBody blindAuctionConfig blindAuctionContract
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
          highestBidderGetter.body .reverted := by
      simpa [highestBidderGetter, initState] using
        (bodyReverts_nonPayable (cfg := blindAuctionConfig) (contract := blindAuctionContract)
          (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (locals := (∅ : Store))
          (rest := [.return [(.storage highestBidderRef)]])
          (by simp only [initState]; exact hwv))
    exact (blindAuctionX_highestBidder_nonpayable (g := Sat256.ofUInt256 g) hwv hreach)
      |>.reEquivExecutionRevert hcode hd hdec hbody

end BlindAuction
