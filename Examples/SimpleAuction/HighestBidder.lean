import Examples.SimpleAuction.Storage
import Reasoning.Refinement
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace SimpleAuction

/-! ## `highestBidder()` getter -/

def highestBidderWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)

abbrev highestBidderReturnWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (highestBidderWord σ I) solcAddrMask

theorem simpleAuctionHighestBidderBodyReturns (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hlocals : locals.get? "highestBidder" = none) :
    ExecTransitionBody simpleAuctionConfig simpleAuctionContract evm locals highestBidderGetter.body
      (.returned { contract := simpleAuctionContract, locals := locals } evm
        (some (.address (AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩)
            solcAddrMask).toNat)))) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      have her : evalStorageRef simpleAuctionConfig
          { contract := simpleAuctionContract, locals := locals } evm highestBidderRef =
          .ok { base := "highestBidder", steps := [] } := by
        simp [evalStorageRef, evalStorageRefSteps, highestBidderRef, EvalResult.bind, pure, bind]
      have hty : storageTypeAt? simpleAuctionContract.storage
          ({ base := "highestBidder", steps := [] } : EvaledStorageRef) =
          some (.elem .address) := by
        decide
      rw [evalExpr_storage_scalar (t := .address) (hbase := hlocals) (her := her)
        (hty := hty) (hloc := simpleAuctionConfig_storage_highestBidder),
        simpleAuctionStorageLocLoad_address_offset0])

theorem simpleAuctionHighestBidderSelector_size {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x91, 0xf9, 0x01, 0x57]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x91, 0xf9, 0x01, 0x57]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem simpleAuctionDispatch_highestBidder {cd : ByteArray}
    (hsel : ((⟨#[0x91, 0xf9, 0x01, 0x57]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg simpleAuctionContract cd = some highestBidderGetter := by
  have hcd : cd.extract 0 4 = (⟨#[0x91, 0xf9, 0x01, 0x57]⟩ : ByteArray) :=
    (simpleAuctionByteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [bidTransition, withdrawTransition, auctionEndTransition, beneficiaryGetter,
      auctionEndTimeGetter])
    (post := [highestBidGetter])
    rfl ?_ (by rw [selectorOf, simpleAuctionHighestBidderSelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · rw [selectorOf, simpleAuctionBidSelectorBytes, hcd]; decide
  · rw [selectorOf, simpleAuctionWithdrawSelectorBytes, hcd]; decide
  · rw [selectorOf, simpleAuctionAuctionEndSelectorBytes, hcd]; decide
  · rw [selectorOf, simpleAuctionBeneficiarySelectorBytes, hcd]; decide
  · rw [selectorOf, simpleAuctionAuctionEndTimeSelectorBytes, hcd]; decide

theorem simpleAuctionDecode_highestBidder {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldata (highestBidderGetter.params.map Param.name)
      (transitionSignature highestBidderGetter).paramTypes I.calldata = some ∅ := by
  show decodeCalldata [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem simpleAuctionX_highestBidder {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hreach : ∃ k C, RD simpleAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨274⟩
      [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret simpleAuctionBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (highestBidderReturnWord σ I)) := by
  obtain ⟨_, _, rd274⟩ := hreach
  have rd285 := evm_run rd274 with [
    jumpdest, callvalue, dup1, iszero, push2 ⟨285⟩,
    jumpiT (by rw [hwv]; decide) (by jump_dest)]
  have rd289 := evm_run rd285 with [jumpdest, pop, push1 ⟨2⟩]
  obtain ⟨_, _, rd290⟩ := rd289.sload (by decide) (by evm_ov)
  have rd174 := evm_run rd290 with [
    push2 ⟨174⟩, swap1, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩,
    shl, sub, and, dup2, jump (by jump_dest)]
  obtain ⟨_, _, rd194⟩ := RD.simpleAuctionRoutineEncodeAddress
    (val := UInt256.land solcAddrMask (highestBidderWord σ I)) (ret := ⟨174⟩) (R := [sel])
    rd174 (by simp only [List.length_singleton]; omega)
  have hval : UInt256.land solcAddrMask (highestBidderWord σ I) =
      UInt256.land (highestBidderWord σ I) solcAddrMask :=
    simpleAuctionU256_land_comm solcAddrMask (highestBidderWord σ I)
  have hclean :
      UInt256.land (UInt256.land solcAddrMask (highestBidderWord σ I)) solcAddrMask =
        UInt256.land (highestBidderWord σ I) solcAddrMask := by
    rw [hval]
    exact solcAddrMask_clean (simpleAuctionSolcAddrMask_result_canonical (highestBidderWord σ I))
  have hret := RD.simpleAuctionReturnOneWord194 (R := [⟨174⟩, sel]) rd194
    (by simp only [List.length_cons, List.length_nil]; omega)
  simpa [highestBidderReturnWord, hclean] using hret

theorem simpleAuctionHighestBidderX_nonpayable {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hwv : I.weiValue ≠ ⟨0⟩)
    (hreach : ∃ k C, RD simpleAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨274⟩
      [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev simpleAuctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd274⟩ := hreach
  have rd282 := evm_run rd274 with [
    jumpdest, callvalue, dup1, iszero, push2 ⟨285⟩,
    jumpiNT (isZero_eq_zero_of_ne hwv)]
  exact rd282.revertStub (by decide) (by decide) (by decide) (by simp)

theorem simpleAuctionHighestBidderBody {cA gh bl σ_evm σ₀_evm σ_solm σ₀_solm A I}
    {g : UInt256}
    (hcode : I.code = simpleAuctionBytecode) (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hsel : selIs I ⟨#[0x91, 0xf9, 0x01, 0x57]⟩)
    (hreach : ∃ k C, RD simpleAuctionBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀_evm (Sat256.ofUInt256 g) A I) ⟨274⟩
      [simpleAuctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor simpleAuctionConfig simpleAuctionContract cA gh bl
      σ_evm σ₀_evm σ_solm σ₀_solm g A I := by
  have hsz := simpleAuctionHighestBidderSelector_size hsel
  have hd := simpleAuctionDispatch_highestBidder (cd := I.calldata) hsel
  have hdec := simpleAuctionDecode_highestBidder (I := I) hsz
  by_cases hwv : I.weiValue = ⟨0⟩
  · have hword : highestBidderWord σ_evm I = highestBidderWord σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨2⟩ ⟨0⟩
    have hbody :
        ExecTransitionBody simpleAuctionConfig simpleAuctionContract
          (initState cA gh bl σ_solm σ₀_solm (Sat256.ofUInt256 g) A I) ∅
          highestBidderGetter.body
          (.returned { contract := simpleAuctionContract, locals := ∅ }
            (initState cA gh bl σ_solm σ₀_solm (Sat256.ofUInt256 g) A I)
            (some (.address (AccountAddress.ofNat (highestBidderReturnWord σ_solm I).toNat)))) := by
      simpa [highestBidderWord, highestBidderReturnWord, initState, Solm.EVM.storageLoad,
        State.lookupAccount] using simpleAuctionHighestBidderBodyReturns
          (initState cA gh bl σ_solm σ₀_solm (Sat256.ofUInt256 g) A I) ∅
          (by simp only [initState]; exact hwv) (by simp)
    exact (simpleAuctionX_highestBidder (g := Sat256.ofUInt256 g) hwv hreach)
      |>.reEquivExecutionTransport hcode hd hdec hbody (by simp [highestBidderReturnWord, hword])
        hAccounts
        (returnEquiv_of_encode (simpleAuctionAddressReturnEncoding (highestBidderWord σ_evm I)))
  · have hbody :
        ExecTransitionBody simpleAuctionConfig simpleAuctionContract
          (initState cA gh bl σ_solm σ₀_solm (Sat256.ofUInt256 g) A I) ∅
          highestBidderGetter.body .reverted := by
      simpa [highestBidderGetter, initState] using
        (bodyReverts_nonPayable (cfg := simpleAuctionConfig) (contract := simpleAuctionContract)
          (evm := initState cA gh bl σ_solm σ₀_solm (Sat256.ofUInt256 g) A I)
          (locals := (∅ : Store))
          (rest := [.return (.storage highestBidderRef)])
          (by simp only [initState]; exact hwv))
    exact (simpleAuctionHighestBidderX_nonpayable (g := Sat256.ofUInt256 g) hwv hreach)
      |>.reEquivExecutionRevert hcode hd hdec hbody

end SimpleAuction
