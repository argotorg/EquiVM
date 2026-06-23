import Examples.SimpleAuction.Storage
import Reasoning.Refinement
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace SimpleAuction

def highestBidWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨3⟩ ⟨0⟩)

theorem simpleAuctionHighestBidBodyReturns (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hlocals : locals.get? "highestBid" = none) :
    ExecTransitionBody simpleAuctionConfig simpleAuctionContract evm locals highestBidGetter.body
      (.returned { contract := simpleAuctionContract, locals := locals } evm
        (some (.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩).toNat)))) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      have her : evalStorageRef simpleAuctionConfig
          { contract := simpleAuctionContract, locals := locals } evm highestBidRef =
          .ok { base := "highestBid", steps := [] } := by
        simp [evalStorageRef, evalStorageRefSteps, highestBidRef, EvalResult.bind, pure, bind]
      have hty : storageTypeAt? simpleAuctionContract.storage
          ({ base := "highestBid", steps := [] } : EvaledStorageRef) =
          some (.elem (.int uint256Int)) := by
        decide
      rw [evalExpr_storage_scalar (t := .int uint256Int) (hbase := hlocals) (her := her)
        (hty := hty) (hloc := simpleAuctionConfig_storage_highestBid)]
      rw [simpleAuctionStorageLocLoad_uint256])

theorem simpleAuctionX_highestBid_callvalue_ne {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD simpleAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨305⟩
      [simpleAuctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev simpleAuctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd305⟩ := hreach
  exact evm_run rd305 with [
    jumpdest, callvalue, dup1, iszero, push2 ⟨316⟩,
    jumpiNT (isZero_eq_zero_of_ne hwv),
    raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem simpleAuctionX_highestBid {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD simpleAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨305⟩
      [simpleAuctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hwv : I.weiValue = ⟨0⟩) :
    RDret simpleAuctionBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (highestBidWord σ I)) := by
  obtain ⟨_, _, rd305⟩ := hreach
  have rd323 := evm_run rd305 with [
    jumpdest, callvalue, dup1, iszero, push2 ⟨316⟩,
    jumpiT (by rw [hwv]; decide) (by jump_dest),
    jumpdest, pop, push2 ⟨260⟩, push1 ⟨3⟩ ]
  obtain ⟨_, _, rd324⟩ := rd323.sload (by decide) (by evm_ov)
  have rd260 := evm_run rd324 with [
    dup2, jump (by jump_dest) ]
  have rd194 := evm_run rd260 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost
      solcFreePtrMem_mload64
      (by decide) (by evm_ov),
    swap1, dup2,
    raw mstore 6 (solcReturnMem (highestBidWord σ I)) (UInt256.ofNat 5) (by decide)
      mem_cost
      (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]; rfl)
      (by decide) (by evm_ov),
    push1 ⟨32⟩, add, push2 ⟨194⟩, jump (by jump_dest) ]
  exact evm_run rd194 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by decide)
      mem_cost
      (solcReturnMem_mload64 (highestBidWord σ I))
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray (highestBidWord σ I)) (by decide)
      mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show (UInt256.sub ((⟨32⟩ : UInt256) + ⟨128⟩) ⟨128⟩).toNat = 32 from by decide,
          solcReturnMem_read128])
      (by evm_ov) ]

theorem simpleAuctionHighestBidSelector_size {I : ExecutionEnv}
    (hsel : ((⟨#[0xd5, 0x7b, 0xde, 0x79]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0xd5, 0x7b, 0xde, 0x79]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem simpleAuctionDispatch_highestBid {cd : ByteArray}
    (hsel : ((⟨#[0xd5, 0x7b, 0xde, 0x79]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg simpleAuctionContract cd = some highestBidGetter := by
  have hcd : cd.extract 0 4 = (⟨#[0xd5, 0x7b, 0xde, 0x79]⟩ : ByteArray) :=
    (simpleAuctionByteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [bidTransition, withdrawTransition, auctionEndTransition, beneficiaryGetter,
      auctionEndTimeGetter, highestBidderGetter])
    (post := []) rfl ?_ (by rw [selectorOf, simpleAuctionHighestBidSelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [selectorOf, simpleAuctionBidSelectorBytes, hcd]; decide
  · rw [selectorOf, simpleAuctionWithdrawSelectorBytes, hcd]; decide
  · rw [selectorOf, simpleAuctionAuctionEndSelectorBytes, hcd]; decide
  · rw [selectorOf, simpleAuctionBeneficiarySelectorBytes, hcd]; decide
  · rw [selectorOf, simpleAuctionAuctionEndTimeSelectorBytes, hcd]; decide
  · rw [selectorOf, simpleAuctionHighestBidderSelectorBytes, hcd]; decide

theorem simpleAuctionDecode_highestBid {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldata (highestBidGetter.params.map Param.name)
      (transitionSignature highestBidGetter).paramTypes I.calldata = some ∅ := by
  show decodeCalldata [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem simpleAuctionHighestBidBody {cA gh bl σ_evm σ₀_evm σ_solm σ₀_solm A I}
    {g : UInt256}
    (hcode : I.code = simpleAuctionBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hsel : selIs I ⟨#[0xd5, 0x7b, 0xde, 0x79]⟩)
    (hreach : ∃ k C, RD simpleAuctionBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀_evm (Sat256.ofUInt256 g) A I) ⟨305⟩
      [simpleAuctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor simpleAuctionConfig simpleAuctionContract cA gh bl
      σ_evm σ₀_evm σ_solm σ₀_solm g A I := by
  have hsel' : ((⟨#[0xd5, 0x7b, 0xde, 0x79]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs] using hsel
  have hsz := simpleAuctionHighestBidSelector_size hsel'
  have hd := simpleAuctionDispatch_highestBid (cd := I.calldata) hsel'
  have hdec := simpleAuctionDecode_highestBid (I := I) hsz
  by_cases hwv : I.weiValue = ⟨0⟩
  · have hword : highestBidWord σ_evm I = highestBidWord σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨3⟩ ⟨0⟩
    have hbody :
        ExecTransitionBody simpleAuctionConfig simpleAuctionContract
          (initState cA gh bl σ_solm σ₀_solm (Sat256.ofUInt256 g) A I) ∅
          highestBidGetter.body
          (.returned { contract := simpleAuctionContract, locals := ∅ }
            (initState cA gh bl σ_solm σ₀_solm (Sat256.ofUInt256 g) A I)
            (some (.int (Int.ofNat (highestBidWord σ_solm I).toNat)))) := by
      simpa [highestBidWord, initState, Solm.EVM.storageLoad, State.lookupAccount] using
        simpleAuctionHighestBidBodyReturns
          (initState cA gh bl σ_solm σ₀_solm (Sat256.ofUInt256 g) A I) ∅
          (by simp only [initState]; exact hwv) (by simp)
    exact (simpleAuctionX_highestBid (g := Sat256.ofUInt256 g) hreach hwv)
      |>.reEquivExecutionTransport hcode hd hdec hbody (by rw [hword]) hAccounts
        (returnEquiv_of_encode (uint256ReturnEncoding (highestBidWord σ_evm I)))
  · have hbody :
        ExecTransitionBody simpleAuctionConfig simpleAuctionContract
          (initState cA gh bl σ_solm σ₀_solm (Sat256.ofUInt256 g) A I) ∅
          highestBidGetter.body .reverted :=
      bodyReverts_nonPayable (by simp only [initState]; exact hwv)
    exact (simpleAuctionX_highestBid_callvalue_ne (g := Sat256.ofUInt256 g) hreach hwv)
      |>.reEquivExecutionRevert hcode hd hdec hbody

end SimpleAuction
