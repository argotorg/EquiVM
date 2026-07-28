import Examples.SimpleAuction.Storage
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace SimpleAuction

/-! ## `auctionEndTime()` getter -/

def auctionEndTimeWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)

theorem simpleAuctionAuctionEndTimeBodyReturns (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hlocals : locals.get? "auctionEndTime" = none) :
    ExecTransitionBody simpleAuctionConfig simpleAuctionContract evm locals auctionEndTimeGetter.body
      (.returned { contract := simpleAuctionContract, locals := locals } evm
        (some [(.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat))])) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      have her : evalStorageRef simpleAuctionConfig { contract := simpleAuctionContract, locals := locals }
          evm auctionEndTimeRef = .ok { base := "auctionEndTime", steps := [] } := by
        simp [evalStorageRef, evalStorageRefSteps, auctionEndTimeRef, EvalResult.bind, pure, bind]
      have hty : storageTypeAt? simpleAuctionContract.storage
          ({ base := "auctionEndTime", steps := [] } : EvaledStorageRef)
          = some (.elem (.int uint256Int)) := by
        decide
      rw [evalExpr_storage_scalar (t := .int uint256Int) (hbase := hlocals) (her := her)
        (hty := hty) (hloc := simpleAuctionConfig_storage_auctionEndTime),
        simpleAuctionStorageLocLoad_uint256])

theorem simpleAuctionX_auctionEndTime {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hreach : ∃ k C, RD simpleAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨239⟩
      [simpleAuctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    RDret simpleAuctionBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (auctionEndTimeWord σ I)) := by
  obtain ⟨_, _, rd239⟩ := hreach
  have rd257 := evm_run rd239 with [
    jumpdest, callvalue, dup1, iszero, push2 ⟨250⟩,
    jumpiT (by rw [hwv]; decide) (by jump_dest),
    jumpdest, pop, push2 ⟨260⟩, push1 ⟨1⟩ ]
  obtain ⟨_, _, rd258₀⟩ := rd257.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd258⟩ :
      ∃ k C, RD simpleAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨258⟩
        [auctionEndTimeWord σ I, ⟨260⟩, simpleAuctionSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionEndTimeWord, initState] using rd258₀⟩
  have rd260 := evm_run rd258 with [
    dup2, jump (by jump_dest) ]
  have rd194 := evm_run rd260 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost
      solcFreePtrMem_mload64
      (by decide) (by evm_ov),
    swap1, dup2,
    raw mstore 6 (solcReturnMem (auctionEndTimeWord σ I)) (UInt256.ofNat 5)
      (by decide) mem_cost
      (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]; rfl)
      (by decide) (by evm_ov),
    push1 ⟨32⟩, add, push2 ⟨194⟩, jump (by jump_dest) ]
  exact evm_run rd194 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by decide)
      mem_cost
      (solcReturnMem_mload64 (auctionEndTimeWord σ I))
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray (auctionEndTimeWord σ I)) (by decide)
      mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          simpleAuctionSubRet32_toNat]
        simpa using solcReturnMem_read128 (auctionEndTimeWord σ I))
      (by evm_ov) ]

theorem simpleAuctionX_auctionEndTime_nonpayable {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue ≠ ⟨0⟩)
    (hreach : ∃ k C, RD simpleAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨239⟩
      [simpleAuctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    RDrev simpleAuctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd239⟩ := hreach
  have rd247 := evm_run rd239 with [
    jumpdest, callvalue, dup1, iszero, push2 ⟨250⟩,
    jumpiNT (isZero_eq_zero_of_ne hwv) ]
  exact rd247.revertStub (by decide) (by decide) (by decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem simpleAuctionAuctionEndTimeSelector_size {I : ExecutionEnv}
    (hsel : ((⟨#[0x4b, 0x44, 0x9c, 0xba]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x4b, 0x44, 0x9c, 0xba]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem simpleAuctionDispatch_auctionEndTime {cd : ByteArray}
    (hsel : ((⟨#[0x4b, 0x44, 0x9c, 0xba]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg simpleAuctionContract cd = some auctionEndTimeGetter := by
  have hcd : cd.extract 0 4 = (⟨#[0x4b, 0x44, 0x9c, 0xba]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [bidTransition, withdrawTransition, auctionEndTransition, beneficiaryGetter])
    (post := [highestBidderGetter, highestBidGetter])
    rfl rfl ?_ (by rw [selectorOf, simpleAuctionAuctionEndTimeSelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl
  · rw [selectorOf, simpleAuctionBidSelectorBytes, hcd]; decide
  · rw [selectorOf, simpleAuctionWithdrawSelectorBytes, hcd]; decide
  · rw [selectorOf, simpleAuctionAuctionEndSelectorBytes, hcd]; decide
  · rw [selectorOf, simpleAuctionBeneficiarySelectorBytes, hcd]; decide

theorem simpleAuctionDecode_auctionEndTime {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldata (auctionEndTimeGetter.params.map Param.name)
      (transitionSignature auctionEndTimeGetter).paramTypes I.calldata = some ∅ := by
  show decodeCalldata [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem simpleAuctionAuctionEndTimeBody {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = simpleAuctionBytecode) (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hsel : selIs I ⟨#[0x4b, 0x44, 0x9c, 0xba]⟩)
    (hreach : ∃ k C, RD simpleAuctionBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨239⟩
      [simpleAuctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor simpleAuctionConfig simpleAuctionContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := simpleAuctionAuctionEndTimeSelector_size hsel
  have hd := simpleAuctionDispatch_auctionEndTime (cd := I.calldata) hsel
  have hdec := simpleAuctionDecode_auctionEndTime (I := I) hsz
  by_cases hwv : I.weiValue = ⟨0⟩
  · have hword : auctionEndTimeWord σ_evm I = auctionEndTimeWord σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨1⟩ ⟨0⟩
    have hbody :
        ExecTransitionBody simpleAuctionConfig simpleAuctionContract
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
          auctionEndTimeGetter.body
          (.returned { contract := simpleAuctionContract, locals := ∅ }
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            (some [(.int (Int.ofNat (auctionEndTimeWord σ_solm I).toNat))])) := by
      simpa [auctionEndTimeWord, initState, Solm.EVM.storageLoad, State.lookupAccount] using
        simpleAuctionAuctionEndTimeBodyReturns
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
          (by simp only [initState]; exact hwv) (by simp)
    exact (simpleAuctionX_auctionEndTime (g := Sat256.ofUInt256 g) hwv hreach)
      |>.reEquivExecutionTransport hcode hd hdec hbody (by rw [hword]) hAccounts
        (returnEquiv_of_encode (uint256ReturnEncoding (auctionEndTimeWord σ_evm I)))
  · have hbody :
        ExecTransitionBody simpleAuctionConfig simpleAuctionContract
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
          auctionEndTimeGetter.body .reverted := by
      simpa [auctionEndTimeGetter] using
        bodyReverts_nonPayable (cfg := simpleAuctionConfig) (contract := simpleAuctionContract)
          (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (locals := (∅ : Store)) (rest := [.return [(.storage auctionEndTimeRef)]])
          (by simp only [initState]; exact hwv)
    exact (simpleAuctionX_auctionEndTime_nonpayable (g := Sat256.ofUInt256 g) hwv hreach)
      |>.reEquivExecutionRevert hcode hd hdec hbody

end SimpleAuction
