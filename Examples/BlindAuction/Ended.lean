import Examples.BlindAuction.Storage
import Reasoning.Refinement
import Reasoning.SolmBody
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Digits.Lemmas

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace BlindAuction

/-! ## `ended()` getter -/

def endedWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨3⟩ ⟨0⟩)

abbrev endedMaskedWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land ⟨255⟩ (endedWord σ I)

abbrev endedReturnWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.isZero (UInt256.isZero (endedMaskedWord σ I))

theorem blindAuctionEndedBodyReturns (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hlocals : locals.get? "ended" = none) :
    ExecTransitionBody blindAuctionConfig blindAuctionContract evm locals endedGetter.body
      (.returned { contract := blindAuctionContract, locals := locals } evm
        (some [(wordToElem .bool
          (UInt256.land ⟨255⟩ (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩)))])) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      have her : evalStorageRef blindAuctionConfig
          { contract := blindAuctionContract, locals := locals } evm endedRef =
          .ok { base := "ended", steps := [] } := by
        simp [evalStorageRef, evalStorageRefSteps, endedRef, EvalResult.bind, pure, bind]
      have hty : storageTypeAt? blindAuctionContract.storage
          ({ base := "ended", steps := [] } : EvaledStorageRef) = some (.elem .bool) := by
        decide
      rw [evalExpr_storage_scalar (t := .bool) (hbase := hlocals) (her := her)
        (hty := hty) (hloc := blindAuctionConfig_storage_ended),
        blindAuctionStorageLocLoad_bool_offset0])

theorem blindAuctionX_ended {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hreach : ∃ k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨215⟩ [blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret blindAuctionBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (endedReturnWord σ I)) := by
  obtain ⟨_, _, rd215⟩ := hreach
  have rd228 := evm_run rd215 with [
    jumpdest, callvalue, dup1, iszero, push2 ⟨226⟩,
    jumpiT (by rw [hwv]; decide) (by jump_dest),
    jumpdest, pop, push1 ⟨3⟩]
  obtain ⟨_, _, rd231₀⟩ := rd228.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd231⟩ :
      ∃ k C, RD blindAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨231⟩
        [endedWord σ I, blindAuctionSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [endedWord, initState] using rd231₀⟩
  have rd240 := evm_run rd231 with [
    push2 ⟨240⟩, swap1, push1 ⟨255⟩, and, dup2, jump (by jump_dest)]
  have rd206 := evm_run rd240 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost
      solcFreePtrMem_mload64
      (by decide) (by evm_ov),
    swap1, iszero, iszero, dup2,
    raw mstore 6 (solcReturnMem (endedReturnWord σ I)) (UInt256.ofNat 5)
      (by decide) mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]
        rfl)
      (by decide) (by evm_ov),
    push1 ⟨32⟩, add, push2 ⟨206⟩, jump (by jump_dest)]
  exact blindAuctionReturnOneWord206 (R := [⟨240⟩, blindAuctionSelWord I]) rd206
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem blindAuctionX_ended_nonpayable {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue ≠ ⟨0⟩)
    (hreach : ∃ k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨215⟩ [blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev blindAuctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd215⟩ := hreach
  have rd223 := evm_run rd215 with [
    jumpdest, callvalue, dup1, iszero, push2 ⟨226⟩,
    jumpiNT (isZero_eq_zero_of_ne hwv)]
  exact rd223.revertStub (by decide) (by decide) (by decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem blindAuctionEndedSelector_size {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x12, 0xfa, 0x6f, 0xeb]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x12, 0xfa, 0x6f, 0xeb]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem blindAuctionDispatch_ended {cd : ByteArray}
    (hsel : ((⟨#[0x12, 0xfa, 0x6f, 0xeb]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg blindAuctionContract cd = some endedGetter := by
  have hcd : cd.extract 0 4 = (⟨#[0x12, 0xfa, 0x6f, 0xeb]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [bidTransition, revealTransition, withdrawTransition, auctionEndTransition,
      beneficiaryGetter, biddingEndGetter, revealEndGetter])
    (post := [highestBidderGetter, highestBidGetter, bidsGetter])
    rfl rfl ?_ (by rw [selectorOf, blindAuctionEndedSelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [selectorOf, blindAuctionBidSelectorBytes, hcd]; decide
  · rw [selectorOf, blindAuctionRevealSelectorBytes, hcd]; decide
  · rw [selectorOf, blindAuctionWithdrawSelectorBytes, hcd]; decide
  · rw [selectorOf, blindAuctionAuctionEndSelectorBytes, hcd]; decide
  · rw [selectorOf, blindAuctionBeneficiarySelectorBytes, hcd]; decide
  · rw [selectorOf, blindAuctionBiddingEndSelectorBytes, hcd]; decide
  · rw [selectorOf, blindAuctionRevealEndSelectorBytes, hcd]; decide

theorem blindAuctionDecode_ended {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldata (endedGetter.params.map Param.name)
      (transitionSignature endedGetter).paramTypes I.calldata = some ∅ := by
  show decodeCalldata [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

/-- `ended()` getter body (pc 215) refines its transition. -/
theorem blindAuctionEndedBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = blindAuctionBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hsel : selIs I ⟨#[0x12, 0xfa, 0x6f, 0xeb]⟩)
    (hreach : ∃ k C, RD blindAuctionBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨215⟩
      [blindAuctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm)
      k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
 :
    runtimeEquivalenceFor blindAuctionConfig blindAuctionContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have _hsize : I.calldata.size < UInt256.size := hsize
  have _hperm : I.perm = true := hperm

  have hsz := blindAuctionEndedSelector_size hsel
  have hd := blindAuctionDispatch_ended (cd := I.calldata) hsel
  have hdec := blindAuctionDecode_ended (I := I) hsz
  by_cases hwv : I.weiValue = ⟨0⟩
  · have hword : endedWord σ_evm I = endedWord σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨3⟩ ⟨0⟩
    have hbody :
        ExecTransitionBody blindAuctionConfig blindAuctionContract
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
          endedGetter.body
          (.returned { contract := blindAuctionContract, locals := ∅ }
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            (some [(wordToElem .bool (endedMaskedWord σ_solm I))])) := by
      simpa [endedWord, endedMaskedWord, initState, Solm.EVM.storageLoad, State.lookupAccount] using
        blindAuctionEndedBodyReturns
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
          (by simp only [initState]; exact hwv) (by simp)
    exact (blindAuctionX_ended (g := Sat256.ofUInt256 g) hwv hreach)
      |>.reEquivExecutionTransport hcode hd hdec hbody (by simp [endedMaskedWord, hword])
        hAccounts
        (returnEquiv_of_encode (abit := boolTy)
          (rv := wordToElem .bool (endedMaskedWord σ_evm I))
          (o := UInt256.toByteArray (endedReturnWord σ_evm I))
          (by
            rw [endedReturnWord, endedMaskedWord]
            rw [Reasoning.Theory.u256_land_comm ⟨255⟩ (endedWord σ_evm I)]
            simpa [boolTy] using boolWordReturnEncoding (endedWord σ_evm I)))
  · have hbody :
        ExecTransitionBody blindAuctionConfig blindAuctionContract
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
          endedGetter.body .reverted := by
      simpa [endedGetter, initState] using
        (bodyReverts_nonPayable (cfg := blindAuctionConfig) (contract := blindAuctionContract)
          (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (locals := (∅ : Store))
          (rest := [.return [(.storage endedRef)]])
          (by simp only [initState]; exact hwv))
    exact (blindAuctionX_ended_nonpayable (g := Sat256.ofUInt256 g) hwv hreach)
      |>.reEquivExecutionRevert hcode hd hdec hbody

end BlindAuction
