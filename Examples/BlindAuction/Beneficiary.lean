import Examples.BlindAuction.Storage
import Reasoning.Refinement
import Reasoning.SolmBody
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Digits.Lemmas

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace BlindAuction

/-! ## `beneficiary()` getter -/

def beneficiaryWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)

abbrev beneficiaryReturnWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (beneficiaryWord σ I) solcAddrMask

theorem blindAuctionBeneficiaryBodyReturns (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hlocals : locals.get? "beneficiary" = none) :
    ExecTransitionBody blindAuctionConfig blindAuctionContract evm locals beneficiaryGetter.body
      (.returned { contract := blindAuctionContract, locals := locals } evm
        (some (.address (AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
            solcAddrMask).toNat)))) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      have her : evalStorageRef blindAuctionConfig
          { contract := blindAuctionContract, locals := locals } evm beneficiaryRef =
          .ok { base := "beneficiary", steps := [] } := by
        simp [evalStorageRef, evalStorageRefSteps, beneficiaryRef, EvalResult.bind, pure, bind]
      have hty : storageTypeAt? blindAuctionContract.storage
          ({ base := "beneficiary", steps := [] } : EvaledStorageRef) =
          some (.elem .address) := by
        decide
      rw [evalExpr_storage_scalar (t := .address) (hbase := hlocals) (her := her)
        (hty := hty) (hloc := blindAuctionConfig_storage_beneficiary),
        blindAuctionStorageLocLoad_address_offset0])

theorem blindAuctionX_beneficiary {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hreach : ∃ k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨278⟩ [blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret blindAuctionBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (beneficiaryReturnWord σ I)) := by
  obtain ⟨_, _, rd278⟩ := hreach
  have rd289 := evm_run rd278 with [
    jumpdest, callvalue, dup1, iszero, push2 ⟨289⟩,
    jumpiT (by rw [hwv]; decide) (by jump_dest)]
  have rd292 := evm_run rd289 with [jumpdest, pop, push0]
  obtain ⟨_, _, rd293₀⟩ := rd292.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd293⟩ :
      ∃ k C, RD blindAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨293⟩
        [beneficiaryWord σ I, blindAuctionSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [beneficiaryWord, initState] using rd293₀⟩
  have rd308 := evm_run rd293 with [
    push2 ⟨308⟩, swap1, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩,
    shl, sub, and, dup2, jump (by jump_dest)]
  obtain ⟨_, _, rd206⟩ := blindAuctionRoutineEncodeAddress308
    (val := UInt256.land solcAddrMask (beneficiaryWord σ I)) (ret := ⟨308⟩)
    (R := [blindAuctionSelWord I]) rd308 (by simp only [List.length_singleton]; omega)
  have hval : UInt256.land solcAddrMask (beneficiaryWord σ I) =
      UInt256.land (beneficiaryWord σ I) solcAddrMask :=
    Reasoning.Theory.u256_land_comm solcAddrMask (beneficiaryWord σ I)
  have hclean : UInt256.land (UInt256.land solcAddrMask (beneficiaryWord σ I)) solcAddrMask =
      beneficiaryReturnWord σ I := by
    rw [hval]
    exact solcAddrMask_clean (solcAddrMask_result_canonical (beneficiaryWord σ I))
  have hret := blindAuctionReturnOneWord206 (R := [⟨308⟩, blindAuctionSelWord I]) rd206
    (by simp only [List.length_cons, List.length_nil]; omega)
  simpa [beneficiaryReturnWord, hclean] using hret

theorem blindAuctionX_beneficiary_nonpayable {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue ≠ ⟨0⟩)
    (hreach : ∃ k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨278⟩ [blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev blindAuctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd278⟩ := hreach
  have rd286 := evm_run rd278 with [
    jumpdest, callvalue, dup1, iszero, push2 ⟨289⟩,
    jumpiNT (isZero_eq_zero_of_ne hwv)]
  exact rd286.revertStub (by decide) (by decide) (by decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem blindAuctionBeneficiarySelector_size {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x38, 0xaf, 0x3e, 0xed]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x38, 0xaf, 0x3e, 0xed]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem blindAuctionDispatch_beneficiary {cd : ByteArray}
    (hsel : ((⟨#[0x38, 0xaf, 0x3e, 0xed]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg blindAuctionContract cd = some beneficiaryGetter := by
  have hcd : cd.extract 0 4 = (⟨#[0x38, 0xaf, 0x3e, 0xed]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [bidTransition, revealTransition, withdrawTransition, auctionEndTransition])
    (post := [biddingEndGetter, revealEndGetter, endedGetter, highestBidderGetter,
      highestBidGetter, bidsGetter])
    rfl rfl ?_ (by rw [selectorOf, blindAuctionBeneficiarySelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl
  · rw [selectorOf, blindAuctionBidSelectorBytes, hcd]; decide
  · rw [selectorOf, blindAuctionRevealSelectorBytes, hcd]; decide
  · rw [selectorOf, blindAuctionWithdrawSelectorBytes, hcd]; decide
  · rw [selectorOf, blindAuctionAuctionEndSelectorBytes, hcd]; decide

theorem blindAuctionDecode_beneficiary {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldata (beneficiaryGetter.params.map Param.name)
      (transitionSignature beneficiaryGetter).paramTypes I.calldata = some ∅ := by
  show decodeCalldata [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

/-- `beneficiary()` getter body (pc 278) refines its transition. -/
theorem blindAuctionBeneficiaryBodyCore {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = blindAuctionBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hsel : selIs I ⟨#[0x38, 0xaf, 0x3e, 0xed]⟩)
    (hreach : ∃ k C, RD blindAuctionBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨278⟩
      [blindAuctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm)
      k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
 :
    runtimeEquivalenceFor blindAuctionConfig blindAuctionContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have _hsize : I.calldata.size < UInt256.size := hsize
  have _hperm : I.perm = true := hperm

  have hsz := blindAuctionBeneficiarySelector_size hsel
  have hd := blindAuctionDispatch_beneficiary (cd := I.calldata) hsel
  have hdec := blindAuctionDecode_beneficiary (I := I) hsz
  by_cases hwv : I.weiValue = ⟨0⟩
  · have hword : beneficiaryWord σ_evm I = beneficiaryWord σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨0⟩ ⟨0⟩
    have hbody :
        ExecTransitionBody blindAuctionConfig blindAuctionContract
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
          beneficiaryGetter.body
          (.returned { contract := blindAuctionContract, locals := ∅ }
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            (some (.address (AccountAddress.ofNat (beneficiaryReturnWord σ_solm I).toNat)))) := by
      simpa [beneficiaryWord, beneficiaryReturnWord, initState, Solm.EVM.storageLoad,
        State.lookupAccount] using blindAuctionBeneficiaryBodyReturns
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
          (by simp only [initState]; exact hwv) (by simp)
    exact (blindAuctionX_beneficiary (g := Sat256.ofUInt256 g) hwv hreach)
      |>.reEquivExecutionTransport hcode hd hdec hbody
        (by simp [beneficiaryReturnWord, hword]) hAccounts
        (returnEquiv_of_encode (solcAddressReturnEncoding (addrTy := addr) rfl (beneficiaryWord σ_evm I)))
  · have hbody :
        ExecTransitionBody blindAuctionConfig blindAuctionContract
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
          beneficiaryGetter.body .reverted := by
      simpa [beneficiaryGetter, initState] using
        (bodyReverts_nonPayable (cfg := blindAuctionConfig) (contract := blindAuctionContract)
          (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (locals := (∅ : Store))
          (rest := [.return (.storage beneficiaryRef)])
          (by simp only [initState]; exact hwv))
    exact (blindAuctionX_beneficiary_nonpayable (g := Sat256.ofUInt256 g) hwv hreach)
      |>.reEquivExecutionRevert hcode hd hdec hbody

end BlindAuction
