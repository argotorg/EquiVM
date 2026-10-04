import Examples.SimpleAuction.Storage
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace SimpleAuction

/-! ## `beneficiary()` getter -/

def beneficiaryWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.get? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.getD ⟨0⟩ ⟨0⟩)

abbrev beneficiaryReturnWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (beneficiaryWord σ I) solcAddrMask

theorem simpleAuctionBeneficiaryBodyReturns (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hlocals : locals.get? "beneficiary" = none) :
    ExecTransitionBody simpleAuctionConfig simpleAuctionContract evm locals beneficiaryGetter.body
      (.returned { contract := simpleAuctionContract, locals := locals } evm
        (some [(.address (AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
            solcAddrMask).toNat))])) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      have her : evalStorageRef simpleAuctionConfig { contract := simpleAuctionContract, locals := locals }
          evm beneficiaryRef = .ok { base := "beneficiary", steps := [] } := by
        simp [evalStorageRef, evalStorageRefSteps, beneficiaryRef, EvalResult.bind, pure, bind]
      have hty : storageTypeAt? simpleAuctionContract.storage
          ({ base := "beneficiary", steps := [] } : EvaledStorageRef) = some (.elem .address) := by
        decide
      rw [evalExpr_storage_scalar (t := .address) (hbase := hlocals) (her := her)
        (hty := hty) (hloc := simpleAuctionConfig_storage_beneficiary)]
      simpa [simpleAuctionAddrLoc] using
        congrArg EvalResult.ok (simpleAuctionStorageLocLoad_address_offset0 evm ⟨0⟩))

theorem simpleAuctionX_beneficiary {σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hreach : ∃ k C, RD simpleAuctionBytecode I g
      (initState σ σ₀ g A I) ⟨144⟩ [simpleAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    RDret simpleAuctionBytecode g (initState σ σ₀ g A I) σ
      (UInt256.toByteArray (beneficiaryReturnWord σ I)) := by
  obtain ⟨_, _, rd144⟩ := hreach
  have rd155 := evm_run rd144 with [
    jumpdest, callvalue, dup1, iszero, push2 ⟨155⟩,
    jumpiT (by rw [hwv]; decide) (by jump_dest) ]
  have rd158 := evm_run rd155 with [jumpdest, pop, push0]
  obtain ⟨_, _, rd159⟩ := rd158.sload (by decide) (by evm_ov)
  have rd174 := evm_run rd159 with [
    push2 ⟨174⟩, swap1, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩,
    shl, sub, and, dup2, jump (by jump_dest) ]
  obtain ⟨_, _, rd194⟩ := RD.simpleAuctionRoutineEncodeAddress
    (val := UInt256.land solcAddrMask (beneficiaryWord σ I)) (ret := ⟨174⟩)
    (R := [simpleAuctionSelWord I]) rd174 (by simp only [List.length_singleton]; omega)
  have hclean : UInt256.land (UInt256.land solcAddrMask (beneficiaryWord σ I)) solcAddrMask =
      beneficiaryReturnWord σ I := by
    rw [u256_land_comm solcAddrMask (beneficiaryWord σ I)]
    exact solcAddrMask_clean (solcAddrMask_result_canonical (beneficiaryWord σ I))
  have hret := RD.simpleAuctionReturnOneWord194 (R := [⟨174⟩, simpleAuctionSelWord I]) rd194
    (by simp only [List.length_cons, List.length_nil]; omega)
  simpa [beneficiaryReturnWord, hclean] using hret

theorem simpleAuctionX_beneficiary_nonzero {σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue ≠ ⟨0⟩)
    (hreach : ∃ k C, RD simpleAuctionBytecode I g
      (initState σ σ₀ g A I) ⟨144⟩ [simpleAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    RDrev simpleAuctionBytecode g (initState σ σ₀ g A I) := by
  obtain ⟨_, _, rd144⟩ := hreach
  exact evm_run rd144 with [
    jumpdest, callvalue, dup1, iszero, push2 ⟨155⟩,
    jumpiNT (isZero_eq_zero_of_ne hwv),
    raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem simpleAuctionBeneficiarySelector_size {I : ExecutionEnv}
    (hsel : ((⟨#[0x38, 0xaf, 0x3e, 0xed]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x38, 0xaf, 0x3e, 0xed]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem simpleAuctionDispatch_beneficiary {cd : ByteArray}
    (hsel : ((⟨#[0x38, 0xaf, 0x3e, 0xed]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg simpleAuctionContract cd = some beneficiaryGetter := by
  have hcd : cd.extract 0 4 = (⟨#[0x38, 0xaf, 0x3e, 0xed]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [bidTransition, withdrawTransition, auctionEndTransition])
    (post := [auctionEndTimeGetter, highestBidderGetter, highestBidGetter])
    rfl rfl ?_ (by rw [selectorOf, simpleAuctionBeneficiarySelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · rw [selectorOf, simpleAuctionBidSelectorBytes, hcd]; decide
  · rw [selectorOf, simpleAuctionWithdrawSelectorBytes, hcd]; decide
  · rw [selectorOf, simpleAuctionAuctionEndSelectorBytes, hcd]; decide

theorem simpleAuctionDecode_beneficiary {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldata (beneficiaryGetter.params.map Param.name)
      (transitionSignature beneficiaryGetter).paramTypes I.calldata = some ∅ := by
  show decodeCalldata [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem simpleAuctionBeneficiaryBody {σ σ₀ A I}
    {g : UInt256}
    (hcode : I.code = simpleAuctionBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hsel : selIs I ⟨#[0x38, 0xaf, 0x3e, 0xed]⟩)
    (hreach : ∃ k C, RD simpleAuctionBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨144⟩
      [simpleAuctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      σ k C) :
    runtimeEquivalenceFor simpleAuctionConfig simpleAuctionContract
      σ σ₀ g A I := by
  have _hsize : I.calldata.size < UInt256.size := hsize
  have _hperm : I.perm = true := hperm
  have hsz := simpleAuctionBeneficiarySelector_size hsel
  have hd := simpleAuctionDispatch_beneficiary (cd := I.calldata) hsel
  have hdec := simpleAuctionDecode_beneficiary (I := I) hsz
  by_cases hwv : I.weiValue = ⟨0⟩
  · have hbody :
        ExecTransitionBody simpleAuctionConfig simpleAuctionContract
          (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅ beneficiaryGetter.body
          (.returned { contract := simpleAuctionContract, locals := ∅ }
            (initState σ σ₀ (Sat256.ofUInt256 g) A I)
            (some [(.address (AccountAddress.ofNat (beneficiaryReturnWord σ I).toNat))])) := by
      simpa [beneficiaryWord, beneficiaryReturnWord, initState, Solm.EVM.storageLoad,
        State.lookupAccount] using simpleAuctionBeneficiaryBodyReturns
          (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅
          (by simp only [initState]; exact hwv) (by simp)
    exact (simpleAuctionX_beneficiary (g := Sat256.ofUInt256 g) hwv hreach)
      |>.reEquivExecutionGen hcode hd hdec hbody (by rfl)
        (returnEquiv_of_encode (solcAddressReturnEncoding (addrTy := addr) rfl (beneficiaryWord σ I)))
  · have hbody :
        ExecTransitionBody simpleAuctionConfig simpleAuctionContract
          (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅ beneficiaryGetter.body
          .reverted := by
      exact bodyReverts_nonPayable (by simp only [initState]; exact hwv)
    exact (simpleAuctionX_beneficiary_nonzero (g := Sat256.ofUInt256 g) hwv hreach)
      |>.reEquivExecutionRevert hcode hd hdec hbody

end SimpleAuction
