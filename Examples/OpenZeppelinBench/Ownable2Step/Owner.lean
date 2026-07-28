import Examples.OpenZeppelinBench.Ownable2Step.Storage
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace OpenZeppelinBench.Ownable2Step

/-! ## `owner()` getter -/

def ownerWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)

abbrev ownerReturnWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (ownerWord σ I) solcAddrMask

theorem ownable2StepOwnerBodyReturns (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hlocals : locals.get? "_owner" = none) :
    ExecTransitionBody config contract evm locals ownerTransition.body
      (.returned { contract := contract, locals := locals } evm
        (some [(.address (AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
            solcAddrMask).toNat))])) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      have her : evalStorageRef config { contract := contract, locals := locals } evm ownerRef =
          .ok { base := "_owner", steps := [] } := by
        simp [evalStorageRef, evalStorageRefSteps, ownerRef, EvalResult.bind, pure, bind]
      have hty : storageTypeAt? contract.storage
          ({ base := "_owner", steps := [] } : EvaledStorageRef) = some (.elem .address) := by
        decide
      rw [evalExpr_storage_scalar (t := .address) (hbase := hlocals) (her := her)
        (hty := hty) (hloc := by rfl), ownable2StepStorageLocLoad_address_offset0])

theorem ownable2StepX_owner {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD ownable2StepBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨107⟩ [ownable2StepSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret ownable2StepBenchBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (ownerReturnWord σ I)) := by
  obtain ⟨_, _, rd107⟩ := hreach
  have rd108 := evm_run rd107 with [jumpdest, push0]
  obtain ⟨_, _, rd109⟩ := rd108.sload (by decide) (by evm_ov)
  have rd119 := evm_run rd109 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and ]
  have hclean :
      UInt256.land (UInt256.land solcAddrMask (ownerWord σ I)) solcAddrMask =
        ownerReturnWord σ I := by
    rw [Reasoning.Theory.u256_land_comm solcAddrMask (ownerWord σ I)]
    exact solcAddrMask_clean (solcAddrMask_result_canonical (ownerWord σ I))
  have hret := RD.ownable2StepReturnAddress119
    (val := UInt256.land solcAddrMask (ownerWord σ I)) (R := [ownable2StepSelWord I])
    rd119 (by simp only [List.length_singleton]; omega)
  simpa [ownerReturnWord, hclean] using hret

theorem ownable2StepOwnerSelector_size {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x8d, 0xa5, 0xcb, 0x5b]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x8d, 0xa5, 0xcb, 0x5b]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem ownable2StepDispatch_owner {cd : ByteArray}
    (hsel : ((⟨#[0x8d, 0xa5, 0xcb, 0x5b]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg contract cd = some ownerTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0x8d, 0xa5, 0xcb, 0x5b]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split (pre := [acceptOwnershipTransition])
    (post := [pendingOwnerTransition, renounceOwnershipTransition, transferOwnershipTransition])
    rfl rfl ?_ (by rw [selectorOf, ownerSelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_singleton] at ht
  subst ht
  rw [selectorOf, acceptOwnershipSelectorBytes, hcd]
  decide

theorem ownable2StepDecode_owner {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldata (ownerTransition.params.map Param.name)
      (transitionSignature ownerTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldata [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem ownable2StepOwnerBody {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = ownable2StepBenchBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x8d, 0xa5, 0xcb, 0x5b]⟩)
    (hreach : ∃ k C, RD ownable2StepBenchBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨107⟩
      [ownable2StepSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have _hsize : I.calldata.size < UInt256.size := hsize
  have _hperm : I.perm = true := hperm
  have hsz := ownable2StepOwnerSelector_size hsel
  have hd := ownable2StepDispatch_owner (cd := I.calldata) hsel
  have hdec := ownable2StepDecode_owner (I := I) hsz
  have hword : ownerWord σ_evm I = ownerWord σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨0⟩ ⟨0⟩
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ ownerTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.address (AccountAddress.ofNat (ownerReturnWord σ_solm I).toNat))])) := by
    simpa [ownerWord, ownerReturnWord, initState, Solm.EVM.storageLoad, State.lookupAccount] using
      ownable2StepOwnerBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (by simp only [initState]; exact hwv) (by simp)
  exact (ownable2StepX_owner (g := Sat256.ofUInt256 g) hreach)
    |>.reEquivExecutionTransport hcode hd hdec hbody
      (by simp [ownerReturnWord, hword]) hAccounts
      (returnEquiv_of_encode (solcAddressReturnEncoding (addrTy := addr) rfl (ownerWord σ_evm I)))

end OpenZeppelinBench.Ownable2Step
