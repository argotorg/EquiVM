import Examples.OpenZeppelinBench.Ownable2Step.Storage
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace OpenZeppelinBench.Ownable2Step

/-! ## `pendingOwner()` getter -/

def pendingOwnerWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.get? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.getD ⟨1⟩ ⟨0⟩)

abbrev pendingOwnerReturnWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (pendingOwnerWord σ I) solcAddrMask

theorem ownable2StepPendingOwnerBodyReturns (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hlocals : locals.get? "_pendingOwner" = none) :
    ExecTransitionBody config contract evm locals pendingOwnerTransition.body
      (.returned { contract := contract, locals := locals } evm
        (some [(.address (AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
            solcAddrMask).toNat))])) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      have her : evalStorageRef config { contract := contract, locals := locals } evm
          pendingOwnerRef = .ok { base := "_pendingOwner", steps := [] } := by
        simp [evalStorageRef, evalStorageRefSteps, pendingOwnerRef, EvalResult.bind, pure, bind]
      have hty : storageTypeAt? contract.storage
          ({ base := "_pendingOwner", steps := [] } : EvaledStorageRef) =
          some (.elem .address) := by
        decide
      rw [evalExpr_storage_scalar (t := .address) (hbase := hlocals) (her := her)
        (hty := hty) (hloc := by rfl), ownable2StepStorageLocLoad_address_offset0])

theorem ownable2StepPendingOwnerSelector_size {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0xe3, 0x0c, 0x39, 0x78]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0xe3, 0x0c, 0x39, 0x78]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem ownable2StepDispatch_pendingOwner {cd : ByteArray}
    (hsel : ((⟨#[0xe3, 0x0c, 0x39, 0x78]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg contract cd = some pendingOwnerTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0xe3, 0x0c, 0x39, 0x78]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split (pre := [acceptOwnershipTransition, ownerTransition])
    (post := [renounceOwnershipTransition, transferOwnershipTransition])
    rfl rfl ?_ (by rw [selectorOf, pendingOwnerSelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · rw [selectorOf, acceptOwnershipSelectorBytes, hcd]; decide
  · rw [selectorOf, ownerSelectorBytes, hcd]; decide

theorem ownable2StepDecode_pendingOwner {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldata (pendingOwnerTransition.params.map Param.name)
      (transitionSignature pendingOwnerTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldata [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem ownable2StepX_pendingOwner {σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD ownable2StepBenchBytecode I g
      (initState σ σ₀ g A I) ⟨147⟩ [ownable2StepSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    RDret ownable2StepBenchBytecode g (initState σ σ₀ g A I) σ
      (UInt256.toByteArray (pendingOwnerReturnWord σ I)) := by
  obtain ⟨_, _, rd147⟩ := hreach
  have rd150 := evm_run rd147 with [jumpdest, push1 ⟨1⟩]
  obtain ⟨_, _, rd151⟩ := rd150.sload (by decide) (by evm_ov)
  have rd119 := evm_run rd151 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and,
    push2 ⟨119⟩, jump (by jump_dest) ]
  have hclean :
      UInt256.land (UInt256.land solcAddrMask (pendingOwnerWord σ I)) solcAddrMask =
        pendingOwnerReturnWord σ I := by
    rw [Reasoning.Theory.u256_land_comm solcAddrMask (pendingOwnerWord σ I)]
    exact solcAddrMask_clean (solcAddrMask_result_canonical (pendingOwnerWord σ I))
  have hret := RD.ownable2StepReturnAddress119
    (val := UInt256.land solcAddrMask (pendingOwnerWord σ I)) (R := [ownable2StepSelWord I])
    rd119 (by simp only [List.length_singleton]; omega)
  simpa [pendingOwnerReturnWord, hclean] using hret

theorem ownable2StepPendingOwnerBody
    {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = ownable2StepBenchBytecode) (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xe3, 0x0c, 0x39, 0x78]⟩)
    (hreach : ∃ k C, RD ownable2StepBenchBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨147⟩
      [ownable2StepSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      σ k C) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsz := ownable2StepPendingOwnerSelector_size hsel
  have hd := ownable2StepDispatch_pendingOwner (cd := I.calldata) hsel
  have hdec := ownable2StepDecode_pendingOwner (I := I) hsz
  have hbody :
      ExecTransitionBody config contract
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅
        pendingOwnerTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.address (AccountAddress.ofNat (pendingOwnerReturnWord σ I).toNat))])) := by
    simpa [pendingOwnerWord, pendingOwnerReturnWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using ownable2StepPendingOwnerBodyReturns
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅
        (by simp only [initState]; exact hwv) (by simp)
  exact (ownable2StepX_pendingOwner (g := Sat256.ofUInt256 g) hreach)
    |>.reEquivExecution hcode hd hdec hbody
      (returnEquiv_of_encode (solcAddressReturnEncoding (addrTy := addr) rfl (pendingOwnerWord σ I)))

end OpenZeppelinBench.Ownable2Step
