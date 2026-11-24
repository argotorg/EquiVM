import Benchmarks.Dss.Dai.Dispatch
import Benchmarks.Dss.Dai.Storage

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Dai

/-! ## ABI decode and source-level body for `DOMAIN_SEPARATOR()` -/

abbrev domainSeparatorStore : Store :=
  ∅

abbrev domainSeparatorStorageSlot : UInt256 :=
  ⟨5⟩

def domainSeparatorWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.get? I.codeOwner |>.option ⟨0⟩
    (fun acc => acc.storage.getD domainSeparatorStorageSlot ⟨0⟩)

theorem daiDecode_domainSeparator_ok {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) :
    config.externalABI.decodeCalldata?
      (domainSeparatorTransition.params.map Param.name)
      (transitionSignature domainSeparatorTransition).paramTypes I.calldata =
        some domainSeparatorStore := by
  change decodeCalldataWithMode .legacySolc05 [] [] I.calldata =
    some (∅ : Store)
  exact decodeCalldataWithMode_empty_ok hsz4

/-- The Stele `DOMAIN_SEPARATOR()` body returns the bytes32 storage slot `5`. -/
theorem daiDomainSeparatorBodyReturns (evm : EVM.State)
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody fork config contract evm domainSeparatorStore domainSeparatorTransition.body
      (.returned { contract := contract, locals := domainSeparatorStore } evm
        (some [(.fixedBytes bytes32Width
          (EVM.Word.toBytesBE
            (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner
              domainSeparatorStorageSlot)))])) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      rw [evalExpr_storage_scalar_value (hbackend := rfl)
        (cfg := config)
        (stele := { contract := contract, locals := domainSeparatorStore })
        (slot := domainSeparatorRef)
        (er := ({ base := "DOMAIN_SEPARATOR", steps := [] } : EvaledStorageRef))
        (t := .bytes bytes32Width)
        (loc := wordLoc domainSeparatorStorageSlot (.bytes bytes32Width))
        (value := .fixedBytes bytes32Width
          (EVM.Word.toBytesBE
            (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner
              domainSeparatorStorageSlot)))
        (hbase := by
          simp [domainSeparatorStore, domainSeparatorRef])
        (her := by
          simp [evalStorageRef, domainSeparatorRef, domainSeparatorStore, EvalResult.bind,
            bind, pure])
        (hty := by
          simp [storageTypeAt?, contract, storageDecls, bytes32St])
        (hloc := by rfl)
        (hload := by
          simpa [wordLoc, bytes32Loc, bytes32Width] using
            storageLocLoad_bytes32 evm domainSeparatorStorageSlot)])

/-! ## EVM trace -/

theorem daiX_domainSeparator_ok {σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD fork daiBytecode I g
      (initState σ σ₀ g A I) ⟨634⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    RDret fork daiBytecode g (initState σ σ₀ g A I) σ
      (UInt256.toByteArray (domainSeparatorWord σ I)) := by
  exact RD.daiWordGetterExternal
    (entry := ⟨634⟩) (returnPc := ⟨524⟩) (routine := ⟨2005⟩)
    (slot := domainSeparatorStorageSlot)
    hreach
    dai_getter_entry_wf
    dai_word_slot_getter_wf
    (by jump_dest)
    (by jump_dest)
    dai_return_word_from_mem_wf

theorem daiDomainSeparatorBodyCoreOk
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = daiBytecode) (_hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some domainSeparatorTransition)
    (hdecode :
      config.externalABI.decodeCalldata?
        (domainSeparatorTransition.params.map Param.name)
        (transitionSignature domainSeparatorTransition).paramTypes I.calldata =
          some domainSeparatorStore)
    (hreach : ∃ k C, RD fork daiBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨634⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  have hbody :
      ExecTransitionBody fork config contract
        (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        domainSeparatorStore
        domainSeparatorTransition.body
        (.returned { contract := contract, locals := domainSeparatorStore }
          (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.fixedBytes bytes32Width
            (EVM.Word.toBytesBE (domainSeparatorWord σ I)))])) := by
    simpa [domainSeparatorWord, domainSeparatorStorageSlot, initState,
      Stele.EVM.storageLoad, State.lookupAccount] using
      daiDomainSeparatorBodyReturns
        (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (by simp only [initState]; exact hwv)
  exact (daiX_domainSeparator_ok (g := Sat256.ofUInt256 g) hreach)
    |>.reEquivExecution hcode hdispatch hdecode hbody
      (returnEquiv_of_encode
        (by simpa [bytes32, bytes32Width] using
          bytes32ReturnEncoding (domainSeparatorWord σ I)))

/-- `DOMAIN_SEPARATOR()` body refines its Stele transition. -/
theorem daiDomainSeparatorBodyCore {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = daiBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (daiSelBytes 6)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (daiSelBytes 6) (by native_decide) hsel
  have hdispatch : dispatchMsg contract I.calldata = some domainSeparatorTransition :=
    daiDispatchDomainSeparator hsel
  have hreach := daiReachDomainSeparatorBody (fork := fork)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  exact daiDomainSeparatorBodyCoreOk hcode hsize hwv hdispatch
    (daiDecode_domainSeparator_ok hsz4) hreach

end Benchmarks.Dss.Dai
