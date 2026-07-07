import Benchmarks.Dss.Dai.Dispatch
import Benchmarks.Dss.Dai.Storage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.Dss.Dai

/-! ## ABI decode and source-level body for `DOMAIN_SEPARATOR()` -/

abbrev domainSeparatorStore : Store :=
  ∅

abbrev domainSeparatorStorageSlot : UInt256 :=
  ⟨5⟩

def domainSeparatorWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩
    (fun acc => acc.storage.findD domainSeparatorStorageSlot ⟨0⟩)

theorem daiDecode_domainSeparator_ok {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode
      (domainSeparatorTransition.params.map Param.name)
      (transitionSignature domainSeparatorTransition).paramTypes I.calldata =
        some domainSeparatorStore := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata =
    some (∅ : Store)
  exact decodeCalldataWithMode_empty_ok hsz4

/-- The Solm `DOMAIN_SEPARATOR()` body returns the bytes32 storage slot `5`. -/
theorem daiDomainSeparatorBodyReturns (evm : EVM.State)
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract evm domainSeparatorStore domainSeparatorTransition.body
      (.returned { contract := contract, locals := domainSeparatorStore } evm
        (some [(.fixedBytes bytes32Width
          (EVM.Word.toBytesBE
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
              domainSeparatorStorageSlot)))])) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      rw [evalExpr_storage_scalar_value
        (cfg := config)
        (solm := { contract := contract, locals := domainSeparatorStore })
        (slot := domainSeparatorRef)
        (er := ({ base := "DOMAIN_SEPARATOR", steps := [] } : EvaledStorageRef))
        (t := .bytes bytes32Width)
        (loc := wordLoc domainSeparatorStorageSlot (.bytes bytes32Width))
        (value := .fixedBytes bytes32Width
          (EVM.Word.toBytesBE
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
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

theorem daiX_domainSeparator_ok {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD daiBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨634⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret daiBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
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
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = daiBytecode) (_hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some domainSeparatorTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode
        (domainSeparatorTransition.params.map Param.name)
        (transitionSignature domainSeparatorTransition).paramTypes I.calldata =
          some domainSeparatorStore)
    (hreach : ∃ k C, RD daiBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨634⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hword : domainSeparatorWord σ_evm I = domainSeparatorWord σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner domainSeparatorStorageSlot ⟨0⟩
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        domainSeparatorStore
        domainSeparatorTransition.body
        (.returned { contract := contract, locals := domainSeparatorStore }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.fixedBytes bytes32Width
            (EVM.Word.toBytesBE (domainSeparatorWord σ_solm I)))])) := by
    simpa [domainSeparatorWord, domainSeparatorStorageSlot, initState,
      Solm.EVM.storageLoad, State.lookupAccount] using
      daiDomainSeparatorBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (by simp only [initState]; exact hwv)
  exact (daiX_domainSeparator_ok (g := Sat256.ofUInt256 g) hreach)
    |>.reEquivExecutionTransport hcode hdispatch hdecode hbody (by rw [← hword])
      hAccounts
      (returnEquiv_of_encode
        (by simpa [bytes32, bytes32Width] using
          bytes32ReturnEncoding (domainSeparatorWord σ_evm I)))

/-- `DOMAIN_SEPARATOR()` body refines its Solm transition. -/
theorem daiDomainSeparatorBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = daiBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (daiSelBytes 6))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (daiSelBytes 6) (by native_decide) hsel
  have hdispatch : dispatchMsg contract I.calldata = some domainSeparatorTransition :=
    daiDispatchDomainSeparator hsel
  have hreach := daiReachDomainSeparatorBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  exact daiDomainSeparatorBodyCoreOk hcode hsize hwv hdispatch
    (daiDecode_domainSeparator_ok hsz4) hreach hAccounts

end Benchmarks.Dss.Dai
