import Benchmarks.Safe.ViaIR.Dispatch
import Benchmarks.Safe.ViaIR.Calldata
import Benchmarks.Safe.ViaIR.IRLengthCheck
import Benchmarks.Safe.ViaIR.Threshold
import Benchmarks.Safe.ViaIR.Blocks.Runtime_027

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 100000

variable {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}

theorem safeChangeThresholdSource (evm : EVM.State) (value : UInt256)
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth : evm.executionEnv.source = evm.executionEnv.codeOwner)
    (hle : value.toNat ≤ (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩).toNat)
    (hnz : value ≠ ⟨0⟩)
    (hperm : evm.executionEnv.perm = true) :
    ExecTransitionBody fork config contract evm (thresholdArgs value) changethresholdTransition.body
      (.returned (resumeAfterInternalCall (thresholdFrame value) "_ok" none)
        (Stele.EVM.storageStore evm evm.executionEnv.codeOwner ⟨4⟩ value) none) := by
  have hcall := internalCallFunctionReturn (caller := thresholdFrame value)
    (name := "changeThresholdBody") (retVar := "_ok") (callee := changeThresholdBodyFunction)
    (evalExprs?_singleton (safeEvalThreshold evm value)) rfl rfl
    (safeThresholdSource (fork := fork) (hperm := by assumption) evm value hle hnz)
  exact .execBlockOK (.consNormal (.requireTrue (evalCallvalueEq_true hvalue))
    (.consNormal (.requireTrue (by simpa [hauth] using safeEvalAuthorized evm _))
      (.consNormal hcall .nil)))

theorem safeChangeThresholdSourceStatic (evm : EVM.State) (value : UInt256)
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth : evm.executionEnv.source = evm.executionEnv.codeOwner)
    (hle : value.toNat ≤ (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩).toNat)
    (hnz : value ≠ ⟨0⟩) (hperm : evm.executionEnv.perm = false) :
    ExecTransitionBody fork config contract evm (thresholdArgs value) changethresholdTransition.body
      .staticViolation := by
  have hcall := ExecStmt.internalCallStatic (fork := fork) (cfg := config) (stele := thresholdFrame value)
    (name := "changeThresholdBody") (retVar := "_ok") (callee :=
      changeThresholdBodyFunction.toCallable)
    (evalExprs?_singleton (safeEvalThreshold evm value)) rfl rfl
    (safeThresholdSourceStatic (fork := fork) evm value hle hnz hperm)
  exact .execBlockStatic (.consNormal (.requireTrue (evalCallvalueEq_true hvalue))
    (.consNormal (.requireTrue (by simpa [hauth] using safeEvalAuthorized evm _)) (.consStatic
      hcall)))

theorem safeChangeThresholdSourceRevert (evm : EVM.State) (value : UInt256)
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth : evm.executionEnv.source = evm.executionEnv.codeOwner)
    (hbody : ExecFuncBody fork config (thresholdFrame value) evm changeThresholdBodyFunction.body
      .reverted) :
    ExecTransitionBody fork config contract evm (thresholdArgs value) changethresholdTransition.body
      .reverted := by
  have hcall := internalCallFunctionRevert (caller := thresholdFrame value)
    (name := "changeThresholdBody") (retVar := "_ok") (callee := changeThresholdBodyFunction)
    (evalExprs?_singleton (safeEvalThreshold evm value)) rfl rfl hbody
  exact .execBlockRevert (.consNormal (.requireTrue (evalCallvalueEq_true hvalue))
    (.consNormal (.requireTrue (by simpa [hauth] using safeEvalAuthorized evm _)) (.consRevert
      hcall)))

theorem safeChangeThresholdUnauthorized (evm : EVM.State) (locals : Store)
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth : evm.executionEnv.source ≠ evm.executionEnv.codeOwner) :
    ExecTransitionBody fork config contract evm locals changethresholdTransition.body .reverted :=
  .execBlockRevert (nonpayableSecondRequireReverts hvalue
    (by simpa [hauth] using safeEvalAuthorized evm _))

theorem safeChangethresholdBodyCore
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some changethresholdTransition) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  obtain ⟨hlong, hword⟩ := selectorDispatchFacts 0x69 0x4e 0x80 0xc3 ⟨0x694e80c3⟩
    hdispatch changethresholdSelectorBytes (by decide)
  obtain ⟨k, C, h5693⟩ := safeReachEntry (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) ⟨0x694e80c3⟩ 10 ⟨5693⟩ hcode hsize hlong hword
    (by native_decide)
  have hlenWord := safeIRArgumentSizeSub hlong hsize
  by_cases hvalue : I.weiValue = ⟨0⟩
  · have h5699 := safeRuntime_block_5693_fallthrough (by simp) hvalue h5693
    by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hlen : 36 ≤ I.calldata.size
      · have h5711 := safeRuntime_block_5699_fallthrough (by simp)
          (by rw [hlenWord]; exact solcDecodeLenCheckOk_4_32 hlen hbig hsize) h5699
        have h9325 := safeRuntime_block_5711 (by simp) (by jump_dest) h5711
        have hdec : config.externalABI.decodeCalldata?
            (changethresholdTransition.params.map Param.name)
            (transitionSignature changethresholdTransition).paramTypes I.calldata =
            some (thresholdArgs (calldataWord I.calldata 4)) := decodeCalldata_uint256_ok hlen hbig
        by_cases hauth : I.source = I.codeOwner
        · obtain ⟨_, _, h5721⟩ := safeAuthorizedTrace h9325 (by simp) hauth (by jump_dest)
          change RD fork safeBytecode I (.ofUInt256 g) (initState σ σ₀ (.ofUInt256 g) A I) ⟨5721⟩
            [calldataWord I.calldata 4, selWord I, ⟨0⟩] _ _ _ σ _ _ at h5721
          by_cases hle : (calldataWord I.calldata 4).toNat ≤ (solcSlotWordAt ⟨3⟩ σ I).toNat
          · by_cases hz : calldataWord I.calldata 4 = ⟨0⟩
            · have hrev := safeThresholdTraceZero (hz ▸ h5721) (by simp)
              have hbody := safeChangeThresholdSourceRevert (fork := fork) (initState σ σ₀ (.ofUInt256 g) A I)
                (calldataWord I.calldata 4) hvalue hauth (hz ▸ safeThresholdSourceZero (fork := fork) _)
              exact RDrev.reEquivElim hcode hrev fun _ _ hΞ ↦
                reEquivSelectorExecution hdispatch hdec hbody (.revert hΞ rfl)
            · obtain ⟨_, _, h5737⟩ := safeThresholdReach h5721 (by simp) hle hz
              cases hperm : I.perm with
              | false =>
                  have hstatic := safeThresholdTraceStatic h5737 (by simp) hperm
                  have hbody := safeChangeThresholdSourceStatic (fork := fork) (initState σ σ₀ (.ofUInt256 g) A I)
                    (calldataWord I.calldata 4) hvalue hauth hle hz hperm
                  exact RDstatic.reEquivElim hcode hstatic fun hΞ ↦
                    reEquivSelectorExecution hdispatch hdec hbody (.staticHalt hΞ rfl)
              | true =>
                  have hret := safeThresholdTrace h5737 (by simp) hperm
                  have hbody := safeChangeThresholdSource (fork := fork) (hperm := by assumption) (initState σ σ₀ (.ofUInt256 g) A I)
                    (calldataWord I.calldata 4) hvalue hauth hle hz
                  refine reEquivReturnElim hcode hret fun _ _ hsuccess ↦ ?_
                  exact reEquivSelectorExecution hdispatch hdec hbody
                    (.success hsuccess rfl (by simp only [storageStore_accountMap]; rfl)
                      (.abi (.fallthrough rfl rfl encodeReturnValues_nil)))
          · have hrev := safeThresholdTraceTooLarge h5721 (by simp) hle
            have hbody := safeChangeThresholdSourceRevert (fork := fork) (initState σ σ₀ (.ofUInt256 g) A I)
              (calldataWord I.calldata 4) hvalue hauth (safeThresholdSourceTooLarge (fork := fork) _ _ hle)
            exact RDrev.reEquivElim hcode hrev fun _ _ hΞ ↦
              reEquivSelectorExecution hdispatch hdec hbody (.revert hΞ rfl)
        · have hrev := safeUnauthorizedTrace h9325 (by simp [safeRuntime_block_5711_stack]) hauth
          exact reEquivSelectorRevert hcode hdispatch hrev fun locals ↦
            safeChangeThresholdUnauthorized _ locals hvalue hauth
      · have h111 := safeRuntime_block_5699_taken (by simp)
          (by
            rw [hlenWord]
            change UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ ≠ ⟨0⟩
            rw [solcDecodeLenCheckShort_4_32 hlong (by omega) hsize]
            decide) (by jump_dest) h5699
        have hrev := safeRuntime_block_111 (by simp) h111
        exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
          (decodeCalldata_uint256_none_short (by omega)) hrev
    · have h111 := safeRuntime_block_5699_taken (by simp)
        (by
          rw [hlenWord]
          change UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ ≠ ⟨0⟩
          rw [solcDecodeLenCheckHuge_4_32 (by omega) hsize]
          decide) (by jump_dest) h5699
      have hrev := safeRuntime_block_111 (by simp) h111
      exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
        (decodeCalldata_uint256_none_huge (by omega)) hrev
  · have h111 := safeRuntime_block_5693_taken (by simp) hvalue (by jump_dest) h5693
    have hrev := safeRuntime_block_111 (by simp) h111
    exact reEquivSelectorRevert hcode hdispatch hrev fun _ ↦ bodyReverts_nonPayable hvalue

/-- Refinement obligation for `changeThreshold` (`changethresholdTransition`). -/
theorem safeChangethresholdRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some changethresholdTransition) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  exact safeChangethresholdBodyCore hcode hsize hdispatch

end Benchmarks.Safe.ViaIR
