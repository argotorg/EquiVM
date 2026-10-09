import Benchmarks.Safe.Dispatch
import Benchmarks.Safe.Decoders
import Benchmarks.Safe.Threshold
import Benchmarks.Safe.Blocks.Runtime_006
import Benchmarks.Safe.Blocks.Runtime_008
import Benchmarks.Safe.Blocks.Runtime_009

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000

variable {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}

theorem safeChangeThresholdSource (evm : EVM.State) (value : UInt256)
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth : evm.executionEnv.source = evm.executionEnv.codeOwner)
    (hle : value.toNat ≤ (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩).toNat)
    (hnz : value ≠ ⟨0⟩) :
    ExecTransitionBody config contract evm (thresholdArgs value) changethresholdTransition.body
      (.returned (resumeAfterInternalCall (thresholdFrame value) "_ok" none)
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨4⟩ value) none) := by
  have hcall := internalCallFunctionReturn (caller := thresholdFrame value)
    (name := "changeThresholdBody") (retVar := "_ok") (callee := changeThresholdBodyFunction)
    (evalExprs?_singleton (safeEvalThreshold evm value)) rfl rfl
    (safeThresholdSource evm value hle hnz)
  exact .execBlockOK (.consNormal (.requireTrue (evalCallvalueEq_true hvalue))
    (.consNormal (.requireTrue (by simpa [hauth] using safeEvalAuthorized evm _))
      (.consNormal hcall .nil)))

theorem safeChangeThresholdSourceStatic (evm : EVM.State) (value : UInt256)
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth : evm.executionEnv.source = evm.executionEnv.codeOwner)
    (hle : value.toNat ≤ (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩).toNat)
    (hnz : value ≠ ⟨0⟩) (hperm : evm.executionEnv.perm = false) :
    ExecTransitionBody config contract evm (thresholdArgs value) changethresholdTransition.body
      .staticViolation := by
  have hcall := ExecStmt.internalCallStatic (cfg := config) (solm := thresholdFrame value)
    (name := "changeThresholdBody") (retVar := "_ok") (callee :=
      changeThresholdBodyFunction.toCallable)
    (evalExprs?_singleton (safeEvalThreshold evm value)) rfl rfl
    (safeThresholdSourceStatic evm value hle hnz hperm)
  exact .execBlockStatic (.consNormal (.requireTrue (evalCallvalueEq_true hvalue))
    (.consNormal (.requireTrue (by simpa [hauth] using safeEvalAuthorized evm _)) (.consStatic
      hcall)))

theorem safeChangeThresholdSourceRevert (evm : EVM.State) (value : UInt256)
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth : evm.executionEnv.source = evm.executionEnv.codeOwner)
    (hbody : ExecFuncBody config (thresholdFrame value) evm changeThresholdBodyFunction.body
      .reverted) :
    ExecTransitionBody config contract evm (thresholdArgs value) changethresholdTransition.body
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
    ExecTransitionBody config contract evm locals changethresholdTransition.body .reverted :=
  .execBlockRevert (nonpayableSecondRequireReverts hvalue
    (by simpa [hauth] using safeEvalAuthorized evm _))

theorem safeChangethresholdBodyCore
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some changethresholdTransition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  obtain ⟨hlong, hword⟩ := selectorDispatchFacts 0x69 0x4e 0x80 0xc3 ⟨0x694e80c3⟩
    hdispatch changethresholdSelectorBytes (by decide)
  obtain ⟨k, C, h1019⟩ := safeReachEntry (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) ⟨0x694e80c3⟩ 3 ⟨1019⟩ hcode hsize hlong hword
    (by native_decide)
  by_cases hvalue : I.weiValue = ⟨0⟩
  · have h1030 := safeRuntime_block_1019_taken (by simp)
      (by rw [hvalue]; decide) (by jump_dest) h1019
    have h9894 := safeRuntime_block_1030 (by simp) (by jump_dest) h1030
    by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hlen : 36 ≤ I.calldata.size
      · obtain ⟨_, _, h1045⟩ := safeDecodeWord h9894 (by simp)
          (solcDecodeLenCheckOk_4_32 hlen hbig hsize) (by jump_dest)
        have h3415 := safeRuntime_block_1045 (by simp) (by jump_dest) h1045
        have h6757 := safeRuntime_block_3415 (by simp) (by jump_dest) h3415
        have hdec : decodeCalldataWithMode config.abiDecodeMode
            (changethresholdTransition.params.map Param.name)
            (transitionSignature changethresholdTransition).paramTypes I.calldata =
            some (thresholdArgs (calldataWord I.calldata 4)) := decodeCalldata_uint256_ok hlen hbig
        by_cases hauth : I.source = I.codeOwner
        · obtain ⟨_, _, h3423⟩ := safeAuthorizedTrace h6757 (by simp) hauth (by jump_dest)
          change RD safeBytecode I (.ofUInt256 g) (initState σ σ₀ (.ofUInt256 g) A I) ⟨3423⟩
            [calldataWord I.calldata 4, ⟨664⟩, selWord I] _ _ _ σ _ _ at h3423
          by_cases hle : (calldataWord I.calldata 4).toNat ≤ (solcSlotWordAt ⟨3⟩ σ I).toNat
          · by_cases hz : calldataWord I.calldata 4 = ⟨0⟩
            · have hrev := safeThresholdTraceZero (hz ▸ h3423) (by simp)
              have hbody := safeChangeThresholdSourceRevert (initState σ σ₀ (.ofUInt256 g) A I)
                (calldataWord I.calldata 4) hvalue hauth (hz ▸ safeThresholdSourceZero _)
              exact RDrev.reEquivElim hcode hrev fun _ _ hΞ ↦
                reEquivSelectorExecution hdispatch hdec hbody (.revert hΞ rfl)
            · obtain ⟨_, _, h3474⟩ := safeThresholdReach h3423 (by simp) hle hz
              cases hperm : I.perm with
              | false =>
                  have hstatic := safeThresholdTraceStatic h3474 (by simp) hperm
                  have hbody := safeChangeThresholdSourceStatic (initState σ σ₀ (.ofUInt256 g) A I)
                    (calldataWord I.calldata 4) hvalue hauth hle hz hperm
                  exact RDstatic.reEquivElim hcode hstatic fun hΞ ↦
                    reEquivSelectorExecution hdispatch hdec hbody (.staticHalt hΞ rfl)
              | true =>
                  obtain ⟨_, _, _, _, h664⟩ := safeThresholdTrace h3474 (by simp) hperm (by
                    jump_dest)
                  have hret := safeRuntime_block_664 (by simp) h664
                  have hbody := safeChangeThresholdSource (initState σ σ₀ (.ofUInt256 g) A I)
                    (calldataWord I.calldata 4) hvalue hauth hle hz
                  refine reEquivReturnElim hcode hret fun _ _ hsuccess ↦ ?_
                  exact reEquivSelectorExecution hdispatch hdec hbody
                    (.success hsuccess rfl (by simp only [storageStore_accountMap]; rfl)
                      (.abi (.fallthrough rfl rfl encodeReturnValues_nil)))
          · have hrev := safeThresholdTraceTooLarge h3423 (by simp) hle
            have hbody := safeChangeThresholdSourceRevert (initState σ σ₀ (.ofUInt256 g) A I)
              (calldataWord I.calldata 4) hvalue hauth (safeThresholdSourceTooLarge _ _ hle)
            exact RDrev.reEquivElim hcode hrev fun _ _ hΞ ↦
              reEquivSelectorExecution hdispatch hdec hbody (.revert hΞ rfl)
        · have hrev := safeUnauthorizedTrace h6757 (by simp [safeRuntime_block_3415_stack]) hauth
          exact reEquivSelectorRevert hcode hdispatch hrev fun locals ↦
            safeChangeThresholdUnauthorized _ locals hvalue hauth
      · have hrev := safeDecodeWordRevert h9894 (by simp)
          (solcDecodeLenCheckShort_4_32 hlong (by omega) hsize)
        exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
          (decodeCalldata_uint256_none_short (by omega)) hrev
    · have hrev := safeDecodeWordRevert h9894 (by simp)
        (solcDecodeLenCheckHuge_4_32 (by omega) hsize)
      exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
        (decodeCalldata_uint256_none_huge (by omega)) hrev
  · have h1027 := safeRuntime_block_1019_fallthrough (by simp)
      (isZero_eq_zero_of_ne hvalue) h1019
    have hrev := safeRuntime_block_1027 (by simp [safeRuntime_block_1019_fallthrough_stack]) h1027
    exact reEquivSelectorRevert hcode hdispatch hrev fun _ ↦ bodyReverts_nonPayable hvalue

/-- Refinement obligation for `changeThreshold` (`changethresholdTransition`). -/
theorem safeChangethresholdRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some changethresholdTransition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  exact safeChangethresholdBodyCore hcode hsize hdispatch

end Benchmarks.Safe
