import Benchmarks.Safe.ViaIR.Dispatch
import Benchmarks.Safe.ViaIR.InternalSetFallbackHandler
import Benchmarks.Safe.ViaIR.IRLengthCheck
import Benchmarks.Safe.ViaIR.Blocks.Runtime_004
import Benchmarks.Safe.ViaIR.Blocks.Runtime_007

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 100000

variable {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}

theorem safeSetFallbackHandlerSource (evm : EVM.State) (handler : UInt256)
    (hcanon : handler.toNat < EVM.addressModulus)
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth : evm.executionEnv.source = evm.executionEnv.codeOwner)
    (hne : AccountAddress.ofNat handler.toNat ≠ evm.executionEnv.codeOwner)
    (hperm : evm.executionEnv.perm = true) :
    ExecTransitionBody fork config contract evm (fallbackHandlerArgs handler)
      setfallbackhandlerTransition.body
      (.returned (resumeAfterInternalCall (fallbackHandlerFrame handler) "_ok" none)
        (Stele.EVM.storageStore evm evm.executionEnv.codeOwner fallbackHandlerSlot handler) none)
          := by
  have hcall := internalCallFunctionReturn (caller := fallbackHandlerFrame handler)
    (name := "internalSetFallbackHandler") (retVar := "_ok")
    (callee := internalSetFallbackHandlerFunction)
    (evalExprs?_singleton (safeEvalHandler evm handler)) rfl rfl
    (safeInternalSetFallbackHandlerSource (fork := fork) (hperm := by assumption) evm handler hcanon hne)
  refine .execBlockOK (.consNormal (.requireTrue (evalCallvalueEq_true hvalue))
    (.consNormal (.requireTrue (by simpa [hauth] using safeEvalAuthorized evm _))
      (.consNormal hcall (.consNormal
        (.emit (hperm := by simpa only [storageStore_executionEnv] using hperm) (vals := [.address (AccountAddress.ofNat handler.toNat)]) ?_) .nil))))
  apply evalExprs?_singleton
  simp [resumeAfterInternalCall, fallbackHandlerFrame, fallbackHandlerArgs,
    evalExpr?, EvalResult.ofOption, Std.HashMap.getElem_insert]

theorem safeSetFallbackHandlerSourceStatic (evm : EVM.State) (handler : UInt256)
    (hcanon : handler.toNat < EVM.addressModulus)
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth : evm.executionEnv.source = evm.executionEnv.codeOwner)
    (hne : AccountAddress.ofNat handler.toNat ≠ evm.executionEnv.codeOwner)
    (hperm : evm.executionEnv.perm = false) :
    ExecTransitionBody fork config contract evm (fallbackHandlerArgs handler)
      setfallbackhandlerTransition.body
      .staticViolation := by
  have hcall := ExecStmt.internalCallStatic (fork := fork) (cfg := config) (stele := fallbackHandlerFrame handler)
    (name := "internalSetFallbackHandler") (retVar := "_ok")
    (callee := internalSetFallbackHandlerFunction.toCallable)
    (evalExprs?_singleton (safeEvalHandler evm handler)) rfl rfl
    (safeInternalSetFallbackHandlerStatic (fork := fork) evm handler hcanon hne hperm)
  exact .execBlockStatic (.consNormal (.requireTrue (evalCallvalueEq_true hvalue))
    (.consNormal (.requireTrue (by simpa [hauth] using safeEvalAuthorized evm _))
      (.consStatic hcall)))

theorem safeSetFallbackHandlerSourceRevert (evm : EVM.State) (handler : UInt256)
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth : evm.executionEnv.source = evm.executionEnv.codeOwner)
    (heq : AccountAddress.ofNat handler.toNat = evm.executionEnv.codeOwner) :
    ExecTransitionBody fork config contract evm (fallbackHandlerArgs handler)
      setfallbackhandlerTransition.body
      .reverted := by
  have hcall := internalCallFunctionRevert (fork := fork) (caller := fallbackHandlerFrame handler)
    (name := "internalSetFallbackHandler") (retVar := "_ok")
    (callee := internalSetFallbackHandlerFunction)
    (evalExprs?_singleton (safeEvalHandler evm handler)) rfl rfl
    (safeInternalSetFallbackHandlerRevert (fork := fork) evm handler heq)
  exact .execBlockRevert (.consNormal (.requireTrue (evalCallvalueEq_true hvalue))
    (.consNormal (.requireTrue (by simpa [hauth] using safeEvalAuthorized evm _))
      (.consRevert hcall)))

theorem safeSetFallbackHandlerUnauthorized (evm : EVM.State) (locals : Store)
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth : evm.executionEnv.source ≠ evm.executionEnv.codeOwner) :
    ExecTransitionBody fork config contract evm locals setfallbackhandlerTransition.body .reverted :=
  .execBlockRevert (nonpayableSecondRequireReverts hvalue
    (by simpa [hauth] using safeEvalAuthorized evm _))

theorem safeSetFallbackHandlerTrace {I g s0 σ k C} {handler : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨10692⟩ (handler :: ⟨1106⟩ :: handler :: ⟨0⟩ :: R)
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C)
    (hov : R.length + 6 ≤ 1024) (hperm : I.perm = true) :
    RDret fork safeBytecode g s0 (sstoreAccountMap I.codeOwner σ fallbackHandlerSlot handler)
      ByteArray.empty := by
  obtain ⟨_, _, h1106⟩ := safeInternalFallbackTrace h (by simp; omega) hperm (by jump_dest)
  have hret := safeRuntime_block_1106 (by omega) hperm h1106
  simpa only [show (⟨0⟩ : UInt256).toNat = 0 from rfl, byteArray_readWithPadding_zero] using hret

theorem safeSetfallbackhandlerBodyCore
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some setfallbackhandlerTransition) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  obtain ⟨hlong, hword⟩ := selectorDispatchFacts 0xf0 0x8a 0x03 0x23 ⟨0xf08a0323⟩
    hdispatch setfallbackhandlerSelectorBytes (by decide)
  obtain ⟨k, C, h1063⟩ := safeReachEntry (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) ⟨0xf08a0323⟩ 26 ⟨1063⟩ hcode hsize hlong hword
    (by native_decide)
  have hlenWord := safeIRArgumentSizeSub hlong hsize
  by_cases hvalue : I.weiValue = ⟨0⟩
  · have h1070 := safeRuntime_block_1063_fallthrough (by simp) hvalue h1063
    simp only [safeRuntime_block_1063_fallthrough_stack] at h1070
    by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hlen : 36 ≤ I.calldata.size
      · have h1082 := safeRuntime_block_1070_fallthrough (by simp)
          (by rw [hlenWord]; exact solcDecodeLenCheckOk_4_32 hlen hbig hsize) h1070
        have h6952 := safeRuntime_block_1082 (by simp) (by jump_dest) h1082
        by_cases hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus
        · obtain ⟨_, _, h1089⟩ := safeDecodeAddress h6952
            (by simp [safeRuntime_block_1082_stack]) hcanon (by jump_dest)
          have h9325 := safeRuntime_block_1089 (by simp) (by jump_dest) h1089
          have hdec : config.externalABI.decodeCalldata?
              (setfallbackhandlerTransition.params.map Param.name)
              (transitionSignature setfallbackhandlerTransition).paramTypes I.calldata =
              some (fallbackHandlerArgs (calldataWord I.calldata 4)) :=
            decodeCalldata_address_ok hlen hbig hcanon
          by_cases hauth : I.source = I.codeOwner
          · obtain ⟨_, _, h1097⟩ := safeAuthorizedTrace h9325 (by simp) hauth (by jump_dest)
            have h10675 := safeRuntime_block_1097 (by simp) (by jump_dest) h1097
            by_cases heq : AccountAddress.ofNat (calldataWord I.calldata 4).toNat = I.codeOwner
            · have h10727 := safeRuntime_block_10675_taken (by simp)
                (by
                  rw [safeAddressMask, solcAddrMask_clean hcanon,
                    (canonicalAddress_eq_address_iff _ _ hcanon).mp heq, uInt256_eq_self]
                  decide) (by jump_dest) h10675
              have hrev := safeInternalFallbackTraceRevert h10727
                (by simp [safeRuntime_block_1097_stack])
              have hbody := safeSetFallbackHandlerSourceRevert (fork := fork)
                (initState σ σ₀ (.ofUInt256 g) A I) (calldataWord I.calldata 4) hvalue hauth heq
              exact RDrev.reEquivElim hcode hrev fun _ _ hΞ ↦
                reEquivSelectorExecution hdispatch hdec hbody (.revert hΞ rfl)
            · have h10692 := safeRuntime_block_10675_fallthrough (by simp)
                (by
                  rw [safeAddressMask, solcAddrMask_clean hcanon]
                  exact uInt256_eq_zero_of_ne (fun hw ↦ heq
                    ((canonicalAddress_eq_address_iff _ _ hcanon).mpr
                      (uInt256_eq_one_eq hw).symm))) h10675
              cases hperm : I.perm with
              | false =>
                  have hstatic := safeInternalFallbackTraceStatic h10692 (by simp) hperm
                  have hbody := safeSetFallbackHandlerSourceStatic (fork := fork)
                    (initState σ σ₀ (.ofUInt256 g) A I) (calldataWord I.calldata 4)
                    hcanon hvalue hauth heq hperm
                  exact RDstatic.reEquivElim hcode hstatic fun hΞ ↦
                    reEquivSelectorExecution hdispatch hdec hbody (.staticHalt hΞ rfl)
              | true =>
                  have hret := safeSetFallbackHandlerTrace h10692 (by simp) hperm
                  have hbody := safeSetFallbackHandlerSource (fork := fork) (hperm := by assumption)
                    (initState σ σ₀ (.ofUInt256 g) A I) (calldataWord I.calldata 4)
                    hcanon hvalue hauth heq
                  refine reEquivReturnElim hcode hret fun _ _ hsuccess ↦ ?_
                  exact reEquivSelectorExecution hdispatch hdec hbody
                    (.success hsuccess rfl (by simp only [storageStore_accountMap]; rfl)
                      (.abi (.fallthrough rfl rfl encodeReturnValues_nil)))
          · have hrev := safeUnauthorizedTrace h9325 (by simp [safeRuntime_block_1089_stack]) hauth
            exact reEquivSelectorRevert hcode hdispatch hrev fun locals ↦
              safeSetFallbackHandlerUnauthorized _ locals hvalue hauth
        · have hrev := safeDecodeAddressNoncanon h6952
            (by simp [safeRuntime_block_1082_stack]) hcanon
          exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
            (decodeCalldata_address_none_noncanon hlen hbig hcanon) hrev
      · have h589 := safeRuntime_block_1070_taken (by simp)
          (by
            rw [hlenWord]
            change UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ ≠ ⟨0⟩
            rw [solcDecodeLenCheckShort_4_32 hlong (by omega) hsize]
            decide) (by jump_dest) h1070
        have hrev := safeRuntime_block_589 (by simp) h589
        exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
          (decodeCalldata_address_none_short hlong (by omega)) hrev
    · have h589 := safeRuntime_block_1070_taken (by simp)
        (by
          rw [hlenWord]
          change UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ ≠ ⟨0⟩
          rw [solcDecodeLenCheckHuge_4_32 (by omega) hsize]
          decide) (by jump_dest) h1070
      have hrev := safeRuntime_block_589 (by simp) h589
      exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
        (decodeCalldata_address_none_huge (by omega)) hrev
  · have h589 := safeRuntime_block_1063_taken (by simp) hvalue (by jump_dest) h1063
    have hrev := safeRuntime_block_589 (by simp) h589
    exact reEquivSelectorRevert hcode hdispatch hrev fun _ ↦ bodyReverts_nonPayable hvalue

/-- Refinement obligation for `setFallbackHandler` (`setfallbackhandlerTransition`). -/
theorem safeSetfallbackhandlerRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some setfallbackhandlerTransition) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  exact safeSetfallbackhandlerBodyCore hcode hsize hdispatch

end Benchmarks.Safe.ViaIR
