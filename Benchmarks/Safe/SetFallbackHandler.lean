import Benchmarks.Safe.Dispatch
import Benchmarks.Safe.InternalSetFallbackHandler
import Benchmarks.Safe.Blocks.Runtime_006
import Benchmarks.Safe.Blocks.Runtime_012
import Benchmarks.Safe.Blocks.Runtime_028

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000

variable {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}

theorem safeSetFallbackHandlerSource (evm : EVM.State) (handler : UInt256)
    (hcanon : handler.toNat < EVM.addressModulus)
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth : evm.executionEnv.source = evm.executionEnv.codeOwner)
    (hne : AccountAddress.ofNat handler.toNat ≠ evm.executionEnv.codeOwner) :
    ExecTransitionBody config contract evm (fallbackHandlerArgs handler)
      setfallbackhandlerTransition.body
      (.returned (resumeAfterInternalCall (fallbackHandlerFrame handler) "_ok" none)
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner fallbackHandlerSlot handler) none)
          := by
  have hcall := internalCallFunctionReturn (caller := fallbackHandlerFrame handler)
    (name := "internalSetFallbackHandler") (retVar := "_ok")
    (callee := internalSetFallbackHandlerFunction)
    (evalExprs?_singleton (safeEvalHandler evm handler)) rfl rfl
    (safeInternalSetFallbackHandlerSource evm handler hcanon hne)
  refine .execBlockOK (.consNormal (.requireTrue (evalCallvalueEq_true hvalue))
    (.consNormal (.requireTrue (by simpa [hauth] using safeEvalAuthorized evm _))
      (.consNormal hcall (.consNormal
        (.emit (vals := [.address (AccountAddress.ofNat handler.toNat)]) ?_) .nil))))
  apply evalExprs?_singleton
  simp [resumeAfterInternalCall, fallbackHandlerFrame, fallbackHandlerArgs,
    evalExpr?, EvalResult.ofOption, Std.HashMap.getElem_insert]

theorem safeSetFallbackHandlerSourceStatic (evm : EVM.State) (handler : UInt256)
    (hcanon : handler.toNat < EVM.addressModulus)
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth : evm.executionEnv.source = evm.executionEnv.codeOwner)
    (hne : AccountAddress.ofNat handler.toNat ≠ evm.executionEnv.codeOwner)
    (hperm : evm.executionEnv.perm = false) :
    ExecTransitionBody config contract evm (fallbackHandlerArgs handler)
      setfallbackhandlerTransition.body
      .staticViolation := by
  have hcall := ExecStmt.internalCallStatic (cfg := config) (solm := fallbackHandlerFrame handler)
    (name := "internalSetFallbackHandler") (retVar := "_ok")
    (callee := internalSetFallbackHandlerFunction.toCallable)
    (evalExprs?_singleton (safeEvalHandler evm handler)) rfl rfl
    (safeInternalSetFallbackHandlerStatic evm handler hcanon hne hperm)
  exact .execBlockStatic (.consNormal (.requireTrue (evalCallvalueEq_true hvalue))
    (.consNormal (.requireTrue (by simpa [hauth] using safeEvalAuthorized evm _))
      (.consStatic hcall)))

theorem safeSetFallbackHandlerSourceRevert (evm : EVM.State) (handler : UInt256)
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth : evm.executionEnv.source = evm.executionEnv.codeOwner)
    (heq : AccountAddress.ofNat handler.toNat = evm.executionEnv.codeOwner) :
    ExecTransitionBody config contract evm (fallbackHandlerArgs handler)
      setfallbackhandlerTransition.body
      .reverted := by
  have hcall := internalCallFunctionRevert (caller := fallbackHandlerFrame handler)
    (name := "internalSetFallbackHandler") (retVar := "_ok")
    (callee := internalSetFallbackHandlerFunction)
    (evalExprs?_singleton (safeEvalHandler evm handler)) rfl rfl
    (safeInternalSetFallbackHandlerRevert evm handler heq)
  exact .execBlockRevert (.consNormal (.requireTrue (evalCallvalueEq_true hvalue))
    (.consNormal (.requireTrue (by simpa [hauth] using safeEvalAuthorized evm _))
      (.consRevert hcall)))

theorem safeSetFallbackHandlerUnauthorized (evm : EVM.State) (locals : Store)
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth : evm.executionEnv.source ≠ evm.executionEnv.codeOwner) :
    ExecTransitionBody config contract evm locals setfallbackhandlerTransition.body .reverted :=
  .execBlockRevert (nonpayableSecondRequireReverts hvalue
    (by simpa [hauth] using safeEvalAuthorized evm _))

theorem safeSetFallbackHandlerTrace {I g s0 σ k C} {handler : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨8283⟩ (handler :: ⟨6472⟩ :: handler :: ⟨664⟩ :: R)
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C)
    (hov : R.length + 6 ≤ 1024) (hperm : I.perm = true) :
    RDret safeBytecode g s0 (sstoreAccountMap I.codeOwner σ fallbackHandlerSlot handler)
      ByteArray.empty := by
  obtain ⟨_, _, h6472⟩ := safeInternalFallbackTrace h (by simp; omega) hperm (by jump_dest)
  have h664 := safeRuntime_block_6472 hov hperm (by jump_dest) h6472
  exact safeRuntime_block_664 (by simpa only [safeRuntime_block_6472_stack] using
    (show R.length + 0 ≤ 1024 by omega)) h664

theorem safeSetfallbackhandlerBodyCore
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some setfallbackhandlerTransition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  obtain ⟨hlong, hword⟩ := selectorDispatchFacts 0xf0 0x8a 0x03 0x23 ⟨0xf08a0323⟩
    hdispatch setfallbackhandlerSelectorBytes (by decide)
  obtain ⟨k, C, h1521⟩ := safeReachEntry (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) ⟨0xf08a0323⟩ 3 ⟨1521⟩ hcode hsize hlong hword
    (by native_decide)
  by_cases hvalue : I.weiValue = ⟨0⟩
  · have h1532 := safeRuntime_block_1521_taken (by simp)
      (by rw [hvalue]; decide) (by jump_dest) h1521
    have h9591 := safeRuntime_block_1532 (by simp) (by jump_dest) h1532
    by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hlen : 36 ≤ I.calldata.size
      · have hcheck := solcDecodeLenCheckOk_4_32 hlen hbig hsize
        by_cases hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus
        · obtain ⟨_, _, h1547⟩ := safeDecodeAddress h9591 (by simp) hcheck hcanon (by jump_dest)
          have h6455 := safeRuntime_block_1547 (by simp) (by jump_dest) h1547
          have h6757 := safeRuntime_block_6455 (by simp) (by jump_dest) h6455
          have hdec : decodeCalldataWithMode config.abiDecodeMode
              (setfallbackhandlerTransition.params.map Param.name)
              (transitionSignature setfallbackhandlerTransition).paramTypes I.calldata =
              some (fallbackHandlerArgs (calldataWord I.calldata 4)) :=
            decodeCalldata_address_ok hlen hbig hcanon
          by_cases hauth : I.source = I.codeOwner
          · obtain ⟨_, _, h6463⟩ := safeAuthorizedTrace h6757 (by simp) hauth (by jump_dest)
            have h8250 := safeRuntime_block_6463 (by simp) (by jump_dest) h6463
            by_cases heq : AccountAddress.ofNat (calldataWord I.calldata 4).toNat = I.codeOwner
            · have h8267 := safeRuntime_block_8250_fallthrough (by simp)
                (by rw [safeAddressMask, show (UInt256.ofNat 4).toNat = 4 by rfl,
                      solcAddrMask_clean hcanon]
                    exact u256_sub_eq_zero_iff_eq.mpr
                      ((canonicalAddress_eq_address_iff _ _ hcanon).mp heq)) h8250
              have hrev := safeInternalFallbackTraceRevert h8267 (by simp)
              have hbody := safeSetFallbackHandlerSourceRevert
                (initState σ σ₀ (.ofUInt256 g) A I) (calldataWord I.calldata 4) hvalue hauth heq
              exact RDrev.reEquivElim hcode hrev fun _ _ hΞ ↦
                reEquivSelectorExecution hdispatch hdec hbody (.revert hΞ rfl)
            · have h8283 := safeRuntime_block_8250_taken (by simp)
                (by rw [safeAddressMask, show (UInt256.ofNat 4).toNat = 4 by rfl,
                      solcAddrMask_clean hcanon]
                    exact u256_sub_ne_zero_of_ne
                      (fun hw ↦ heq ((canonicalAddress_eq_address_iff _ _ hcanon).mpr hw)))
                (by jump_dest) h8250
              cases hperm : I.perm with
              | false =>
                  have hstatic := safeInternalFallbackTraceStatic h8283 (by simp) hperm
                  have hbody := safeSetFallbackHandlerSourceStatic
                    (initState σ σ₀ (.ofUInt256 g) A I) (calldataWord I.calldata 4)
                    hcanon hvalue hauth heq hperm
                  exact RDstatic.reEquivElim hcode hstatic fun hΞ ↦
                    reEquivSelectorExecution hdispatch hdec hbody (.staticHalt hΞ rfl)
              | true =>
                  have hret := safeSetFallbackHandlerTrace h8283 (by simp) hperm
                  have hbody := safeSetFallbackHandlerSource
                    (initState σ σ₀ (.ofUInt256 g) A I) (calldataWord I.calldata 4)
                    hcanon hvalue hauth heq
                  refine reEquivReturnElim hcode hret fun _ _ hsuccess ↦ ?_
                  exact reEquivSelectorExecution hdispatch hdec hbody
                    (.success hsuccess rfl (by simp only [storageStore_accountMap]; rfl)
                      (.abi (.fallthrough rfl rfl encodeReturnValues_nil)))
          · have hrev := safeUnauthorizedTrace h6757 (by simp [safeRuntime_block_6455_stack]) hauth
            exact reEquivSelectorRevert hcode hdispatch hrev fun locals ↦
              safeSetFallbackHandlerUnauthorized _ locals hvalue hauth
        · have hrev := safeDecodeAddressNoncanon h9591 (by simp) hcheck hcanon
          exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
            (decodeCalldata_address_none_noncanon hlen hbig hcanon) hrev
      · have hrev := safeDecodeAddressRevert h9591 (by simp)
          (solcDecodeLenCheckShort_4_32 hlong (by omega) hsize)
        exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
          (decodeCalldata_address_none_short hlong (by omega)) hrev
    · have hrev := safeDecodeAddressRevert h9591 (by simp)
        (solcDecodeLenCheckHuge_4_32 (by omega) hsize)
      exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
        (decodeCalldata_address_none_huge (by omega)) hrev
  · have h1529 := safeRuntime_block_1521_fallthrough (by simp)
      (isZero_eq_zero_of_ne hvalue) h1521
    have hrev := safeRuntime_block_1529 (by simp [safeRuntime_block_1521_fallthrough_stack]) h1529
    exact reEquivSelectorRevert hcode hdispatch hrev fun _ ↦ bodyReverts_nonPayable hvalue

/-- Refinement obligation for `setFallbackHandler` (`setfallbackhandlerTransition`). -/
theorem safeSetfallbackhandlerRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some setfallbackhandlerTransition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  exact safeSetfallbackhandlerBodyCore hcode hsize hdispatch

end Benchmarks.Safe
