import Examples.Ripemd160.Dispatch
import Examples.Precompiles.Ripemd160.Fallback

/-!
# RIPEMD-160 fallback equivalence bridges

These are the fallback cases that connect the bytecode traces to the Solm specification. Pure
bytecode behavior, including the corresponding revert traces, is proved in
`Examples.Precompiles.Ripemd160.Fallback`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Ripemd160

/-- The macro-added nonpayable guard is the first statement of the fallback body. -/
theorem fallbackBodyReverts_nonPayable (evm : EVM.State) (locals : Store)
    (hwv : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecTransitionBody config contract evm locals fallbackTransition.body .reverted := by
  exact bodyReverts_nonPayable hwv

/-- Runtime equivalence for the nonzero-callvalue branch. -/
theorem fallbackNonPayable {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = ripemd160RuntimeBytecode)
    (hwv : I.weiValue ≠ ⟨0⟩) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hrun := ripemd160X_callvalue_ne
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) hcode hwv
  have hequiv :
      runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀
        (Sat256.ofUInt256 g).toUInt256 A I :=
    hrun.reEquivElim hcode fun _ _ hrev => by
    refine runtimeEquivalenceFor.execution
      (returnConvention := .rawBytes) (solmRes := .reverted) hrev ?_ ?_
    · exact solmExec.fallback
        (selectorDispatch_none I.calldata)
        (receiveDispatch_none I.calldata)
        rfl
        (fallback_callargs I.calldata)
        fallback_returnConvention
        rfl
        (fallbackBodyReverts_nonPayable
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (fallbackLocals I)
          (by simpa [initState] using hwv))
    · exact execResultsEquiv.revert rfl rfl
  simpa using hequiv

theorem fallbackAllocationGuard_false (evm : EVM.State)
    (hlarge : maxFallbackCalldataSize < evm.executionEnv.calldata.size) :
    evalExpr? config
      { contract := contract, locals := fallbackLocals evm.executionEnv }
      evm
      (.binary .le
        (.arrayLength .localVar { base := "data", steps := [] })
        (.intLit maxFallbackCalldataSize)) = .ok (.bool false) := by
  unfold maxFallbackCalldataSize at hlarge ⊢
  simp [fallbackLocals, evalExpr?, readLocalPath?, EvalResult.bind, bind, pure,
    evalBinaryOp?] <;> omega

/-- On oversized calldata the explicit fallback guard models Solidity's failed memory copy. -/
theorem fallbackBodyReverts_allocator (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlarge : maxFallbackCalldataSize < evm.executionEnv.calldata.size) :
    ExecTransitionBody config contract evm (fallbackLocals evm.executionEnv)
      fallbackTransition.body .reverted := by
  exact ExecFuncBody.execBlockRevert
    (nonpayableSecondRequireReverts hwv (fallbackAllocationGuard_false evm hlarge))

/-- Runtime equivalence for calldata rejected by Solidity's implicit memory allocator. -/
theorem fallbackOversized {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = ripemd160RuntimeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hlarge : maxFallbackCalldataSize < I.calldata.size) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hrun :
      RDrev ripemd160RuntimeBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) := by
    by_cases hmax : I.calldata.size ≤ 18446744073709551615
    · exact ripemd160X_calldata_rounding_overflow hcode hwv hsize hmax hlarge
    · exact ripemd160X_calldata_gt_u64 hcode hwv hsize (by omega)
  have hequiv :
      runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀
        (Sat256.ofUInt256 g).toUInt256 A I :=
    hrun.reEquivElim hcode fun _ _ hrev => by
      refine runtimeEquivalenceFor.execution
        (returnConvention := .rawBytes) (solmRes := .reverted) hrev ?_ ?_
      · exact solmExec.fallback
          (selectorDispatch_none I.calldata)
          (receiveDispatch_none I.calldata)
          rfl
          (fallback_callargs I.calldata)
          fallback_returnConvention
          rfl
          (fallbackBodyReverts_allocator
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            (by simpa [initState] using hwv)
            (by simpa [initState] using hlarge))
      · exact execResultsEquiv.revert rfl rfl
  simpa using hequiv

end Ripemd160
