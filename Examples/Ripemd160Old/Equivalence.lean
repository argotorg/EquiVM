import Examples.Ripemd160Old.HashTrace
import Examples.Ripemd160.SolmFallback

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 5000000

namespace Ripemd160Old

open Ripemd160

/-- Equivalence for successful zero-value calls accepted by the old allocator. -/
theorem fallbackSuccess {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = runtimeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hrun := runtime_success
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) hcode hwv hsize hsmall
  have hequiv :
      runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀
        (Sat256.ofUInt256 g).toUInt256 A I :=
    hrun.reEquivElim hcode fun g' A' hxi => by
      let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let final := sourceChainRun I.calldata
        (Model.paddedLength I.calldata.size / 64) runtimeInitialChain
      let resultLocals := (fallbackLocals I).insert "digest" (digestBytes20 final)
      have hbody : ExecTransitionBody config contract evmSolm (fallbackLocals I)
          fallbackTransition.body
          (.returned { contract := contract, locals := resultLocals } evmSolm
            (some [.bytes (Model.rawOutput I.calldata)])) := by
        simpa only [evmSolm, final, resultLocals, initState] using
          fallbackBodyReturns evmSolm
            (by simpa [evmSolm, initState] using hwv)
            (by simpa [evmSolm, initState] using hsmall)
      have hsolm : solmExec config contract cA gh bl σ_solm σ₀
          (Sat256.ofUInt256 g).toUInt256 A I
          (.returned { contract := contract, locals := resultLocals } evmSolm
            (some [.bytes (Model.rawOutput I.calldata)])) .rawBytes := by
        exact solmExec.fallback
          (selectorDispatch_none I.calldata)
          (receiveDispatch_none I.calldata)
          rfl
          (fallback_callargs I.calldata)
          fallback_returnConvention
          (by simp [evmSolm, initState])
          hbody
      refine runtimeEquivalenceFor.execution hxi hsolm ?_
      exact execResultsEquiv.success rfl rfl
        (by simp [evmSolm, initState])
        (by simpa [evmSolm, initState] using hAccounts)
        (.rawBytes rfl)
  simpa using hequiv

end Ripemd160Old
