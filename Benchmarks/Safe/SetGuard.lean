import Benchmarks.Safe.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

variable {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}

theorem safeSetguardBodyCore
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some setguardTransition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  sorry

/-- Refinement obligation for `setGuard` (`setguardTransition`). -/
theorem safeSetguardRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some setguardTransition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  exact safeSetguardBodyCore hcode hsize hdispatch

end Benchmarks.Safe
