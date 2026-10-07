import Benchmarks.Safe.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

variable {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}

theorem safeFallbackBodyCore
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hnonempty : I.calldata.size ≠ 0)
    (hdispatch : selectorDispatchMsg contract I.calldata = none) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  sorry

/-- Unmatched nonempty calldata follows the raw-return fallback. -/
theorem safeFallbackRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hnonempty : I.calldata.size ≠ 0)
    (hdispatch : selectorDispatchMsg contract I.calldata = none) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  exact safeFallbackBodyCore hcode hsize hnonempty hdispatch

end Benchmarks.Safe
