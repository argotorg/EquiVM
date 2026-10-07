import Benchmarks.Safe.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

variable {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}

theorem safeAddownerwiththresholdBodyCore
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some addownerwiththresholdTransition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  sorry

/-- Refinement obligation for `addOwnerWithThreshold` (`addownerwiththresholdTransition`). -/
theorem safeAddownerwiththresholdRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some addownerwiththresholdTransition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  exact safeAddownerwiththresholdBodyCore hcode hsize hdispatch

end Benchmarks.Safe
