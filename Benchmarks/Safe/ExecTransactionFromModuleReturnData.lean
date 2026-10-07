import Benchmarks.Safe.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

variable {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}

theorem safeExectransactionfrommodulereturndataBodyCore
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata =
      some exectransactionfrommodulereturndataTransition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  sorry

/-- Refinement obligation for `execTransactionFromModuleReturnData`
(`exectransactionfrommodulereturndataTransition`). -/
theorem safeExectransactionfrommodulereturndataRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata =
      some exectransactionfrommodulereturndataTransition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  exact safeExectransactionfrommodulereturndataBodyCore hcode hsize hdispatch

end Benchmarks.Safe
