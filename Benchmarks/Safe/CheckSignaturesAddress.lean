import Benchmarks.Safe.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

variable {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}

theorem safeChecksignaturesAddressBytes32BytesBodyCore
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata =
      some checksignaturesAddressBytes32BytesTransition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  sorry

/-- Refinement obligation for `checkSignatures` (`checksignaturesAddressBytes32BytesTransition`). -/
theorem safeChecksignaturesAddressBytes32BytesRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata =
      some checksignaturesAddressBytes32BytesTransition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  exact safeChecksignaturesAddressBytes32BytesBodyCore hcode hsize hdispatch

end Benchmarks.Safe
