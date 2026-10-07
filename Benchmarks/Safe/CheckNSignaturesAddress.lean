import Benchmarks.Safe.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

variable {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}

theorem safeChecknsignaturesAddressBytes32BytesUint256BodyCore
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata =
      some checknsignaturesAddressBytes32BytesUint256Transition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  sorry

/-- Refinement obligation for `checkNSignatures`
(`checknsignaturesAddressBytes32BytesUint256Transition`). -/
theorem safeChecknsignaturesAddressBytes32BytesUint256Refines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata =
      some checknsignaturesAddressBytes32BytesUint256Transition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  exact safeChecknsignaturesAddressBytes32BytesUint256BodyCore hcode hsize hdispatch

end Benchmarks.Safe
