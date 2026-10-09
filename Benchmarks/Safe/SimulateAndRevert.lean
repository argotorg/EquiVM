import Benchmarks.Safe.Dispatch
import Benchmarks.Safe.SimulateTrace
import Benchmarks.Safe.SimulateSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

variable {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}

set_option maxRecDepth 100000 in
theorem safeSimulateandrevertBodyCore
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some simulateandrevertTransition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  obtain ⟨hlong, hword⟩ := selectorDispatchFacts 0xb4 0xfa 0xba 0x09 ⟨0xb4faba09⟩
    hdispatch simulateandrevertSelectorBytes (by decide)
  obtain ⟨k, C, hentry⟩ := safeReachEntry (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) ⟨0xb4faba09⟩ 1 ⟨1208⟩ hcode hsize hlong hword
    (by native_decide)
  have hrev := safeSimulateReverts hentry (by simp)
  refine RDrev.reEquivElim hcode hrev fun _ _ hΞ ↦ ?_
  cases hdec : decodeCalldata ["targetContract", "calldataPayload"] [abiAddress, .bytes]
      I.calldata with
  | none => exact .decodingFailed hdispatch rfl hdec hΞ
  | some args =>
      obtain ⟨target, payload, rfl⟩ := decodeAddressBytesShape hdec
      exact reEquivSelectorExecution hdispatch hdec
        (safeSimulateSource (initState σ σ₀ (.ofUInt256 g) A I) target payload)
        (.revert hΞ rfl)

/-- Refinement obligation for `simulateAndRevert` (`simulateandrevertTransition`). -/
theorem safeSimulateandrevertRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some simulateandrevertTransition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  exact safeSimulateandrevertBodyCore hcode hsize hdispatch

end Benchmarks.Safe
