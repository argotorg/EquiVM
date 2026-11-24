import Benchmarks.Safe.ViaIR.Constructor
import Benchmarks.Safe.ViaIR.Runtime
import Benchmarks.Safe.ViaIR.Blocks
import Reasoning.Dispatch

variable {fork : Ethereum.Fork}

/-!
# Safe via-IR refinement

`Runtime.lean` provides the 31 selector, receive, and fallback refinement proofs for the pinned
via-IR bytecode. The runtime and whole-contract wrappers use the approved existing-account
predicate required by owner insertion. The constructor proof has no additional account premise.
`Blocks.lean` imports the generated instruction summaries used by the bytecode traces.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Safe.ViaIR

theorem safeCorrect :
    runtimeRefinementWithWF (fun σ I ↦ σ.get? I.codeOwner ≠ none) noGasBound
      config safeBytecode contract := by
  refine ⟨fun fork _hfork σ σ₀ g A I hcode hsize haccount _ ↦ ?_⟩
  by_cases hempty : I.calldata.size = 0
  · exact safeReceiveRefines hcode hempty
  cases hdispatch : selectorDispatchMsg contract I.calldata with
  | none => exact safeFallbackRefines hcode hsize hempty hdispatch
  | some t =>
      have hmem := dispatchList_some_mem
        ((selectorDispatchMsg_eq_dispatchList contract I.calldata).symm.trans hdispatch)
      simp only [contract, transitions, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact safeVersionRefines hcode hsize hdispatch
      · exact safeAddownerwiththresholdRefines hcode hsize haccount hdispatch
      · exact safeApprovehashRefines hcode hsize hdispatch
      · exact safeApprovedhashesRefines hcode hsize hdispatch
      · exact safeChangethresholdRefines hcode hsize hdispatch
      · exact safeChecknsignaturesRefines hcode hsize hdispatch
      · exact safeChecknsignaturesAddressBytes32BytesUint256Refines hcode hsize hdispatch
      · exact safeChecksignaturesRefines hcode hsize hdispatch
      · exact safeChecksignaturesAddressBytes32BytesRefines hcode hsize hdispatch
      · exact safeDisablemoduleRefines hcode hsize hdispatch
      · exact safeDomainseparatorRefines hcode hsize hdispatch
      · exact safeEnablemoduleRefines hcode hsize hdispatch
      · exact safeExectransactionRefines hcode hsize hdispatch
      · exact safeExectransactionfrommoduleRefines hcode hsize hdispatch
      · exact safeExectransactionfrommodulereturndataRefines hcode hsize hdispatch
      · exact safeGetmodulespaginatedRefines hcode hsize hdispatch
      · exact safeGetownersRefines hcode hsize hdispatch
      · exact safeGetstorageatRefines hcode hsize hdispatch
      · exact safeGetthresholdRefines hcode hsize hdispatch
      · exact safeGettransactionhashRefines hcode hsize hdispatch
      · exact safeIsmoduleenabledRefines hcode hsize hdispatch
      · exact safeIsownerRefines hcode hsize hdispatch
      · exact safeNonceRefines hcode hsize hdispatch
      · exact safeRemoveownerRefines hcode hsize hdispatch
      · exact safeSetfallbackhandlerRefines hcode hsize hdispatch
      · exact safeSetguardRefines hcode hsize hdispatch
      · exact safeSetmoduleguardRefines hcode hsize hdispatch
      · exact safeSetupRefines hcode hsize hdispatch
      · exact safeSignedmessagesRefines hcode hsize hdispatch
      · exact safeSimulateandrevertRefines hcode hsize hdispatch
      · exact safeSwapownerRefines hcode hsize hdispatch

theorem safeContractCorrect :
    contractRefinementWF (fun σ I ↦ σ.get? I.codeOwner ≠ none) noGasBound
      config safeCreationBytecode contract :=
  contractRefinementWF.of_constant safeConstructorCorrect safeCorrect

end Benchmarks.Safe.ViaIR
