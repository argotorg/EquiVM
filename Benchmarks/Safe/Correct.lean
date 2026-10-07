import Benchmarks.Safe.Constructor
import Benchmarks.Safe.Runtime
import Benchmarks.Safe.Blocks
import Reasoning.Dispatch

/-!
# Safe benchmark correctness stub

The upstream Solidity source tree, optimized runtime bytecode, Solm AST spec, and Solm syntax spec
are present. `Runtime.lean` separates all 31 selectors, receive, and fallback into unconditional
refinement obligations. `Blocks.lean` imports the generated instruction summaries. The runtime
assembly proof remains intentionally unproved. This file also exposes the whole-contract wrapper
that combines the constructor and runtime targets.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Safe

theorem safeCorrect :
    runtimeRefinement config safeBytecode contract := by
  refine ⟨fun σ σ₀ g A I hcode hsize ↦ ?_⟩
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
      · exact safeAddownerwiththresholdRefines hcode hsize hdispatch
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
    contractRefinement config safeCreationBytecode contract :=
  contractRefinement.of_constant safeConstructorCorrect safeCorrect

end Benchmarks.Safe
