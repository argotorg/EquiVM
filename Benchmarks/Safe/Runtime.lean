import Benchmarks.Safe.Bytecode
import Solm.Refine

/-!
Proof scaffolds for every Safe runtime entrypoint. All obligations retain the unqualified
refinement relation: arbitrary account maps, calldata (including decoding failures), call value,
gas, call depth, and either permission mode. Bodies are intentionally unproved.
-/

open Solm Ethereum Ethereum.EVM

namespace Benchmarks.Safe

section Runtime

variable {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}


/-- Refinement obligation for `VERSION` (`versionTransition`). -/
theorem safeVersionRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some versionTransition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  sorry

/-- Refinement obligation for `addOwnerWithThreshold` (`addownerwiththresholdTransition`). -/
theorem safeAddownerwiththresholdRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some addownerwiththresholdTransition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  sorry

/-- Refinement obligation for `approveHash` (`approvehashTransition`). -/
theorem safeApprovehashRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some approvehashTransition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  sorry

/-- Refinement obligation for `approvedHashes` (`approvedhashesTransition`). -/
theorem safeApprovedhashesRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some approvedhashesTransition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  sorry

/-- Refinement obligation for `changeThreshold` (`changethresholdTransition`). -/
theorem safeChangethresholdRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some changethresholdTransition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  sorry

/-- Refinement obligation for `checkNSignatures` (`checknsignaturesTransition`). -/
theorem safeChecknsignaturesRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some checknsignaturesTransition) :
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
  sorry

/-- Refinement obligation for `checkSignatures` (`checksignaturesTransition`). -/
theorem safeChecksignaturesRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some checksignaturesTransition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  sorry

/-- Refinement obligation for `checkSignatures` (`checksignaturesAddressBytes32BytesTransition`). -/
theorem safeChecksignaturesAddressBytes32BytesRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata =
      some checksignaturesAddressBytes32BytesTransition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  sorry

/-- Refinement obligation for `disableModule` (`disablemoduleTransition`). -/
theorem safeDisablemoduleRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some disablemoduleTransition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  sorry

/-- Refinement obligation for `domainSeparator` (`domainseparatorTransition`). -/
theorem safeDomainseparatorRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some domainseparatorTransition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  sorry

/-- Refinement obligation for `enableModule` (`enablemoduleTransition`). -/
theorem safeEnablemoduleRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some enablemoduleTransition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  sorry

/-- Refinement obligation for `execTransaction` (`exectransactionTransition`). -/
theorem safeExectransactionRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some exectransactionTransition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  sorry

/-- Refinement obligation for `execTransactionFromModule`
(`exectransactionfrommoduleTransition`). -/
theorem safeExectransactionfrommoduleRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata =
      some exectransactionfrommoduleTransition) :
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
  sorry

/-- Refinement obligation for `getModulesPaginated` (`getmodulespaginatedTransition`). -/
theorem safeGetmodulespaginatedRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some getmodulespaginatedTransition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  sorry

/-- Refinement obligation for `getOwners` (`getownersTransition`). -/
theorem safeGetownersRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some getownersTransition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  sorry

/-- Refinement obligation for `getStorageAt` (`getstorageatTransition`). -/
theorem safeGetstorageatRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some getstorageatTransition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  sorry

/-- Refinement obligation for `getThreshold` (`getthresholdTransition`). -/
theorem safeGetthresholdRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some getthresholdTransition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  sorry

/-- Refinement obligation for `getTransactionHash` (`gettransactionhashTransition`). -/
theorem safeGettransactionhashRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some gettransactionhashTransition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  sorry

/-- Refinement obligation for `isModuleEnabled` (`ismoduleenabledTransition`). -/
theorem safeIsmoduleenabledRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some ismoduleenabledTransition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  sorry

/-- Refinement obligation for `isOwner` (`isownerTransition`). -/
theorem safeIsownerRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some isownerTransition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  sorry

/-- Refinement obligation for `nonce` (`nonceTransition`). -/
theorem safeNonceRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some nonceTransition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  sorry

/-- Refinement obligation for `removeOwner` (`removeownerTransition`). -/
theorem safeRemoveownerRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some removeownerTransition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  sorry

/-- Refinement obligation for `setFallbackHandler` (`setfallbackhandlerTransition`). -/
theorem safeSetfallbackhandlerRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some setfallbackhandlerTransition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  sorry

/-- Refinement obligation for `setGuard` (`setguardTransition`). -/
theorem safeSetguardRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some setguardTransition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  sorry

/-- Refinement obligation for `setModuleGuard` (`setmoduleguardTransition`). -/
theorem safeSetmoduleguardRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some setmoduleguardTransition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  sorry

/-- Refinement obligation for `setup` (`setupTransition`). -/
theorem safeSetupRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some setupTransition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  sorry

/-- Refinement obligation for `signedMessages` (`signedmessagesTransition`). -/
theorem safeSignedmessagesRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some signedmessagesTransition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  sorry

/-- Refinement obligation for `simulateAndRevert` (`simulateandrevertTransition`). -/
theorem safeSimulateandrevertRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some simulateandrevertTransition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  sorry

/-- Refinement obligation for `swapOwner` (`swapownerTransition`). -/
theorem safeSwapownerRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some swapownerTransition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  sorry

/-- Empty calldata follows receive, including its LOG2 static-mode halt. -/
theorem safeReceiveRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size = 0) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  sorry

/-- Unmatched nonempty calldata follows the raw-return fallback. -/
theorem safeFallbackRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hnonempty : I.calldata.size ≠ 0)
    (hdispatch : selectorDispatchMsg contract I.calldata = none) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  sorry

end Runtime

end Benchmarks.Safe
