import Benchmarks.Safe.Dispatch
import Benchmarks.Safe.GetOwnersAllocation
import Benchmarks.Safe.GetOwnersLoop
import Benchmarks.Safe.GetOwnersReturn

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

variable {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
theorem safeGetownersBodyCore
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some getownersTransition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  obtain ⟨hlong, hword⟩ := selectorDispatchFacts 0xa0 0xe6 0x7e 0x2b ⟨0xa0e67e2b⟩
    hdispatch getownersSelectorBytes (by decide)
  obtain ⟨k, C, hentry⟩ := safeReachEntry (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) ⟨0xa0e67e2b⟩ 3 ⟨1154⟩ hcode hsize hlong hword
    (by native_decide)
  let evm := initState σ σ₀ (.ofUInt256 g) A I
  have hcount : ownerCount evm = solcSlotWordAt ⟨3⟩ σ I := by
    rw [ownerCount, storageLoad_eq_solcSlotWord]
    rfl
  by_cases hvalue : I.weiValue = ⟨0⟩
  · have h₁ := safeRuntime_block_1154_taken (by simp) (by rw [hvalue]; decide)
      (by jump_dest) hentry
    have h₂ := safeRuntime_block_1165 (by simp) (by jump_dest) h₁
    by_cases hn : (solcSlotWordAt ⟨3⟩ σ I).toNat ≤ 2 ^ 64 - 1
    · obtain ⟨k₃, C₃, h₃⟩ := safeGetOwnersCountCheck h₂ (by simp [safeRuntime_block_1165_stack]) hn
      have hcount' : UInt256.ofNat (ownerCount evm).toNat = solcSlotWordAt ⟨3⟩ σ I := by
        rw [u256_ofNat_toNat, hcount]
      rw [← hcount'] at h₃
      obtain ⟨aw₄, k₄, C₄, h₄⟩ := safeGetOwnersAllocate h₃
        (by simp [safeRuntime_block_1165_stack]) (by rwa [hcount]) hsize
      have hlink : ownerLinkAt σ I ⟨1⟩ = ownerLink evm ⟨1⟩ := (ownerLink_eq_at evm ⟨1⟩).symm
      rw [hlink] at h₄
      have hmem := (safeAddressArrayAllocated solcFreePtrMem (ownerCount evm).toNat
        solcFreePtrMem_size).scratch ⟨1⟩ ⟨2⟩
      have hlocals := safeGetOwnersInitialLocals evm
      have hwords : ∀ w ∈ List.replicate (ownerCount evm).toNat (⟨0⟩ : UInt256),
          w.toNat < EVM.addressModulus := by
        intro w hw
        have := (List.mem_replicate.mp hw).2
        subst w
        decide
      have hloop := safeGetOwnersLoop evm (i := 0) h₄
        (by simp [safeRuntime_block_1165_stack]) hmem hlocals (by rwa [hcount])
        (by omega) (solcAddrMask_result_canonical _) hwords (by jump_dest)
      rcases hloop with ⟨hsrc, hrev⟩ | ⟨ws, ls, ms, aw', k', C', j, hsrc, hls, hms, hws, hrd⟩
      · have hbody : ExecTransitionBody config contract evm ∅ getownersTransition.body .reverted :=
          .execBlockRevert (safeGetOwnersPrefix evm hvalue (by rwa [hcount]) (.consRevert hsrc))
        refine RDrev.reEquivElim hcode hrev fun _ _ hΞ ↦ ?_
        exact reEquivSelectorExecution hdispatch (decodeCalldata_empty_ok hlong) hbody
          (.revert hΞ rfl)
      · have hret := safeGetOwnersReturnTrace hrd (by simp) hms (by rwa [hcount]) hws
        have hbody : ExecTransitionBody config contract evm ∅ getownersTransition.body
            (.returned { contract := contract, locals := ls } evm
              (some [.array (ws.map addressArrayValue)])) :=
          .execBlockRet (safeGetOwnersPrefix evm hvalue (by rwa [hcount])
            (.consNormal hsrc (safeGetOwnersReturn evm hls)))
        refine RDret.reEquivElim hcode hret fun _ _ hΞ ↦ ?_
        exact reEquivSelectorExecution hdispatch (decodeCalldata_empty_ok hlong) hbody
          (.success hΞ rfl rfl (.abi (returnEquiv_of_encode (addressArrayReturnEncoding ws hws))))
    · have hrev := safeGetOwnersCountFail h₂ (by simp [safeRuntime_block_1165_stack]) hn
      have hbody := safeGetOwnersCountRevert evm hvalue (by rwa [hcount])
      refine RDrev.reEquivElim hcode hrev fun _ _ hΞ ↦ ?_
      exact reEquivSelectorExecution hdispatch (decodeCalldata_empty_ok hlong) hbody
        (.revert hΞ rfl)
  · have h₁ := safeRuntime_block_1154_fallthrough (by simp)
      (isZero_eq_zero_of_ne hvalue) hentry
    have hrev := safeRuntime_block_1162 (by simp [safeRuntime_block_1154_fallthrough_stack]) h₁
    exact reEquivSelectorRevert hcode hdispatch hrev fun _ ↦ bodyReverts_nonPayable hvalue

/-- Refinement obligation for `getOwners` (`getownersTransition`). -/
theorem safeGetownersRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some getownersTransition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  exact safeGetownersBodyCore hcode hsize hdispatch

end Benchmarks.Safe
