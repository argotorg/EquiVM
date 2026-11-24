import Benchmarks.Safe.ViaIR.IRLengthCheck
import Benchmarks.Safe.ViaIR.GetOwnersAllocation
import Benchmarks.Safe.ViaIR.GetOwnersLoop
import Benchmarks.Safe.ViaIR.GetOwnersReturn

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

variable {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
theorem safeGetownersBodyCore
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some getownersTransition) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  obtain ⟨hlong, hword⟩ := selectorDispatchFacts 0xa0 0xe6 0x7e 0x2b ⟨0xa0e67e2b⟩
    hdispatch getownersSelectorBytes (by decide)
  obtain ⟨k, C, hentry⟩ := safeReachEntry (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) ⟨0xa0e67e2b⟩ 14 ⟨4048⟩ hcode hsize hlong hword
    (by native_decide)
  let evm := initState σ σ₀ (.ofUInt256 g) A I
  have hcount : ownerCount evm = solcSlotWordAt ⟨3⟩ σ I := by
    rw [ownerCount, storageLoad_eq_solcSlotWord]
    rfl
  by_cases hvalue : I.weiValue = ⟨0⟩
  · have h4055 := safeRuntime_block_4048_fallthrough (by simp) hvalue hentry
    by_cases hsmall : I.calldata.size < 2 ^ 255 + 4
    · have h4066 := safeRuntime_block_4055_fallthrough (by simp)
        (safeIRLengthCheckOk hlong hsmall hsize) h4055
      obtain ⟨_, _, _, h₃⟩ := safeRuntime_block_4066_packed (by simp) (by jump_dest) h4066
      change RD fork safeBytecode I (.ofUInt256 g) _ ⟨8950⟩
        (solcSlotWordAt ⟨3⟩ σ I :: ⟨4076⟩ :: ⟨0⟩ :: []) solcFreePtrMem _ _ σ _ _ at h₃
      by_cases hn : (solcSlotWordAt ⟨3⟩ σ I).toNat ≤ 2 ^ 59 - 6
      · have hbound : (ownerCount evm).toNat ≤ 2 ^ 64 - 1 := by rw [hcount]; omega
        have hcount' : UInt256.ofNat (ownerCount evm).toNat = solcSlotWordAt ⟨3⟩ σ I := by
          rw [u256_ofNat_toNat, hcount]
        rw [← hcount'] at h₃
        obtain ⟨aw₄, k₄, C₄, h₄⟩ := safeGetOwnersAllocate h₃
          (by simp) (by rwa [hcount]) hsize
        have hlink : ownerLinkAt σ I ⟨1⟩ = ownerLink evm ⟨1⟩ := (ownerLink_eq_at evm ⟨1⟩).symm
        rw [hlink] at h₄
        have hmem := (safeGetOwnersAllocated (ownerCount evm).toNat).scratch ⟨1⟩ ⟨2⟩
        have hlocals := safeGetOwnersInitialLocals evm
        have hwords : ∀ w ∈ List.replicate (ownerCount evm).toNat (⟨0⟩ : UInt256),
            w.toNat < EVM.addressModulus := by
          intro w hw
          have := (List.mem_replicate.mp hw).2
          subst w
          decide
        have hloop := safeGetOwnersLoop evm (i := 0) h₄
          (by simp) hmem hlocals hbound
          (by omega) (solcAddrMask_result_canonical _) hwords
        rcases hloop with ⟨hsrc, hrev⟩ | ⟨ws, ls, ms, aw', k', C', j, hsrc, hls, hms, hws, hrd⟩
        · have hbody : ExecTransitionBody fork config contract evm ∅
              getownersTransition.body .reverted :=
            .execBlockRevert (safeGetOwnersPrefix evm hvalue (by rwa [hcount]) (.consRevert hsrc))
          refine RDrev.reEquivElim hcode hrev fun _ _ hΞ ↦ ?_
          exact reEquivSelectorExecution hdispatch (safeDecodeCalldata_empty_ok hlong hsmall) hbody
            (.revert hΞ rfl)
        · have hret := safeGetOwnersReturnTrace hrd (by simp) hms hbound hws
          have hbody : ExecTransitionBody fork config contract evm ∅ getownersTransition.body
              (.returned { contract := contract, locals := ls } evm
                (some [.array (ws.map addressArrayValue)])) :=
            .execBlockRet (safeGetOwnersPrefix evm hvalue (by rwa [hcount])
              (.consNormal hsrc (safeGetOwnersReturn evm hls)))
          refine RDret.reEquivElim hcode hret fun _ _ hΞ ↦ ?_
          exact reEquivSelectorExecution hdispatch (safeDecodeCalldata_empty_ok hlong hsmall) hbody
            (.success hΞ rfl rfl (.abi (returnEquiv_of_encode (addressArrayReturnEncoding ws hws))))
      · have hrev := safeGetOwnersCountFail h₃ (by simp) hn
        have hbody := safeGetOwnersCountRevert (fork := fork) evm hvalue (by rwa [hcount])
        refine RDrev.reEquivElim hcode hrev fun _ _ hΞ ↦ ?_
        exact reEquivSelectorExecution hdispatch (safeDecodeCalldata_empty_ok hlong hsmall)
          hbody (.revert hΞ rfl)
    · have h589 := safeRuntime_block_4055_taken (by simp)
        (by
          change UInt256.slt (UInt256.ofNat I.calldata.size + UInt256.lnot ⟨3⟩) ⟨0⟩ ≠ ⟨0⟩
          rw [safeIRLengthCheckHuge (by omega) hsize]
          decide) (by jump_dest) h4055
      exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
        (safeDecodeCalldata_empty_huge (by omega)) (safeRuntime_block_589 (by simp) h589)
  · have h589 := safeRuntime_block_4048_taken (by simp) hvalue (by jump_dest) hentry
    have hrev := safeRuntime_block_589 (by simp) h589
    exact reEquivSelectorRevert hcode hdispatch hrev fun _ ↦ bodyReverts_nonPayable hvalue

/-- Refinement obligation for `getOwners` (`getownersTransition`). -/
theorem safeGetownersRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some getownersTransition) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  exact safeGetownersBodyCore hcode hsize hdispatch

end Benchmarks.Safe.ViaIR
