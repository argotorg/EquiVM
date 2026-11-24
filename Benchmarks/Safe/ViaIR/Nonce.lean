import Benchmarks.Safe.ViaIR.IRLengthCheck

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

variable {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}

set_option maxRecDepth 100000 in
theorem safeNonceBodyCore
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some nonceTransition) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  obtain ⟨hlong, hword⟩ := selectorDispatchFacts 0xaf 0xfe 0xd0 0xe0 ⟨0xaffed0e0⟩
    hdispatch nonceSelectorBytes (by decide)
  obtain ⟨k, C, h4018⟩ := safeReachEntry (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) ⟨0xaffed0e0⟩ 15 ⟨4018⟩ hcode hsize hlong hword
    (by native_decide)
  by_cases hvalue : I.weiValue = ⟨0⟩
  · have h4025 := safeRuntime_block_4018_fallthrough (by simp) hvalue h4018
    by_cases hsmall : I.calldata.size < 2 ^ 255 + 4
    · have h4036 := safeRuntime_block_4025_fallthrough (by simp)
        (safeIRLengthCheckOk hlong hsmall hsize) h4025
      have hret := safeRuntime_block_4036 (by simp) h4036
      simp only [show memLoad (UInt256.ofNat 64) solcFreePtrMem = ⟨128⟩ from
          solcFreePtrMem_mload64, show (⟨128⟩ : UInt256).toNat = 128 from rfl,
        show (UInt256.ofNat 32).toNat = 32 from rfl] at hret
      change RDret fork safeBytecode _ _ σ
        ((solcReturnMem (solcSlotWordAt ⟨5⟩ σ I)).readWithPadding 128 32) at hret
      rw [solcReturnMem_read128] at hret
      refine RDret.reEquivElim hcode hret fun _ _ hsuccess ↦ ?_
      exact reEquivSelectorExecution hdispatch (safeDecodeCalldata_empty_ok hlong hsmall)
        (safeIRNonceSourceReturns hvalue)
        (.success hsuccess rfl rfl (.abi (returnEquiv_of_encode
          (by simpa [uint256] using uint256ReturnEncoding (solcSlotWordAt ⟨5⟩ σ I)))))
    · have h589 := safeRuntime_block_4025_taken (by simp)
        (by
          change UInt256.slt (UInt256.ofNat I.calldata.size + UInt256.lnot ⟨3⟩) ⟨0⟩ ≠ ⟨0⟩
          rw [safeIRLengthCheckHuge (by omega) hsize]
          decide) (by jump_dest) h4025
      exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
        (safeDecodeCalldata_empty_huge (by omega)) (safeRuntime_block_589 (by simp) h589)
  · have h589 := safeRuntime_block_4018_taken (by simp) hvalue (by jump_dest) h4018
    have hrev := safeRuntime_block_589 (by simp [safeRuntime_block_4018_taken_stack]) h589
    exact reEquivSelectorRevert hcode hdispatch hrev fun _ ↦ bodyReverts_nonPayable hvalue

/-- Refinement obligation for `nonce` (`nonceTransition`). -/
theorem safeNonceRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some nonceTransition) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  exact safeNonceBodyCore hcode hsize hdispatch

end Benchmarks.Safe.ViaIR
