import Benchmarks.Safe.Dispatch
import Benchmarks.Safe.Hashes
import Benchmarks.Safe.Routines
import Benchmarks.Safe.Blocks.Runtime_012
import Benchmarks.Safe.Blocks.Runtime_013

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

variable {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}

theorem safeDomainMemory (I : ExecutionEnv) :
    safeRuntime_block_1563_memory (ee := I) (mem := solcFreePtrMem) = domainMemory I := by
  unfold safeRuntime_block_1563_memory
  rw [show memLoad (UInt256.ofNat 64) solcFreePtrMem = ⟨128⟩ from solcFreePtrMem_mload64]
  change (UInt256.ofNat I.codeOwner.val).toByteArray.write 0
    ((UInt256.ofNat Ethereum.chainId).toByteArray.write 0
      (solcReturnMem domainTypehashWord) 160 32) 192 32 = _
  rw [writeWordAtEnd _ _ (solcReturnMem_size _),
    writeWordAtEnd _ _ (by simp [solcReturnMem_size])]
  simp only [solcReturnMem_eq, domainMemory, domainPreimage, ByteArray.append_assoc]

theorem safeDomainStack (I : ExecutionEnv) (R : List UInt256) :
    safeRuntime_block_1563_stack (ee := I) (mem := solcFreePtrMem) (R := R) =
      domainWord I :: R := by
  change keccakWord (memLoad (UInt256.ofNat 64) solcFreePtrMem) (UInt256.ofNat 96)
    (safeRuntime_block_1563_memory (ee := I) (mem := solcFreePtrMem)) :: R = _
  rw [safeDomainMemory,
    show memLoad (UInt256.ofNat 64) solcFreePtrMem = ⟨128⟩ from solcFreePtrMem_mload64]
  simp only [keccakWord, show (⟨128⟩ : UInt256).toNat = 128 from rfl,
    show (UInt256.ofNat 96).toNat = 96 from rfl, domainMemory_read,
    domainWord, uInt256OfByteArray_eq]

set_option maxRecDepth 100000 in
theorem safeDomainTrace {I g s0 σ k C} {R : List UInt256} {cv : UInt256}
    (h : RD safeBytecode I g s0 ⟨1563⟩ (cv :: R) solcFreePtrMem
      (UInt256.ofNat 3) ByteArray.empty σ k C)
    (hov : R.length + 5 ≤ 1024) :
    RDret safeBytecode g s0 σ (domainWord I).toByteArray := by
  have h974 := safeRuntime_block_1563 hov (by jump_dest) h
  rw [safeDomainMemory, safeDomainStack] at h974
  apply safeReturnWordFromMem h974 (by omega)
  · exact mloadFreePtrValue (by rw [domainMemory_size]; decide) (domainMemory_read64 I)
  · apply mloadFreePtrValue
    · exact writeWord_size_gt64_of_mem (by rw [domainMemory_size]; decide)
        (by rw [domainMemory_size]; decide)
    · exact wordReturnWrite_preserves_read64 (freePtr := ⟨128⟩) (len := domainWord I)
        (by decide) (by rw [domainMemory_size]; decide) (domainMemory_read64 I)
  · exact toByteArray_write32_read_back _ _ _ (by rw [domainMemory_size]; decide)

set_option maxRecDepth 100000 in
theorem safeDomainseparatorBodyCore
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some domainseparatorTransition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  obtain ⟨hlong, hword⟩ := selectorDispatchFacts 0xf6 0x98 0xda 0x25 ⟨0xf698da25⟩
    hdispatch domainseparatorSelectorBytes (by decide)
  obtain ⟨k, C, h1552⟩ := safeReachEntry (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) ⟨0xf698da25⟩ 0 ⟨1552⟩ hcode hsize hlong hword
    (by native_decide)
  by_cases hvalue : I.weiValue = ⟨0⟩
  · have h1563 := safeRuntime_block_1552_taken (by simp)
      (by rw [hvalue]; decide) (by jump_dest) h1552
    have hret := safeDomainTrace h1563 (by simp)
    have hbody := nonpayableReturnExprBodyReturns (cfg := config) (contract := contract)
      (imms := ∅) (locals := (∅ : Store)) (evm := initState σ σ₀ (.ofUInt256 g) A I)
      hvalue (evalDomainSeparator _ _)
    refine RDret.reEquivElim hcode hret fun _ _ hsuccess ↦ ?_
    exact reEquivSelectorExecution hdispatch (decodeCalldata_empty_ok hlong) hbody
      (.success hsuccess rfl rfl (.abi (returnEquiv_of_encode (bytes32ReturnEncoding _))))
  · have h1560 := safeRuntime_block_1552_fallthrough (by simp)
      (isZero_eq_zero_of_ne hvalue) h1552
    have hrev := safeRuntime_block_1560 (by simp [safeRuntime_block_1552_fallthrough_stack])
      h1560
    exact reEquivSelectorRevert hcode hdispatch hrev fun _ ↦ bodyReverts_nonPayable hvalue

/-- Refinement obligation for `domainSeparator` (`domainseparatorTransition`). -/
theorem safeDomainseparatorRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some domainseparatorTransition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  exact safeDomainseparatorBodyCore hcode hsize hdispatch

end Benchmarks.Safe
