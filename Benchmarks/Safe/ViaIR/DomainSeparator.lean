import Benchmarks.Safe.ViaIR.IRLengthCheck
import Benchmarks.Safe.ViaIR.Hashes
import Benchmarks.Safe.ViaIR.Routines
import Benchmarks.Safe.ViaIR.Blocks.Runtime_007

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

variable {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}

theorem safeDomainMemory (I : ExecutionEnv) :
    safeRuntime_block_995_memory (ee := I) (mem := solcFreePtrMem) = domainMemory I := by
  unfold safeRuntime_block_995_memory
  rw [show memLoad (UInt256.ofNat 64) solcFreePtrMem = ⟨128⟩ from solcFreePtrMem_mload64]
  change (UInt256.ofNat I.codeOwner.val).toByteArray.write 0
    ((UInt256.ofNat Ethereum.chainId).toByteArray.write 0
      (solcReturnMem domainTypehashWord) 160 32) 192 32 = _
  rw [writeWordAtEnd _ _ (solcReturnMem_size _),
    writeWordAtEnd _ _ (by simp [solcReturnMem_size])]
  simp only [solcReturnMem_eq, domainMemory, domainPreimage, ByteArray.append_assoc]

theorem safeDomainStack (I : ExecutionEnv) (R : List UInt256) :
    safeRuntime_block_995_stack (ee := I) (mem := solcFreePtrMem) (R := R) =
      domainWord I :: ⟨32⟩ :: R := by
  change keccakWord (memLoad (UInt256.ofNat 64) solcFreePtrMem) (UInt256.ofNat 96)
    (safeRuntime_block_995_memory (ee := I) (mem := solcFreePtrMem)) :: ⟨32⟩ :: R = _
  rw [safeDomainMemory,
    show memLoad (UInt256.ofNat 64) solcFreePtrMem = ⟨128⟩ from solcFreePtrMem_mload64]
  simp only [keccakWord, show (⟨128⟩ : UInt256).toNat = 128 from rfl,
    show (UInt256.ofNat 96).toNat = 96 from rfl, domainMemory_read,
    domainWord, uInt256OfByteArray_eq]

set_option maxRecDepth 100000 in
theorem safeDomainTrace {I g s0 σ k C} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨995⟩ R solcFreePtrMem
      (UInt256.ofNat 3) ByteArray.empty σ k C)
    (hov : R.length + 7 ≤ 1024) :
    RDret fork safeBytecode g s0 σ (domainWord I).toByteArray := by
  have h1055 := safeRuntime_block_995 hov (by jump_dest) h
  rw [safeDomainMemory, safeDomainStack] at h1055
  apply safeReturnWordFromMem h1055 (by omega)
  · exact mloadFreePtrValue (by rw [domainMemory_size]; decide) (domainMemory_read64 I)
  · exact toByteArray_write32_read_back _ _ _ (by rw [domainMemory_size]; decide)

set_option maxRecDepth 100000 in
theorem safeDomainseparatorBodyCore
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some domainseparatorTransition) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  obtain ⟨hlong, hword⟩ := selectorDispatchFacts 0xf6 0x98 0xda 0x25 ⟨0xf698da25⟩
    hdispatch domainseparatorSelectorBytes (by decide)
  obtain ⟨k, C, h977⟩ := safeReachEntry (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) ⟨0xf698da25⟩ 27 ⟨977⟩ hcode hsize hlong hword
    (by native_decide)
  by_cases hvalue : I.weiValue = ⟨0⟩
  · have h984 := safeRuntime_block_977_fallthrough (by simp) hvalue h977
    by_cases hsmall : I.calldata.size < 2 ^ 255 + 4
    · have h995 := safeRuntime_block_984_fallthrough (by simp)
        (safeIRLengthCheckOk hlong hsmall hsize) h984
      have hret := safeDomainTrace h995 (by simp)
      have hbody := nonpayableReturnExprBodyReturns (fork := fork) (cfg := config) (contract := contract)
        (imms := ∅) (locals := (∅ : Store)) (evm := initState σ σ₀ (.ofUInt256 g) A I)
        hvalue (evalDomainSeparator _ _)
      refine RDret.reEquivElim hcode hret fun _ _ hsuccess ↦ ?_
      exact reEquivSelectorExecution hdispatch (safeDecodeCalldata_empty_ok hlong hsmall) hbody
        (.success hsuccess rfl rfl (.abi (returnEquiv_of_encode (bytes32ReturnEncoding _))))
    · have h589 := safeRuntime_block_984_taken (by simp)
        (by
          change UInt256.slt (UInt256.ofNat I.calldata.size + UInt256.lnot ⟨3⟩) ⟨0⟩ ≠ ⟨0⟩
          rw [safeIRLengthCheckHuge (by omega) hsize]
          decide) (by jump_dest) h984
      exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
        (safeDecodeCalldata_empty_huge (by omega)) (safeRuntime_block_589 (by simp) h589)
  · have h589 := safeRuntime_block_977_taken (by simp) hvalue (by jump_dest) h977
    exact reEquivSelectorRevert hcode hdispatch (safeRuntime_block_589 (by simp) h589)
      fun _ ↦ bodyReverts_nonPayable hvalue

/-- Refinement obligation for `domainSeparator` (`domainseparatorTransition`). -/
theorem safeDomainseparatorRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some domainseparatorTransition) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  exact safeDomainseparatorBodyCore hcode hsize hdispatch

end Benchmarks.Safe.ViaIR
