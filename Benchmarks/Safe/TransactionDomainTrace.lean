import Benchmarks.Safe.TransactionHashMemory
import Benchmarks.Safe.Blocks.Runtime_026

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

theorem safeTransactionDomainMemory {I : ExecutionEnv} {mem : ByteArray} {ptr : Nat}
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr) (hb : ptr + 96 < UInt256.size) :
    safeRuntime_block_5311_memory (ee := I) (mem := mem) = domainMemoryAt mem ptr I := by
  have hadd (j : Nat) (hj : j ≤ 96) :
      (UInt256.ofNat ptr + UInt256.ofNat j).toNat = ptr + j :=
    uadd_ofNat_toNat (by omega) (by omega) (by omega)
  change memLoad (UInt256.ofNat 64) mem = UInt256.ofNat ptr at hf
  simp only [safeRuntime_block_5311_memory, hf, hadd 32 (by decide), hadd 64 (by decide),
    ulit_toNat' ptr (by omega), domainMemoryAt, writeWords, domainTypehashWord,
    Reasoning.Theory.writeWord, Nat.add_assoc]
  rfl

theorem safeTransactionDomainStack {I : ExecutionEnv} {mem : ByteArray} {ptr : Nat}
    {R : List UInt256} (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr)
    (hb : ptr + 96 < UInt256.size) :
    safeRuntime_block_5311_stack (ee := I) (mem := mem) (R := R) =
      domainWord I :: ⟨0⟩ :: ⟨0⟩ :: R := by
  change keccakWord (memLoad (UInt256.ofNat 64) mem) (UInt256.ofNat 96)
    (safeRuntime_block_5311_memory (ee := I) (mem := mem)) :: _ = _
  rw [safeTransactionDomainMemory hf hb]
  change memLoad (UInt256.ofNat 64) mem = UInt256.ofNat ptr at hf
  rw [hf]
  simp only [keccakWord, ulit_toNat' ptr (by omega),
    show (UInt256.ofNat 96).toNat = 96 by rfl, domainMemoryAt_read,
    domainWord, uInt256OfByteArray_eq]

set_option maxRecDepth 100000 in
theorem safeTransactionDomainTrace {I g s0 σ k C aw mem rdata ptr} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨5311⟩ R mem aw rdata σ k C)
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr) (hb : ptr + 96 < UInt256.size)
    (hov : R.length + 8 ≤ 1024) :
    ∃ aw' k' C', RD safeBytecode I g s0 ⟨5377⟩ (domainWord I :: ⟨0⟩ :: ⟨0⟩ :: R)
      (domainMemoryAt mem ptr I) aw' rdata σ k' C' := by
  obtain ⟨aw', k', C', hr⟩ := safeRuntime_block_5311_packed hov (by jump_dest) h
  rw [safeTransactionDomainMemory hf hb, safeTransactionDomainStack hf hb] at hr
  exact ⟨aw', k', C', hr⟩

end Benchmarks.Safe
