import Benchmarks.Safe.ViaIR.TransactionHashMemory
import Benchmarks.Safe.ViaIR.Blocks.Runtime_042

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

theorem safeTransactionDomainMemory {I : ExecutionEnv} {mem : ByteArray} {ptr : Nat}
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr) (hb : ptr + 96 < UInt256.size) :
    safeRuntime_block_9040_memory (ee := I) (mem := mem) = domainMemoryAt mem ptr I := by
  have hadd (j : Nat) (hj : j ≤ 96) :
      (UInt256.ofNat ptr + UInt256.ofNat j).toNat = ptr + j :=
    uadd_ofNat_toNat (by omega) (by omega) (by omega)
  change memLoad (UInt256.ofNat 64) mem = UInt256.ofNat ptr at hf
  simp only [safeRuntime_block_9040_memory, hf, hadd 32 (by decide), hadd 64 (by decide),
    ulit_toNat' ptr (by omega), domainMemoryAt, writeWords, domainTypehashWord,
    Reasoning.Theory.writeWord, Nat.add_assoc]
  rfl

theorem safeTransactionDomainStack {I : ExecutionEnv} {mem : ByteArray} {ptr : Nat}
    {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : UInt256}
    {R : List UInt256} (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr)
    (hb : ptr + 96 < UInt256.size) :
    safeRuntime_block_9040_stack (ee := I) (mem := mem) (x0 := x0) (x1 := x1)
      (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7)
      (x8 := x8) (x9 := x9) (x10 := x10) (R := R) =
      domainWord I :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x1 :: x0 :: x3 :: x2 ::
        ⟨30⟩ :: ⟨66⟩ :: R := by
  change keccakWord (memLoad (UInt256.ofNat 64) mem) (UInt256.ofNat 96)
    (safeRuntime_block_9040_memory (ee := I) (mem := mem)) :: _ = _
  rw [safeTransactionDomainMemory hf hb]
  change memLoad (UInt256.ofNat 64) mem = UInt256.ofNat ptr at hf
  rw [hf]
  simp only [keccakWord, ulit_toNat' ptr (by omega),
    show (UInt256.ofNat 96).toNat = 96 by rfl, domainMemoryAt_read,
    domainWord, uInt256OfByteArray_eq]
  rfl

set_option maxRecDepth 2000 in
theorem safeTransactionDomainTrace {I g s0 σ k C aw mem rdata ptr} {R : List UInt256}
    {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : UInt256}
    (h : RD fork safeBytecode I g s0 ⟨9040⟩
      (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: R)
      mem aw rdata σ k C)
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr) (hb : ptr + 96 < UInt256.size)
    (hov : R.length + 19 ≤ 1024) :
    ∃ aw' k' C', RD fork safeBytecode I g s0 ⟨9114⟩
      (domainWord I :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x1 :: x0 :: x3 :: x2 ::
        ⟨30⟩ :: ⟨66⟩ :: R)
      (domainMemoryAt mem ptr I) aw' rdata σ k' C' := by
  obtain ⟨aw', k', C', hr⟩ := safeRuntime_block_9040_packed hov (by jump_dest) h
  rw [safeTransactionDomainMemory hf hb, safeTransactionDomainStack hf hb] at hr
  exact ⟨aw', k', C', hr⟩

end Benchmarks.Safe.ViaIR
