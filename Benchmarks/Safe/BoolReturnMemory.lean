import Benchmarks.Safe.Routines
import Benchmarks.Safe.MemoryBytesDecoded

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000 in
theorem safeReturnBoolFromMemory {I g s0 σ k C rdata aw mem} {b : Bool} {ptr : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨759⟩ (b.toUInt256 :: R) mem aw rdata σ k C)
    (hov : R.length + 3 ≤ 1024) (hf : memLoad ⟨64⟩ mem = ptr)
    (hm : 96 ≤ mem.size) (hp : 96 ≤ ptr.toNat) :
    RDret safeBytecode g s0 σ b.toUInt256.toByteArray := by
  have hf' : memLoad (UInt256.ofNat 64) (writeWord mem ptr.toNat b.toUInt256) = ptr := by
    rw [memLoadReadWord, show (UInt256.ofNat 64).toNat = 64 by rfl,
      writeWordReadBelow _ _ _ _ _ hm hp]
    exact (memLoadReadWord mem ⟨64⟩).symm.trans hf
  have hbool : UInt256.isZero (UInt256.isZero b.toUInt256) = b.toUInt256 := by
    cases b <;> rfl
  have h₁ := safeRuntime_block_759 hov h
  change memLoad (UInt256.ofNat 64) mem = ptr at hf
  simp only [safeRuntime_block_759_stack, safeRuntime_block_759_memory, hf, hbool] at h₁
  have h₂ := safeRuntime_block_771 hov h₁
  change RDret safeBytecode g s0 σ
    ((writeWord mem ptr.toNat b.toUInt256).readWithPadding
      (memLoad (UInt256.ofNat 64) (writeWord mem ptr.toNat b.toUInt256)).toNat
      (UInt256.sub (UInt256.ofNat 32 + ptr)
        (memLoad (UInt256.ofNat 64) (writeWord mem ptr.toNat b.toUInt256))).toNat) at h₂
  rw [hf', u256_add_comm (UInt256.ofNat 32) ptr, word_add_sub_left,
    show (UInt256.ofNat 32).toNat = 32 by rfl, writeWord_sparse_read_back] at h₂
  exact h₂

end Benchmarks.Safe
