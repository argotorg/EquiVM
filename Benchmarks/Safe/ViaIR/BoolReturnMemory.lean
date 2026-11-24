import Benchmarks.Safe.ViaIR.Blocks.Runtime_023
import Benchmarks.Safe.ViaIR.MemoryBytesDecoded

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 2000 in
theorem safeReturnBoolFromMemory {I g s0 σ k C rdata aw mem} {b : Bool}
    {scratch₀ scratch₁ scratch₂ : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨4819⟩
      (scratch₀ :: scratch₁ :: scratch₂ :: UInt256.isZero b.toUInt256 :: R)
      mem aw rdata σ k C) (hov : R.length + 8 ≤ 1024) :
    RDret fork safeBytecode g s0 σ b.toUInt256.toByteArray := by
  have hbool : UInt256.isZero (UInt256.isZero b.toUInt256) = b.toUInt256 := by
    cases b <;> rfl
  have hr := safeRuntime_block_4819 hov h
  rw [hbool] at hr
  change RDret fork safeBytecode g s0 σ
    ((writeWord mem (memLoad ⟨64⟩ mem).toNat b.toUInt256).readWithPadding
      (memLoad ⟨64⟩ mem).toNat 32) at hr
  simpa only [writeWord_sparse_read_back] using hr

end Benchmarks.Safe.ViaIR
