import Benchmarks.Safe.ViaIR.PostModuleSource
import Benchmarks.Safe.ViaIR.Blocks.Runtime_046

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 2000

theorem safePostModuleEventTrace {I g s0 σ k C aw mem rdata}
    {scratch₁ scratch₂ ret : UInt256} {R : List UInt256} (z : Bool)
    (h : RD fork safeBytecode I g s0 ⟨10210⟩
      (scratch₁ :: scratch₂ :: z.toUInt256 :: ⟨0⟩ :: ret :: R) mem aw rdata σ k C)
    (hov : R.length + 8 ≤ 1024) (hret : (D_J safeBytecode 0).contains ret = true)
    (hp : I.perm = true) :
    ∃ aw' k' C', RD fork safeBytecode I g s0 ret R mem aw' rdata σ k' C' := by
  cases z
  · have h₁ := safeRuntime_block_10210_taken (by simp; omega) (by decide) (by jump_dest) h
    exact safeRuntime_block_10256_packed (by omega) hp hret h₁
  · have h₁ := safeRuntime_block_10210_fallthrough (by simp; omega) (by decide) h
    exact safeRuntime_block_10218_packed (by omega) hp hret h₁

set_option maxRecDepth 2000 in
theorem safePostModuleEventTraceStatic {I g s0 σ k C aw mem rdata}
    {scratch₁ scratch₂ ret : UInt256} {R : List UInt256} (z : Bool)
    (h : RD fork safeBytecode I g s0 ⟨10210⟩
      (scratch₁ :: scratch₂ :: z.toUInt256 :: ⟨0⟩ :: ret :: R) mem aw rdata σ k C)
    (hov : R.length + 8 ≤ 1024) (hp : I.perm = false) :
    RDstatic fork safeBytecode g s0 := by
  cases z
  · have h₁ := safeRuntime_block_10210_taken (by simp; omega) (by decide) (by jump_dest) h
    simp only [safeRuntime_block_10210_taken_stack] at h₁
    have h₂ := evm_run h₁ with [jumpdest]
    have h₃ := RD.pushConst (width := 32) (op := .PUSH32) h₂
      ⟨78170231212922831342234521877076235888363197164780376719301842575073259279221⟩
      (by decide) (by native_decide) (by evm_ov)
    have h₄ := evm_run h₃ with [caller, swap2, dup1]
    exact RD.log2Static h₄ hp (by native_decide) (by simp; omega)
  · have h₁ := safeRuntime_block_10210_fallthrough (by simp; omega) (by decide) h
    simp only [safeRuntime_block_10210_fallthrough_stack] at h₁
    have h₃ := RD.pushConst (width := 32) (op := .PUSH32) h₁
      ⟨47305129968795024967062117798590983053302821274770012008259295614936177962168⟩
      (by decide) (by native_decide) (by evm_ov)
    have h₄ := evm_run h₃ with [caller, swap2, dup1]
    exact RD.log2Static h₄ hp (by native_decide) (by simp; omega)

end Benchmarks.Safe.ViaIR
