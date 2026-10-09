import Benchmarks.Safe.PostModuleSource
import Benchmarks.Safe.Blocks.Runtime_033

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000

theorem safePostModuleEventTrace {I g s0 σ k C aw mem rdata}
    {hash guard ret : UInt256} {R : List UInt256} (z : Bool)
    (h : RD safeBytecode I g s0 ⟨7585⟩
      (z.toUInt256 :: hash :: guard :: ret :: R) mem aw rdata σ k C)
    (hov : R.length + 8 ≤ 1024) (hret : (D_J safeBytecode 0).contains ret = true)
    (hp : I.perm = true) :
    ∃ aw' k' C', RD safeBytecode I g s0 ret R mem aw' rdata σ k' C' := by
  cases z
  · have h₁ := safeRuntime_block_7585_taken (by simp; omega) (by decide) (by jump_dest) h
    exact safeRuntime_block_7638_packed hov hp hret h₁
  · have h₁ := safeRuntime_block_7585_fallthrough (by simp; omega) (by decide) h
    exact safeRuntime_block_7592_packed hov hp hret h₁

set_option maxRecDepth 100000 in
theorem safePostModuleEventTraceStatic {I g s0 σ k C aw mem rdata}
    {hash guard ret : UInt256} {R : List UInt256} (z : Bool)
    (h : RD safeBytecode I g s0 ⟨7585⟩
      (z.toUInt256 :: hash :: guard :: ret :: R) mem aw rdata σ k C)
    (hov : R.length + 8 ≤ 1024) (hp : I.perm = false) :
    RDstatic safeBytecode g s0 := by
  cases z
  · have h₁ := safeRuntime_block_7585_taken (by simp; omega) (by decide) (by jump_dest) h
    have h₂ := evm_run h₁ with [jumpdest, push1 ⟨64⟩, genMload, caller, swap1]
    have h₃ := RD.pushConst (width := 32) (op := .PUSH32) h₂
      ⟨78170231212922831342234521877076235888363197164780376719301842575073259279221⟩
      (by decide) (by native_decide) (by evm_ov)
    have h₄ := evm_run h₃ with [swap1, push0, swap1]
    exact RD.log2Static h₄ hp (by native_decide) (by simp; omega)
  · have h₁ := safeRuntime_block_7585_fallthrough (by simp; omega) (by decide) h
    have h₂ := evm_run h₁ with [push1 ⟨64⟩, genMload, caller, swap1]
    have h₃ := RD.pushConst (width := 32) (op := .PUSH32) h₂
      ⟨47305129968795024967062117798590983053302821274770012008259295614936177962168⟩
      (by decide) (by native_decide) (by evm_ov)
    have h₄ := evm_run h₃ with [swap1, push0, swap1]
    exact RD.log2Static h₄ hp (by native_decide) (by simp; omega)

end Benchmarks.Safe
