import Benchmarks.Safe.ViaIR.SignatureInput
import Benchmarks.Safe.ViaIR.BytesMemory
import Benchmarks.Safe.ViaIR.SafeMulTrace
import Benchmarks.Safe.ViaIR.Blocks.Runtime_036
import Benchmarks.Safe.ViaIR.Blocks.Runtime_040

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 2000

theorem safeSignatureBoundsTrace (p : SignatureInput) (evm : EVM.State)
    {I g s0 σ k C aw mem rdata src} {executor ret : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨7531⟩
      (executor :: p.hash :: UInt256.ofNat src :: p.required :: ret :: R) mem aw rdata σ k C)
    (hm : BytesMemory mem src p.signatures) (hn : p.signatures.size < UInt256.size)
    (hov : R.length + 20 ≤ 1024) :
    (RDrev fork safeBytecode g s0 ∧
      ExecFuncBody fork config p.frame evm checkNSignaturesImplFunction.body .reverted) ∨
    ∃ aw' k' C', p.requiredBytes ≤ p.signatures.size ∧
      RD fork safeBytecode I g s0 ⟨7553⟩
        (⟨0⟩ :: UInt256.ofNat src :: p.hash :: ⟨0⟩ :: executor :: p.required :: ret :: R)
        mem aw' rdata σ k' C' := by
  have h₁ := safeRuntime_block_7531 (by simp; omega) (by jump_dest) h
  by_cases hfit : p.requiredBytes < UInt256.size
  swap
  · exact .inl ⟨safeMul65Overflow h₁ (Nat.le_of_not_gt hfit) (by simp; omega),
      safeSignatureBoundsFailed p evm (by omega)⟩
  obtain ⟨_, _, h₂⟩ := safeMul65Trace h₁ hfit (by simp; omega) (by jump_dest)
  have hlen := hm.length
  have hmnat : (UInt256.mul p.required (UInt256.ofNat 65)).toNat = p.requiredBytes := by
    rw [u256_mul_toNat]
    exact Nat.mod_eq_of_lt hfit
  by_cases hbound : p.requiredBytes ≤ p.signatures.size
  · have hcond : UInt256.gt (UInt256.mul p.required (UInt256.ofNat 65))
        (memLoad (UInt256.ofNat src) mem) = ⟨0⟩ := by
      apply ugt_zero
      rw [hlen, ulit_toNat' _ hn, hmnat]
      exact hbound
    have h₃ := safeRuntime_block_7544_fallthrough (by simp; omega) hcond h₂
    obtain ⟨aw', k', C', h₄⟩ := safeRuntime_block_7550_packed (by
      simp only [List.length_cons]; omega) h₃
    exact .inr ⟨aw', k', C', hbound, h₄⟩
  · have hcond : UInt256.gt (UInt256.mul p.required (UInt256.ofNat 65))
        (memLoad (UInt256.ofNat src) mem) = ⟨1⟩ := by
      apply ugt_one
      rw [hlen, ulit_toNat' _ hn, hmnat]
      omega
    have h₃ := safeRuntime_block_7544_taken (by simp; omega)
      (by rw [hcond]; decide) (by jump_dest) h₂
    exact .inl ⟨safeRuntime_block_8738 (by
      simp only [safeRuntime_block_7544_taken_stack, List.length_cons]; omega) h₃,
      safeSignatureBoundsFailed p evm (by omega)⟩

end Benchmarks.Safe.ViaIR
