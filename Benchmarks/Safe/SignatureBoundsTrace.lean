import Benchmarks.Safe.SignatureInput
import Benchmarks.Safe.BytesMemory
import Benchmarks.Safe.SafeMulTrace
import Benchmarks.Safe.Blocks.Runtime_014

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000

theorem safeSignatureBoundsTrace (p : SignatureInput) (evm : EVM.State)
    {I g s0 σ k C aw mem rdata src} {executor ret : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨1959⟩
      (p.required :: UInt256.ofNat src :: p.hash :: executor :: ret :: R) mem aw rdata σ k C)
    (hm : BytesMemory mem src p.signatures) (hn : p.signatures.size < UInt256.size)
    (hov : R.length + 20 ≤ 1024) :
    (RDrev safeBytecode g s0 ∧
      ExecFuncBody config p.frame evm checkNSignaturesImplFunction.body .reverted) ∨
    ∃ aw' k' C', p.requiredBytes ≤ p.signatures.size ∧
      RD safeBytecode I g s0 ⟨2002⟩
        (⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: p.required :: UInt256.ofNat src ::
          p.hash :: executor :: ret :: R) mem aw' rdata σ k' C' := by
  have h₁ := safeRuntime_block_1959 (by simp; omega) (by jump_dest) h
  by_cases hfit : p.requiredBytes < UInt256.size
  swap
  · exact .inl ⟨safeMulOverflow h₁ (Nat.le_of_not_gt hfit) (by simp; omega),
      safeSignatureBoundsFailed p evm (by omega)⟩
  obtain ⟨_, _, h₂⟩ := safeMulTrace h₁ hfit (by simp; omega) (by jump_dest)
  have hlen := hm.length
  have hmnat : (UInt256.mul p.required (UInt256.ofNat 65)).toNat = p.requiredBytes := by
    rw [u256_mul_toNat]
    exact Nat.mod_eq_of_lt hfit
  by_cases hbound : p.requiredBytes ≤ p.signatures.size
  · have hcond : UInt256.lt (memLoad (UInt256.ofNat src) mem)
        (UInt256.mul p.required (UInt256.ofNat 65)) = ⟨0⟩ := by
      apply ult_zero
      rw [hlen, ulit_toNat' _ hn, hmnat]
      exact hbound
    have h₃ := safeRuntime_block_1970_taken (by simp; omega)
      (by rw [hcond]; decide) (by jump_dest) h₂
    obtain ⟨aw', k', C', h₄⟩ := safeRuntime_block_1995_packed (by
      simp only [safeRuntime_block_1970_taken_stack, List.length_cons]; omega) h₃
    exact .inr ⟨aw', k', C', hbound, h₄⟩
  · have hcond : UInt256.lt (memLoad (UInt256.ofNat src) mem)
        (UInt256.mul p.required (UInt256.ofNat 65)) = ⟨1⟩ := by
      apply ult_one
      rw [hlen, ulit_toNat' _ hn, hmnat]
      omega
    have h₃ := safeRuntime_block_1970_fallthrough (by simp; omega)
      (by rw [hcond]; decide) h₂
    have h₄ := safeRuntime_block_1979 (by
      simp only [safeRuntime_block_1970_fallthrough_stack, List.length_cons]; omega)
      (by jump_dest) h₃
    exact .inl ⟨safeRuntime_block_6898 (by
      simp only [safeRuntime_block_1979_stack, safeRuntime_block_1970_fallthrough_stack,
        List.length_cons]; omega) h₄, safeSignatureBoundsFailed p evm (by omega)⟩

end Benchmarks.Safe
