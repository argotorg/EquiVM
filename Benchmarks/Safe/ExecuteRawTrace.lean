import Benchmarks.Safe.ExecuteCallSource
import Benchmarks.Safe.RawDelegateCall
import Benchmarks.Safe.RawValueCall
import Benchmarks.Safe.Blocks.Runtime_032
import Reasoning.WordArithmetic

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000 in
theorem safeExecuteRawTrace {I g s0 σ k C aw mem rdata}
    {target value ptr operation txGas ret : UInt256} {R : List UInt256}
    (evm : EVM.State) (payload : ByteArray)
    (h : RD safeBytecode I g s0 ⟨7408⟩
      (txGas :: operation :: ptr :: value :: target :: ret :: R) mem aw rdata σ k C)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ) (hworld : evm.σ₀ = s0.σ₀)
    (hdata : mem.readWithPadding (ptr + UInt256.ofNat 32).toNat (memLoad ptr mem).toNat =
      payload)
    (hop : operation.toNat ≤ 1) (hov : R.length + 14 ≤ 1024)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    (RDstatic safeBytecode g s0 ∧ operation ≠ ⟨1⟩ ∧
      evm.executionEnv.perm = false ∧ value ≠ ⟨0⟩) ∨
    ∃ evm' σ' z out aw' k' C',
      executeViaEVM evm (AccountAddress.ofUInt256 target) value payload operation z evm' out ∧
      evm'.executionEnv = I ∧ evm'.accountMap = σ' ∧ evm'.σ₀ = s0.σ₀ ∧
      RD safeBytecode I g s0 ret ((if z then ⟨1⟩ else ⟨0⟩) :: R)
        mem aw' out σ' k' C' ∧ out.size < UInt256.size ∧
      (payload.size ≤ maxReturnDataSizeByGas → out.size < 2 ^ 138) := by
  have h₁ := safeRuntime_block_7408_taken (by simp; omega) (by
    rw [ugt_zero hop]
    decide) (by jump_dest) h
  by_cases hd : operation = ⟨1⟩
  · have h₂ := safeRuntime_block_7429_fallthrough (by simp; omega)
      (by rw [hd]; decide) h₁
    have h₃ := safeRuntime_block_7435 (by simp; omega) h₂
    obtain ⟨evm', σ', z, out, aw', k', C', hc, he, ha, hw, h₄, hs, hb⟩ :=
      rawDelegateCallTraceFromBounded evm h₃ hee hacc hworld (by native_decide) (by simp; omega)
    rw [callOutputMem_zero] at h₄
    have h₅ := safeRuntime_block_7446 (by simp; omega) (by jump_dest) h₄
    have h₆ := safeRuntime_block_7467 (by simp; omega) hret h₅
    exact Or.inr ⟨evm', σ', z, out, aw', _, _,
      Or.inl ⟨hd, by simpa only [addressOfAddress, hdata] using hc⟩,
      he, ha, hw, h₆, hs, by simpa only [hdata] using hb⟩
  · have h₂ := safeRuntime_block_7429_taken (by simp; omega)
      (u256_sub_ne_zero_of_ne hd) (by jump_dest) h₁
    have h₃ := safeRuntime_block_7452 (by simp; omega) h₂
    by_cases hp : I.perm = true ∨ value = ⟨0⟩
    · obtain ⟨evm', σ', z, out, aw', k', C', hc, he, ha, hw, h₄, hs, hb⟩ :=
        rawValueCallTraceFrom evm h₃ hee hacc hworld (by native_decide) (by simp; omega) hp
      rw [callOutputMem_zero] at h₄
      have h₅ := safeRuntime_block_7465 (by simp; omega) h₄
      have h₆ := safeRuntime_block_7467 (by simp; omega) hret h₅
      exact Or.inr ⟨evm', σ', z, out, aw', _, _,
        Or.inr ⟨hd, by simpa only [addressOfAddress, hdata] using hc⟩,
        he, ha, hw, h₆, hs, by simpa only [hdata] using hb⟩
    · have hperm : I.perm = false := Bool.eq_false_iff.mpr (fun htrue ↦ hp (Or.inl htrue))
      have hv : value ≠ ⟨0⟩ := fun hz ↦ hp (Or.inr hz)
      exact Or.inl ⟨RD.callValueStatic h₃ hperm hv (by native_decide) (by simp; omega),
        hd, by simpa only [hee] using hperm, hv⟩

end Benchmarks.Safe
