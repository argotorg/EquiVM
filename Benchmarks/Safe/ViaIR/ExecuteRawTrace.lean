import Benchmarks.Safe.ViaIR.ExecuteCallSource
import Benchmarks.Safe.ViaIR.RawDelegateCall
import Benchmarks.Safe.ViaIR.RawValueCall
import Benchmarks.Safe.ViaIR.Blocks.Runtime_045
import Benchmarks.Safe.ViaIR.Blocks.Runtime_046
import Reasoning.WordArithmetic

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 2000 in
theorem safeExecuteRawTrace {I g s0 σ k C aw mem rdata}
    {target value ptr operation ret : UInt256} {R : List UInt256}
    (evm : EVM.State) (payload : ByteArray)
    (h : RD fork safeBytecode I g s0 ⟨10140⟩
      (target :: value :: ptr :: operation :: ret :: R) mem aw rdata σ k C)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ) (hworld : evm.σ₀ = s0.σ₀)
    (hdata : mem.readWithPadding (ptr + UInt256.ofNat 32).toNat (memLoad ptr mem).toNat =
      payload)
    (hop : operation.toNat ≤ 1) (hov : R.length + 14 ≤ 1024)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    (RDstatic fork safeBytecode g s0 ∧ operation ≠ ⟨1⟩ ∧
      evm.executionEnv.perm = false ∧ value ≠ ⟨0⟩) ∨
    ∃ evm' σ' z out aw' k' C',
      executeViaEVM fork evm (AccountAddress.ofUInt256 target) value payload operation z evm' out ∧
      (operation = ⟨1⟩ ∨ value = ⟨0⟩ ∨ evm.executionEnv.perm = true) ∧
      evm'.executionEnv = I ∧ evm'.accountMap = σ' ∧ evm'.σ₀ = s0.σ₀ ∧
      RD fork safeBytecode I g s0 ret ((if z then ⟨1⟩ else ⟨0⟩) :: R)
        mem aw' out σ' k' C' ∧ out.size < UInt256.size ∧
      (payload.size ≤ maxReturnDataSizeByGas → out.size < 2 ^ 138) := by
  have h₁ := safeRuntime_block_10140_fallthrough (by simp; omega) (by
    rw [ult_one (by change operation.toNat < 2; omega)]; decide) h
  by_cases hd : operation = ⟨1⟩
  · have h₂ := safeRuntime_block_10154_fallthrough (by simp; omega)
      (by rw [hd]; decide) h₁
    have h₃ := safeRuntime_block_10165 (by simp; omega) h₂
    obtain ⟨evm', σ', z, out, aw', k', C', hc, he, ha, hw, h₄, hs, hb⟩ :=
      rawDelegateCallTraceFromBounded evm h₃ hee hacc hworld (by native_decide) (by simp; omega)
    rw [callOutputMem_zero] at h₄
    have h₆ := safeRuntime_block_10176 (by simp; omega) hret h₄
    exact Or.inr ⟨evm', σ', z, out, aw', _, _,
      Or.inl ⟨hd, by simpa only [addressOfAddress, hdata] using hc⟩,
      Or.inl hd,
      he, ha, hw, h₆, hs, by simpa only [hdata] using hb⟩
  · have h₂ := safeRuntime_block_10154_taken (by simp; omega)
      (u256_sub_ne_zero_of_ne (fun hh ↦ hd hh.symm)) (by jump_dest) h₁
    have h₃ := safeRuntime_block_10178 (by simp; omega) h₂
    by_cases hp : I.perm = true ∨ value = ⟨0⟩
    · obtain ⟨evm', σ', z, out, aw', k', C', hc, he, ha, hw, h₄, hs, hb⟩ :=
        rawValueCallTraceFrom evm h₃ hee hacc hworld (by native_decide) (by simp; omega) hp
      rw [callOutputMem_zero] at h₄
      have h₆ := safeRuntime_block_10189 (by simp; omega) hret h₄
      exact Or.inr ⟨evm', σ', z, out, aw', _, _,
        Or.inr ⟨hd, by simpa only [addressOfAddress, hdata] using hc⟩,
        Or.inr (by simpa only [hee, or_comm] using hp),
        he, ha, hw, h₆, hs, by simpa only [hdata] using hb⟩
    · have hperm : I.perm = false := Bool.eq_false_iff.mpr (fun htrue ↦ hp (Or.inl htrue))
      have hv : value ≠ ⟨0⟩ := fun hz ↦ hp (Or.inr hz)
      exact Or.inl ⟨RD.callValueStatic h₃ hperm hv (by native_decide) (by simp; omega),
        hd, by simpa only [hee] using hperm, hv⟩

end Benchmarks.Safe.ViaIR
