import Benchmarks.Safe.ViaIR.Common
import Benchmarks.Safe.ViaIR.Blocks.Runtime_036

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 100000

theorem safeIncrementTrace {I g s0 σ k C aw mem rdata} {value ret : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨7497⟩ (value :: ret :: R) mem aw rdata σ k C)
    (hov : R.length + 5 ≤ 1024) (hno : value.toNat + 1 < UInt256.size)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ k' C', RD fork safeBytecode I g s0 ret ((value + ⟨1⟩) :: R) mem aw rdata σ k' C' := by
  have hn : UInt256.eq value (UInt256.lnot ⟨0⟩) = ⟨0⟩ := by
    apply uInt256_eq_zero_of_ne
    intro he
    have hv := congrArg UInt256.toNat (uInt256_eq_one_eq he)
    have hm : (UInt256.lnot ⟨0⟩).toNat + 1 = UInt256.size := by decide
    omega
  have h₁ := safeRuntime_block_7497_fallthrough (by simp; omega) hn h
  have h₂ := safeRuntime_block_7506 (by omega) hret h₁
  simp only [safeRuntime_block_7506_stack] at h₂
  have he : UInt256.ofNat 1 + value = value + (⟨1⟩ : UInt256) := by
    apply u256_inj
    rw [uadd_toNat, uadd_toNat, Nat.add_comm]
    rfl
  rw [he] at h₂
  exact ⟨_, _, h₂⟩

theorem safeIncrementOverflow {I g s0 σ k C aw mem rdata} {value : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨7497⟩ (value :: R) mem aw rdata σ k C)
    (hov : R.length + 5 ≤ 1024) (hno : ¬value.toNat + 1 < UInt256.size) :
    RDrev fork safeBytecode g s0 := by
  have hn : value = UInt256.lnot ⟨0⟩ := by
    apply u256_inj
    have hv : value.toNat < UInt256.size := value.val.isLt
    have hm : (UInt256.lnot ⟨0⟩).toNat + 1 = UInt256.size := by decide
    omega
  have h₁ := safeRuntime_block_7497_taken (by omega)
    (by rw [hn, uInt256_eq_self]; decide) (by jump_dest) h
  exact safeRuntime_block_7511 (by simp; omega) h₁

end Benchmarks.Safe.ViaIR
