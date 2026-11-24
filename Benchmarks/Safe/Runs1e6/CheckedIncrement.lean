import Benchmarks.Safe.Runs1e6.Common
import Benchmarks.Safe.Runs1e6.Blocks.Runtime_049

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.Runs1e6.RuntimeBlocks

namespace Benchmarks.Safe.Runs1e6

set_option maxRecDepth 100000

private theorem safeIncrementSub (w : UInt256) :
    UInt256.sub w
      (UInt256.ofNat
        115792089237316195423570985008687907853269984665640564039457584007913129639935) =
      w + (⟨1⟩ : UInt256) := by
  apply u256_inj
  change (1 + w.toNat) % UInt256.size = (w.toNat + 1) % UInt256.size
  rw [Nat.add_comm]

theorem safeIncrementTrace {I g s0 σ k C aw mem rdata} {value ret : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨13831⟩ (value :: ret :: R) mem aw rdata σ k C)
    (hov : R.length + 5 ≤ 1024) (hno : value.toNat + 1 < UInt256.size)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ k' C', RD fork safeBytecode I g s0 ret ((value + ⟨1⟩) :: R) mem aw rdata σ k' C' := by
  have hn : value + UInt256.ofNat 1 ≠ ⟨0⟩ := by
    intro hz
    have hv := congrArg UInt256.toNat hz
    rw [uadd_word_ofNat_toNat value 1 hno] at hv
    change value.toNat + 1 = 0 at hv
    omega
  have h₁ := safeRuntime_block_13831_taken (by simp; omega)
    (by simpa only [safeIncrementSub] using hn) (by jump_dest) h
  have h₂ := safeRuntime_block_13879 (by omega) hret h₁
  simp only [safeRuntime_block_13879_stack, safeIncrementSub] at h₂
  have he : UInt256.ofNat 1 + value = value + (⟨1⟩ : UInt256) := by
    apply u256_inj
    rw [uadd_toNat, uadd_toNat, Nat.add_comm]
    rfl
  rw [he] at h₂
  exact ⟨_, _, h₂⟩

theorem safeIncrementOverflow {I g s0 σ k C aw mem rdata} {value : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨13831⟩ (value :: R) mem aw rdata σ k C)
    (hov : R.length + 5 ≤ 1024) (hno : ¬value.toNat + 1 < UInt256.size) :
    RDrev fork safeBytecode g s0 := by
  have hn : value + UInt256.ofNat 1 = ⟨0⟩ := by
    apply u256_inj
    change (value.toNat + 1) % UInt256.size = 0
    have hv : value.toNat < UInt256.size := value.val.isLt
    have he : value.toNat + 1 = UInt256.size := by omega
    rw [he, Nat.mod_self]
  have h₁ := safeRuntime_block_13831_fallthrough (by omega)
    (by simpa only [safeIncrementSub] using hn) h
  have h₂ := safeRuntime_block_13872
    (by simp only [safeRuntime_block_13831_fallthrough_stack, List.length_cons]; omega)
    (by jump_dest) h₁
  exact safeRuntime_block_13786
    (by simp only [safeRuntime_block_13872_stack, safeRuntime_block_13831_fallthrough_stack,
      List.length_cons]; omega) h₂

end Benchmarks.Safe.Runs1e6
