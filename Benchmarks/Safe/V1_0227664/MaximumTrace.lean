import Benchmarks.Safe.V1_0227664.WordExpressionSource
import Benchmarks.Safe.V1_0227664.Blocks.Runtime_029
import Benchmarks.Safe.V1_0227664.Blocks.Runtime_032
import Benchmarks.Safe.V1_0227664.Blocks.Runtime_048

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.V1_0227664.RuntimeBlocks

namespace Benchmarks.Safe.V1_0227664

set_option maxRecDepth 100000

theorem safeMaximumTrace {I g s0 σ k C aw mem rdata} {a b ret : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨7520⟩ (b :: a :: ret :: R) mem aw rdata σ k C)
    (hov : R.length + 6 ≤ 1024) (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ k' C', RD fork safeBytecode I g s0 ret (maximumWord a b :: R) mem aw rdata σ k' C' := by
  by_cases hlt : a.toNat < b.toNat
  · have he : UInt256.lt a b = ⟨1⟩ := ult_one hlt
    have h₁ := safeRuntime_block_7520_fallthrough (by simp; omega) (by rw [he]; decide) h
    have h₂ := safeRuntime_block_7530 (by simp; omega) (by jump_dest) h₁
    have h₃ := safeRuntime_block_6705 (by simp; omega) hret h₂
    have hw : maximumWord a b = b := by
      rw [maximumWord, max_eq_right (le_of_lt hlt), u256_ofNat_toNat]
    exact ⟨_, _, by simpa only [safeRuntime_block_6705_stack, hw] using h₃⟩
  · have he : UInt256.lt a b = ⟨0⟩ := ult_zero (by omega)
    have h₁ := safeRuntime_block_7520_taken (by simp; omega) (by rw [he]; decide)
      (by jump_dest) h
    have h₂ := safeRuntime_block_7535 (by simp; omega) hret h₁
    have hw : maximumWord a b = a := by
      rw [maximumWord, max_eq_left (by omega : b.toNat ≤ a.toNat), u256_ofNat_toNat]
    exact ⟨_, _, by simpa only [safeRuntime_block_7535_stack, hw] using h₂⟩

theorem safeCheckedDivTrace {I g s0 σ k C aw mem rdata} {a b ret : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨11087⟩ (a :: b :: ret :: R) mem aw rdata σ k C)
    (hb : b ≠ ⟨0⟩) (hov : R.length + 6 ≤ 1024)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ k' C', RD fork safeBytecode I g s0 ret (UInt256.div a b :: R) mem aw rdata σ k' C' := by
  have h₁ := safeRuntime_block_11087_taken (by simp; omega) hb (by jump_dest) h
  exact ⟨_, _, safeRuntime_block_11113 (by simp; omega) hret h₁⟩

end Benchmarks.Safe.V1_0227664
