import Benchmarks.Safe.ViaIR.WordExpressionSource
import Benchmarks.Safe.ViaIR.Blocks.Runtime_021
import Benchmarks.Safe.ViaIR.Blocks.Runtime_022
import Benchmarks.Safe.ViaIR.Blocks.Runtime_026
import Benchmarks.Safe.ViaIR.Blocks.Runtime_041

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 100000

-- The pinned via-IR bytecode inlines maximum in execTransaction's gas guard.
theorem safeMaximumTrace {I g s0 σ k C aw mem rdata} {a b saved : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨4612⟩ (b :: a :: saved :: R) mem aw rdata σ k C)
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨4621⟩ (saved :: maximumWord a b :: R)
      mem aw rdata σ k' C' := by
  by_cases hlt : a.toNat < b.toNat
  · have he : UInt256.lt a b = ⟨1⟩ := ult_one hlt
    have h₁ := safeRuntime_block_4612_taken (by simp; omega)
      (by rw [he]; decide) (by jump_dest) h
    have h₂ := safeRuntime_block_5446 (by simp; omega) (by jump_dest) h₁
    have hw : maximumWord a b = b := by
      rw [maximumWord, max_eq_right (le_of_lt hlt), u256_ofNat_toNat]
    exact ⟨_, _, by simpa only [safeRuntime_block_5446_stack, hw] using h₂⟩
  · have he : UInt256.lt a b = ⟨0⟩ := ult_zero (by omega)
    have h₁ := safeRuntime_block_4612_fallthrough (by simp; omega) he h
    have h₂ := safeRuntime_block_4619 (by simp; omega) h₁
    have hw : maximumWord a b = a := by
      rw [maximumWord, max_eq_left (by omega : b.toNat ≤ a.toNat), u256_ofNat_toNat]
    exact ⟨_, _, by simpa only [safeRuntime_block_4619_stack, hw] using h₂⟩

theorem safeCheckedDivTrace {I g s0 σ k C aw mem rdata} {a b ret : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨8870⟩ (a :: b :: ret :: R) mem aw rdata σ k C)
    (hb : b ≠ ⟨0⟩) (hov : R.length + 6 ≤ 1024)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ k' C', RD fork safeBytecode I g s0 ret (UInt256.div a b :: R) mem aw rdata σ k' C' := by
  have h₁ := safeRuntime_block_8870_fallthrough (by simp; omega)
    (isZero_eq_zero_of_ne hb) h
  exact ⟨_, _, safeRuntime_block_8877 (by simp; omega) hret h₁⟩

end Benchmarks.Safe.ViaIR
