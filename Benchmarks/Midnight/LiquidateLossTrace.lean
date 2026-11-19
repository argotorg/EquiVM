import Benchmarks.Midnight.Complement128Trace
import Benchmarks.Midnight.LiquidateLossArithmetic
import Benchmarks.Midnight.CheckedMulGas
import Benchmarks.Midnight.CheckedExtraGas
import Benchmarks.Midnight.CheckedUint128Gas
import Benchmarks.Midnight.CheckedArithmeticRevert
import Benchmarks.Midnight.RuntimeBlocks_030
import Benchmarks.Midnight.RuntimeBlocks_027
import Benchmarks.Midnight.RuntimeBlocks_019

/-! Checked loss-factor arithmetic, including total-unit underflow and a zero divisor. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightLiquidateLoss {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw total loss badDebt : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 12 ≤ 1024)
    (ht : total.toNat < 2 ^ 128) (hl : loss.toNat < 2 ^ 128)
    (rd : RD midnightBytecode I g s0 ⟨19421⟩
      ([loss, ⟨7523⟩, ⟨7530⟩, badDebt, ⟨6721⟩, total, ⟨7536⟩, ⟨4204⟩, ⟨7541⟩] ++ R)
      mem aw rdata σ k C) :
    (¬ (badDebt.toNat ≤ total.toNat ∧ total ≠ ⟨0⟩) ∧ RDrev midnightBytecode g s0) ∨
    (badDebt.toNat ≤ total.toNat ∧ total ≠ ⟨0⟩ ∧ ∃ k' C', C ≤ C' ∧
      RD midnightBytecode I g s0 ⟨7541⟩
        (liquidateNextLoss total loss badDebt :: R) mem aw rdata σ k' C') := by
  obtain ⟨k1, C1, hc1, rd1⟩ := midnightComplement128
    (R := ⟨7530⟩ :: badDebt :: ⟨6721⟩ :: total :: ⟨7536⟩ :: ⟨4204⟩ :: ⟨7541⟩ :: R)
    (by simp only [List.length_cons]; omega) hl (by jump_dest) rd
  have rd2 := midnightBlocks.midnight_block_7523
    (R := ⟨7536⟩ :: ⟨4204⟩ :: ⟨7541⟩ :: R)
    (by simp only [List.length_cons]; omega) (by jump_dest) rd1
  simp only [midnightBlocks.midnight_block_7523_stack] at rd2
  by_cases hle : badDebt.toNat ≤ total.toNat
  · obtain ⟨k3, C3, hc3, rd3⟩ := midnightCheckedSub_mono
      (by simp only [List.length_cons]; omega) hle (by jump_dest) rd2
    have rd4 := midnightBlocks.midnight_block_7530
      (R := ⟨6721⟩ :: total :: ⟨7536⟩ :: ⟨4204⟩ :: ⟨7541⟩ :: R)
      (by simp only [List.length_cons]; omega) (by jump_dest) rd3
    simp only [midnightBlocks.midnight_block_7530_stack] at rd4
    obtain ⟨k5, C5, hc5, rd5⟩ := midnightCheckedMul_mono
      (by simp only [List.length_cons]; omega)
      (liquidateLossProduct_lt ht hl hle) (by jump_dest) rd4
    have rd6 := midnightBlocks.midnight_block_6721
      (by simp only [List.length_cons]; omega) (by jump_dest) rd5
    by_cases hnz : total ≠ ⟨0⟩
    · obtain ⟨k7, C7, hc7, rd7⟩ := midnightCheckedDiv_mono
        (by simp only [List.length_cons]; omega) hnz (by jump_dest) rd6
      have rd8 := midnightBlocks.midnight_block_7536
        (by simp only [List.length_cons]; omega) (by jump_dest) rd7
      obtain ⟨k9, C9, hc9, rd9⟩ := midnightComplement128
        (by simp only [List.length_cons]; omega)
        (liquidateLossQuotient_lt ht hl hle) (by jump_dest) rd8
      have rd10 := midnightBlocks.midnight_block_4204
        (by simp only [List.length_cons]; omega) (by jump_dest) rd9
      obtain ⟨k11, C11, hc11, rd11⟩ := midnightToUint128_mono (R := R)
        (by omega)
        (liquidateNextLoss_lt ht hl hle) (by jump_dest) rd10
      exact Or.inr ⟨hle, hnz, _, _, by omega, rd11⟩
    · have hz : total = ⟨0⟩ := by simpa using hnz
      rw [hz] at rd6
      exact Or.inl ⟨fun h ↦ hnz h.2, midnightCheckedDivRevert
        (by simp only [List.length_cons]; omega) rd6⟩
  · exact Or.inl ⟨fun h ↦ hle h.1, midnightCheckedSubRevert
      (by simp only [List.length_cons]; omega) (by omega) rd2⟩

end Benchmarks.Midnight
