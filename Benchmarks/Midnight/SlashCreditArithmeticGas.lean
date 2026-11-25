import Benchmarks.Midnight.CheckedMulGas
import Benchmarks.Midnight.CheckedExtraGas
import Benchmarks.Midnight.CheckedAddGas
import Benchmarks.Midnight.Uint128Arithmetic
import Benchmarks.Midnight.MulDiv
import Benchmarks.Midnight.CheckedArithmetic
import Benchmarks.Midnight.RuntimeBlocks_027
import Benchmarks.Midnight.RuntimeBlocks_085

variable {fork : Ethereum.Fork}

/-! The checked arithmetic used to slash a position's credit. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightSlashCreditArithmetic_mono {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw lastLoss word1 word0 lossDiff ret credit ptr : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 16 ≤ 1024) (hcredit : credit.toNat < 2 ^ 128)
    (hloss : lossDiff.toNat < 2 ^ 128) (hlast : lastLoss.toNat < 2 ^ 128 - 1)
    (rd : RD fork midnightBytecode I g s0 ⟨22893⟩
      ([lastLoss, word1, word0, lossDiff, ret, credit, ptr] ++ R) mem aw rdata σ k C) :
    ∃ k' C', C ≤ C' ∧ RD fork midnightBytecode I g s0 ⟨22948⟩
      ([word0, credit, word1, mulDivDown credit lossDiff (complement128 lastLoss),
        ⟨23076⟩, ret, uint128Mask, ptr] ++ R) mem aw rdata σ k' C' := by
  change RD fork midnightBytecode I g s0 ⟨22893⟩
    (lastLoss :: word1 :: word0 :: lossDiff :: ret :: credit :: ptr :: R)
    mem aw rdata σ k C at rd
  have rd1 := midnightBlocks.midnight_block_22893_fallthrough (by
    simp only [List.length_cons]; omega)
    (by rw [uint128Mask_computed]; exact complement128_guard (by omega)) rd
  simp only [midnightBlocks.midnight_block_22893_fallthrough_stack,
    uint128Mask_computed] at rd1
  have rd2 := midnightBlocks.midnight_block_22917 (by
    simp only [List.length_cons]; omega) (by jump_dest) rd1
  simp only [midnightBlocks.midnight_block_22917_stack, uint128Mask_computed,
    uint128Mask_clean hloss, show UInt256.land (UInt256.sub uint128Mask lastLoss) uint128Mask =
      UInt256.sub uint128Mask lastLoss from uint128Mask_clean (complement128_lt (by omega))] at rd2
  obtain ⟨k3, C3, hc3, rd3⟩ := midnightCheckedMul_mono (by simp only [List.length_cons]; omega)
    (uint128_product_bound hcredit hloss) (by jump_dest) rd2
  have rd4 := midnightBlocks.midnight_block_6721 (by
    simp only [List.length_cons]; omega) (by jump_dest) rd3
  have hnz : complement128 lastLoss ≠ ⟨0⟩ := by
    intro hz
    have hp := complement128_pos hlast
    rw [hz] at hp
    contradiction
  obtain ⟨k5, C5, hc5, rd5⟩ := midnightCheckedDiv_mono (by simp only [List.length_cons]; omega)
    hnz (by jump_dest) rd4
  have rd6 := midnightBlocks.midnight_block_22946 (by
    simp only [List.length_cons]; omega) rd5
  exact ⟨_, _, by omega, rd6⟩

end Benchmarks.Midnight
