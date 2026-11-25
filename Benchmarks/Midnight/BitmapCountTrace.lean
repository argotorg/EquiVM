import Benchmarks.Midnight.BitmapCountArithmetic
import Benchmarks.Midnight.RuntimeBlocks_065
import Benchmarks.Midnight.Dispatch

variable {fork : Ethereum.Fork}

/-! The compiled bit-count computation and its sixteen-collateral guard. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def bitmapCountGuard (x : UInt256) : UInt256 :=
  UInt256.gt (UInt256.land (UInt256.shiftRight
    (UInt256.mul (UInt256.land
      (UInt256.land (bitmapCount2 (bitmapCount1 x)) uint128Mask +
        UInt256.land (UInt256.shiftRight (bitmapCount2 (bitmapCount1 x)) (UInt256.ofNat 4))
          (UInt256.ofNat 21267647932558653966460912964485513215)) countMask4)
      countMultiplier) (UInt256.ofNat 120)) (UInt256.ofNat 255)) (UInt256.ofNat 16)

theorem bitmapCountGuard_eq (x : UInt256) :
    bitmapCountGuard x = UInt256.gt (bitmapCount x) (UInt256.ofNat 16) := by
  unfold bitmapCountGuard
  rw [uint128Mask_clean (bitmapCount2_lt _), bitmapCount2_shift_mask,
    ← bitmapCount4_raw, ← bitmapCount_raw]

theorem midnightBitmapCountGuard {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw x : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 9 ≤ 1024)
    (rd : RD fork midnightBytecode I g s0 ⟨17385⟩
      ([x, countMask1, x, countMask4, countMultiplier, UInt256.ofNat 255,
        UInt256.ofNat 16] ++ R) mem aw rdata σ k C) :
    (16 < (bitmapCount x).toNat ∧ RDrev fork midnightBytecode g s0) ∨
    ((bitmapCount x).toNat ≤ 16 ∧ ∃ k' C', C ≤ C' ∧
      RD fork midnightBytecode I g s0 ⟨17462⟩ R mem aw rdata σ k' C') := by
  by_cases hcount : (bitmapCount x).toNat ≤ 16
  · have rd1 := midnightBlocks.midnight_block_17385_fallthrough (R := R) hstack
      (by change bitmapCountGuard x = UInt256.ofNat 0
          rw [bitmapCountGuard_eq]
          exact ugt_zero hcount) rd
    exact Or.inr ⟨hcount, _, _, by omega, rd1⟩
  · have hc : 16 < (bitmapCount x).toNat := by omega
    have rd1 := midnightBlocks.midnight_block_17385_taken (R := R) hstack
      (by change bitmapCountGuard x ≠ UInt256.ofNat 0
          rw [bitmapCountGuard_eq, ugt_one (a := bitmapCount x) (b := UInt256.ofNat 16) hc]
          decide) (by jump_dest) rd
    exact Or.inl ⟨hc, midnightBlocks.midnight_block_17470 (by
      simp only [midnightBlocks.midnight_block_17385_taken_stack]; omega) rd1⟩

end Benchmarks.Midnight
