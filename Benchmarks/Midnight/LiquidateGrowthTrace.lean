import Benchmarks.Midnight.LiquidateGrowth
import Benchmarks.Midnight.LiquidateEligibilityTrace
import Benchmarks.Midnight.CheckedSubGas
import Benchmarks.Midnight.CheckedMulGas
import Benchmarks.Midnight.CheckedArithmeticRevert
import Benchmarks.Midnight.RuntimeBlocks_026
import Benchmarks.Midnight.RuntimeBlocks_027

variable {fork : Ethereum.Fork}

/-! Runtime arithmetic for the post-maturity liquidation incentive. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightLiquidateGrowth {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw maximum lltv maxDebt : UInt256} {m : MarketData}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024) (hd : decodeCalldataMarket I.calldata 4 = some m)
    (rd : RD fork midnightBytecode I g s0 ⟨6547⟩ (maximum :: lltv :: maxDebt :: R)
      mem aw rdata σ k C) :
    let timestamp := UInt256.ofNat I.header.timestamp
    (¬ LiquidateGrowthSafe maximum timestamp m.maturity ∧ RDrev fork midnightBytecode g s0) ∨
    (LiquidateGrowthSafe maximum timestamp m.maturity ∧ ∃ k' C', C ≤ C' ∧
      RD fork midnightBytecode I g s0 ⟨6639⟩
        (maxDebt :: lltv :: liquidateGrownLif maximum timestamp m.maturity :: R)
        mem aw rdata σ k' C') := by
  dsimp only
  let timestamp := UInt256.ofNat I.header.timestamp
  by_cases hsub : lifScale.toNat ≤ maximum.toNat
  · have hc : UInt256.gt (maximum + UInt256.lnot (UInt256.ofNat 999999999999999999))
        maximum = ⟨0⟩ := by
      rw [wordSubLifScale]
      exact ugt_zero (by rw [usub_toNat hsub]; omega)
    have rd1 := midnightBlocks.midnight_block_6547_fallthrough
      (R := lltv :: maxDebt :: R) (by simp only [List.length_cons]; omega) hc rd
    have rd2 := midnightBlocks.midnight_block_6565
      (R := maximum :: lltv :: maxDebt :: R)
      (by simp only [List.length_cons]; omega) (by jump_dest) rd1
    simp only [midnightBlocks.midnight_block_6565_stack,
      show (UInt256.ofNat 4).toNat = 4 from rfl] at rd2
    have hm := decodeCalldataMarket_maturity hd
    simp only [calldataWord] at hm
    rw [hm] at rd2
    by_cases ht : m.maturity.toNat ≤ timestamp.toNat
    · obtain ⟨k3, C3, hc3, rd3⟩ := midnightCheckedSub_mono
        (by simp only [List.length_cons]; omega) ht (by jump_dest) rd2
      have rd4 := midnightBlocks.midnight_block_6586
        (R := lltv :: maxDebt :: R) (by simp only [List.length_cons]; omega)
        (by jump_dest) rd3
      simp only [midnightBlocks.midnight_block_6586_stack, wordSubLifScale] at rd4
      by_cases hp : (UInt256.sub maximum lifScale).toNat *
          (UInt256.sub timestamp m.maturity).toNat < UInt256.size
      · obtain ⟨k5, C5, hc5, rd5⟩ := midnightCheckedMul_mono
          (by simp only [List.length_cons]; omega) hp (by jump_dest) rd4
        have hadd := liquidateGrowth_add_fit (liquidateGrowthProduct maximum timestamp m.maturity)
        have hcadd : UInt256.gt lifScale (liquidateGrowth maximum timestamp m.maturity) = ⟨0⟩ :=
          ugt_zero (by rw [liquidateGrowth, uadd_toNat, Nat.mod_eq_of_lt hadd]; omega)
        have rd6 := midnightBlocks.midnight_block_6603_fallthrough
          (R := maximum :: lltv :: maxDebt :: R)
          (by simp only [List.length_cons]; omega) hcadd rd5
        simp only [midnightBlocks.midnight_block_6603_fallthrough_stack] at rd6
        have rd7 := midnightBlocks.midnight_block_6630 (R := R) (by omega) rd6
        simp only [midnightBlocks.midnight_block_6630_stack, wordMin_branchless_commuted] at rd7
        exact Or.inr ⟨⟨hsub, ht, hp⟩, _, _, by omega, rd7⟩
      · exact Or.inl ⟨fun h ↦ hp h.2.2, midnightCheckedMulRevert
          (by simp only [List.length_cons]; omega) (Nat.le_of_not_gt hp) rd4⟩
    · exact Or.inl ⟨fun h ↦ ht h.2.1, midnightCheckedSubRevert
        (by simp only [List.length_cons]; omega) (Nat.lt_of_not_ge ht) rd2⟩
  · have hc : UInt256.gt (maximum + UInt256.lnot (UInt256.ofNat 999999999999999999))
        maximum = ⟨1⟩ := by
      rw [wordSubLifScale]
      apply ugt_one
      rw [usub_toNat_underflow (Nat.lt_of_not_ge hsub)]
      have hl := lifScale.val.isLt
      change lifScale.toNat < UInt256.size at hl
      omega
    have rr := midnightBlocks.midnight_block_6547_taken
      (R := lltv :: maxDebt :: R) (by simp only [List.length_cons]; omega)
      (by rw [hc]; decide) (by jump_dest) rd
    exact Or.inl ⟨fun h ↦ hsub h.1, midnightBlocks.midnight_block_7276
      (by simp only [List.length_cons]; omega) rr⟩

end Benchmarks.Midnight
