import Benchmarks.Midnight.LiquidateConversion
import Benchmarks.Midnight.CheckedExtraGas
import Benchmarks.Midnight.CheckedAddGas
import Benchmarks.Midnight.RuntimeBlocks_027
import Benchmarks.Midnight.TransferBudget

variable {fork : Ethereum.Fork}

/-! A specified seized amount determines the repaid amount by two rounded-up conversions. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightLiquidateSeize {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw seized maxDebt lltv lif price root : UInt256} {credit : Nat}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (hstack : R.length + 14 ≤ 1024)
    (hm : memLoad ⟨640⟩ mem = seized) (hb : TransferBudget root credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨6648⟩ (maxDebt :: lltv :: lif :: price :: R)
      mem aw rdata σ k C) :
    (¬ LiquidateSeizeSafe seized price lif ∧ RDrev fork midnightBytecode g s0) ∨
    (LiquidateSeizeSafe seized price lif ∧ ∃ aw' k' C',
      TransferBudget root credit (writeWord mem 608 (liquidateRepaidAmount seized price lif)) aw' C' ∧
      RD fork midnightBytecode I g s0 ⟨6731⟩ (maxDebt :: lltv :: lif :: price :: R)
        (writeWord mem 608 (liquidateRepaidAmount seized price lif)) aw' rdata σ k' C') := by
  have rd1 := midnightBlocks.midnight_block_6648 (R := R) (by omega) (by jump_dest) rd
  have hb1 := transferBudgetAt (root := root) (credit := credit) rd1 (by transfer_budget hb)
  rw [show UInt256.ofNat 640 = (⟨640⟩ : UInt256) from rfl] at hb1
  simp only [midnightBlocks.midnight_block_6648_stack,
    show UInt256.ofNat 640 = (⟨640⟩ : UInt256) from rfl, hm] at rd1
  change RD fork midnightBytecode I g s0 ⟨20413⟩
    (seized :: price :: ⟨6682⟩ :: ⟨6687⟩ :: liquidatePriceScale :: ⟨6693⟩ ::
      maxDebt :: lltv :: lif :: price :: R) mem _ rdata σ _ _ at rd1
  · by_cases hmprod : seized.toNat * price.toNat < UInt256.size
    · obtain ⟨k2, C2, hc2, rd2⟩ := midnightCheckedMul_mono
        (by simp only [List.length_cons]; omega) hmprod (by jump_dest) rd1
      have rd3 := midnightBlocks.midnight_block_6682
        (by simp only [List.length_cons]; omega) (by jump_dest) rd2
      rcases midnightAddPriceScalePred (by simp only [List.length_cons]; omega)
        (by jump_dest) rd3 with ⟨ha, hrev⟩ | ⟨ha, k4, C4, hc4, rd4⟩
      · exact Or.inl ⟨fun h ↦ ha h.1.2.2, hrev⟩
      · have hfirst : MulDivUpSafe seized price liquidatePriceScale := ⟨hmprod, by decide, ha⟩
        have rd5 := midnightBlocks.midnight_block_6687
          (by simp only [List.length_cons]; omega) (by jump_dest) rd4
        simp only [midnightBlocks.midnight_block_6687_stack] at rd5
        rcases midnightMulLifScale (by simp only [List.length_cons]; omega)
          (by jump_dest) rd5 with ⟨hp, hrev⟩ | ⟨hp, k6, C6, hc6, rd6⟩
        · exact Or.inl ⟨fun h ↦ hp h.2.1, hrev⟩
        · by_cases hl : 0 < lif.toNat
          · have hg : UInt256.gt (lif + UInt256.lnot ⟨0⟩) lif = ⟨0⟩ := by
              rw [u256_add_lnot_zero_eq_sub_one]
              exact ugt_zero (by rw [usub_toNat (a := lif) (b := ⟨1⟩) hl]; omega)
            have rd7 := midnightBlocks.midnight_block_6693_fallthrough
              (R := price :: R) (by simp only [List.length_cons]; omega) hg rd6
            have rd8 := midnightBlocks.midnight_block_6704
              (R := price :: R) (by simp only [List.length_cons]; omega) (by jump_dest) rd7
            simp only [midnightBlocks.midnight_block_6704_stack,
              u256_add_lnot_zero_eq_sub_one] at rd8
            by_cases hsum : (UInt256.mul (mulDivUp seized price liquidatePriceScale) lifScale).toNat +
                (UInt256.sub lif ⟨1⟩).toNat < UInt256.size
            · obtain ⟨k9, C9, hc9, rd9⟩ := midnightCheckedAdd_mono
                (by simp only [List.length_cons]; omega) hsum (by jump_dest) rd8
              have rd10 := midnightBlocks.midnight_block_6721
                (by simp only [List.length_cons]; omega) (by jump_dest) rd9
              have hnz : lif ≠ ⟨0⟩ := by intro hz; rw [hz] at hl; contradiction
              obtain ⟨k11, C11, hc11, rd11⟩ := midnightCheckedDiv_mono
                (by simp only [List.length_cons]; omega) hnz (by jump_dest) rd10
              have rd12 := midnightBlocks.midnight_block_6726
                (by simp only [List.length_cons]; omega) rd11
              simp only [midnightBlocks.midnight_block_6726_stack,
                midnightBlocks.midnight_block_6726_memory] at rd12
              have hb11 := hb1.mono (show _ ≤ C11 by omega)
              have hb12 := transferBudgetAt (root := root) (credit := credit) rd12
                (by transfer_budget hb11)
              exact Or.inr ⟨⟨hfirst, hp, hl, hsum⟩, _, _, _, hb12, rd12⟩
            · exact Or.inl ⟨fun h ↦ hsum h.2.2.2, midnightCheckedAddRevert
                (by simp only [List.length_cons]; omega) (Nat.le_of_not_gt hsum) rd8⟩
          · have hz : lif = ⟨0⟩ := uint256_toNat_eq_zero (by omega)
            have rr := midnightBlocks.midnight_block_6693_taken (R := price :: R)
              (by simp only [List.length_cons]; omega) (by rw [hz]; decide +kernel)
              (by jump_dest) rd6
            exact Or.inl ⟨fun h ↦ hl h.2.2.1, midnightBlocks.midnight_block_7276
              (by simp only [List.length_cons]; omega) rr⟩
    · exact Or.inl ⟨fun h ↦ hmprod h.1.1, midnightCheckedMulRevert
        (by simp only [List.length_cons]; omega) (Nat.le_of_not_gt hmprod) rd1⟩
end Benchmarks.Midnight
