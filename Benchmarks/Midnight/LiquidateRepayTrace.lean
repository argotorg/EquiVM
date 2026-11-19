import Benchmarks.Midnight.LiquidateConversion
import Benchmarks.Midnight.CheckedExtraGas
import Benchmarks.Midnight.RuntimeBlocks_029
import Benchmarks.Midnight.TransferBudget

/-! A specified repayment determines the seized amount by two rounded-down conversions. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightLiquidateRepay {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw repaid maxDebt lltv lif price root : UInt256} {credit : Nat}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (hstack : R.length + 12 ≤ 1024)
    (hr : calldataWord I.calldata 100 = repaid) (hb : TransferBudget root credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨7339⟩ (maxDebt :: lltv :: lif :: price :: R)
      mem aw rdata σ k C) :
    (¬ LiquidateRepaySafe repaid price lif ∧ RDrev midnightBytecode g s0) ∨
    (LiquidateRepaySafe repaid price lif ∧ ∃ aw' k' C',
      TransferBudget root credit (writeWord mem 640 (liquidateSeizedAmount repaid price lif)) aw' C' ∧
      RD midnightBytecode I g s0 ⟨6731⟩ (maxDebt :: lltv :: lif :: price :: R)
        (writeWord mem 640 (liquidateSeizedAmount repaid price lif)) aw' rdata σ k' C') := by
  have rd1 := midnightBlocks.midnight_block_7339
    (R := price :: R) (by simp only [List.length_cons]; omega) (by jump_dest) rd
  have hr' : uInt256OfByteArray (I.calldata.readBytes 100 32) = repaid := hr
  simp only [midnightBlocks.midnight_block_7339_stack,
    show (UInt256.ofNat 100).toNat = 100 from rfl, hr'] at rd1
  by_cases hm : repaid.toNat * lif.toNat < UInt256.size
  · obtain ⟨k2, C2, hc2, rd2⟩ := midnightCheckedMul_mono
      (by simp only [List.length_cons]; omega) hm (by jump_dest) rd1
    by_cases hv : (mulDivDown repaid lif lifScale).toNat * liquidatePriceScale.toNat < UInt256.size
    · have rd3 := midnightBlocks.midnight_block_7360_fallthrough
        (R := maxDebt :: lltv :: lif :: price :: R)
        (by simp only [List.length_cons]; omega) (checkedMulGuard hv) rd2
      simp only [midnightBlocks.midnight_block_7360_fallthrough_stack] at rd3
      have rd4 := midnightBlocks.midnight_block_7396 (R := R) (by omega) (by jump_dest) rd3
      simp only [midnightBlocks.midnight_block_7396_stack] at rd4
      by_cases hp : price ≠ ⟨0⟩
      · obtain ⟨k5, C5, hc5, rd5⟩ := midnightCheckedDiv_mono
          (by simp only [List.length_cons]; omega) hp (by jump_dest) rd4
        have rd6 := midnightBlocks.midnight_block_7405
          (by simp only [List.length_cons]; omega) (by jump_dest) rd5
        simp only [midnightBlocks.midnight_block_7405_stack,
          midnightBlocks.midnight_block_7405_memory] at rd6
        have hb5 := hb.mono (show C ≤ C5 by omega)
        have hb6 := transferBudgetAt (root := root) (credit := credit) rd6 (by transfer_budget hb5)
        exact Or.inr ⟨⟨hm, hv, hp⟩, _, _, _, hb6, rd6⟩
      · have hz : price = ⟨0⟩ := not_not.mp hp
        rw [hz] at rd4
        exact Or.inl ⟨fun h ↦ h.2.2 hz, midnightCheckedDivRevert
          (by simp only [List.length_cons]; omega) rd4⟩
    · have hg := checkedMulGuard_overflow (a := mulDivDown repaid lif lifScale)
        (b := liquidatePriceScale) (Nat.le_of_not_gt hv)
      dsimp only [mulDivDown, lifScale, liquidatePriceScale] at hg
      have rr := midnightBlocks.midnight_block_7360_taken
        (R := maxDebt :: lltv :: lif :: price :: R)
        (by simp only [List.length_cons]; omega) (by rw [hg]; decide) (by jump_dest) rd2
      exact Or.inl ⟨fun h ↦ hv h.2.1, midnightBlocks.midnight_block_7276
        (by simp only [midnightBlocks.midnight_block_7360_taken_stack, List.length_cons]; omega) rr⟩
  · exact Or.inl ⟨fun h ↦ hm h.1, midnightCheckedMulRevert
      (by simp only [List.length_cons]; omega) (Nat.le_of_not_gt hm) rd1⟩

end Benchmarks.Midnight
