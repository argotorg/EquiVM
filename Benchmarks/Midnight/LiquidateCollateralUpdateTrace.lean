import Benchmarks.Midnight.LiquidateCollateralWriteGas
import Benchmarks.Midnight.CollateralSourceState
import Benchmarks.Midnight.SupplyCollateralArithmetic
import Benchmarks.Midnight.Uint128Arithmetic
import Benchmarks.Midnight.TransferBudget
import Benchmarks.Midnight.RuntimeBlocks_028

/-! Checked subtraction of seized collateral and its packed storage update. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem midnightLiquidateCollateralUpdate {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw d0 d1 d2 d3 id borrower index seized root : UInt256}
    {σ : AccountMap} {k C credit : Nat} {R : List UInt256} (hstack : R.length + 12 ≤ 1024)
    (hi : calldataWord I.calldata 36 = index) (hseized : memLoad ⟨640⟩ mem = seized)
    (hb : TransferBudget root credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨6744⟩
      (d0 :: d1 :: d2 :: d3 :: positionSlot id borrower :: R) mem aw rdata σ k C) :
    let old := collateralWord (fun slot ↦ solcSlotWordAt slot σ I) id borrower index
    let safe := index.toNat < 128 ∧ seized.toNat < 2^128 ∧ seized.toNat ≤ old.toNat
    (¬ safe ∧ RDrev midnightBytecode g s0) ∨
    (safe ∧ I.perm = false ∧ RDstatic midnightBytecode g s0) ∨
    (safe ∧ I.perm = true ∧ ∃ aw' k' C', TransferBudget root credit mem aw' C' ∧
      RD midnightBytecode I g s0 ⟨6820⟩
        (UInt256.sub old seized :: uint128Mask :: positionSlot id borrower :: R)
        mem aw' rdata (collateralWriteAccounts σ I id borrower index (UInt256.sub old seized))
        k' C') := by
  dsimp only
  let old := collateralWord (fun slot ↦ solcSlotWordAt slot σ I) id borrower index
  have hold : old.toNat < 2^128 := low128_lt _
  have rd1 := midnightBlocks.midnight_block_6744 (R := R) (by omega) (by jump_dest) rd
  have hi' : uInt256OfByteArray (I.calldata.readBytes 36 32) = index := hi
  simp only [midnightBlocks.midnight_block_6744_stack,
    show (UInt256.ofNat 36).toNat = 36 from rfl, hi', uint128Mask_computed] at rd1
  by_cases hidx : index.toNat < 128
  · obtain ⟨k2, C2, hc2, rd2⟩ := midnightUint128ArrayLocation_mono
      (by simp only [List.length_cons]; omega) hidx (by jump_dest) rd1
    obtain ⟨k3, C3, hc3, rd3⟩ := liquidate_block_6775_paid
      (by simp only [List.length_cons]; omega) (by jump_dest) rd2
    simp only [midnightBlocks.midnight_block_6775_stack,
      show UInt256.ofNat 640 = (⟨640⟩ : UInt256) from rfl, hseized,
      (uint128ArrayIndexFacts index hidx).2.2] at rd3
    change RD midnightBytecode I g s0 ⟨23403⟩
      (seized :: ⟨6795⟩ :: old :: ⟨6801⟩ :: uint128Mask :: positionSlot id borrower :: R)
      mem (M aw ⟨640⟩ ⟨32⟩) rdata σ k3 C3 at rd3
    have hb3 := transferBudgetAt (root := root) (credit := credit) rd3 (by
      simp only [show UInt256.ofNat 640 = (⟨640⟩ : UInt256) from rfl, memExpansionCost] at hc3
      transfer_budget hb)
    by_cases h128 : seized.toNat < 2^128
    · obtain ⟨k4, C4, hc4, rd4⟩ := midnightToUint128_mono
        (by simp only [List.length_cons]; omega) h128 (by jump_dest) rd3
      have rd5 := midnightBlocks.midnight_block_6795
        (by simp only [List.length_cons]; omega) (by jump_dest) rd4
      simp only [midnightBlocks.midnight_block_6795_stack] at rd5
      by_cases hle : seized.toNat ≤ old.toNat
      · obtain ⟨k6, C6, hc6, rd6⟩ := midnightCheckedSub128_mono
          (by simp only [List.length_cons]; omega) hold h128 hle (by jump_dest) rd5
        have rd7 := midnightBlocks.midnight_block_6801
          (by omega) (by jump_dest) rd6
        simp only [midnightBlocks.midnight_block_6801_stack,
          show (UInt256.ofNat 36).toNat = 36 from rfl, hi'] at rd7
        obtain ⟨k8, C8, hc8, rd8⟩ := midnightUint128ArrayLocation_mono
          (by simp only [List.length_cons]; omega) hidx (by jump_dest) rd7
        by_cases hp : I.perm = true
        · obtain ⟨k9, C9, hc9, rd9⟩ := collateral_block_4593_mono
            (by simp only [List.length_cons]; omega) hp (by jump_dest) rd8
          simp only [midnightBlocks.midnight_block_4593_stack, uint128Mask_computed,
            (uint128ArrayIndexFacts index hidx).2.2] at rd9
          exact Or.inr (Or.inr ⟨⟨hidx, h128, hle⟩, hp, _, k9, C9,
            hb3.mono (by omega), rd9⟩)
        · exact Or.inr (Or.inl ⟨⟨hidx, h128, hle⟩, Bool.eq_false_iff.mpr hp,
            collateral_block_4593_static (by simp only [List.length_cons]; omega)
              (Bool.eq_false_iff.mpr hp) rd8⟩)
      · exact Or.inl ⟨fun h ↦ hle h.2.2, midnightCheckedSub128Revert
          (by simp only [List.length_cons]; omega) hold h128 (Nat.lt_of_not_ge hle) rd5⟩
    · exact Or.inl ⟨fun h ↦ h128 h.2.1, midnightToUint128Revert
        (by simp only [List.length_cons]; omega) (Nat.le_of_not_gt h128) rd3⟩
  · exact Or.inl ⟨fun h ↦ hidx h.1, midnightUint128ArrayLocationRevert
      (by simp only [List.length_cons]; omega) (Nat.le_of_not_gt hidx) rd1⟩

end Benchmarks.Midnight
