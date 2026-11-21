import Benchmarks.Midnight.LiquidateStorageGas

/-! The total-unit store and branch into the remaining-fee calculation. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightLiquidateFeeEntry {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw root value oldWord : UInt256} {σ : AccountMap}
    {k C credit : Nat} {R : List UInt256} (hstack : R.length + 6 ≤ 1024)
    (hp : I.perm = true) (hzero : memLoad (UInt256.ofNat 800) mem = ⟨0⟩)
    (hb : TransferBudget root credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨7603⟩
      (value :: uint128Mask :: oldWord :: R) mem aw rdata σ k C) :
    let σ' := storeLow128Accounts σ I (memLoad (UInt256.ofNat 672) mem) value
    let loss := UInt256.shiftRight (solcSlotWordAt (memLoad (UInt256.ofNat 672) mem) σ' I) ⟨128⟩
    let fee := UInt256.shiftRight (solcSlotWordAt (memLoad (UInt256.ofNat 672) mem + ⟨1⟩) σ' I) ⟨128⟩
    ((UInt256.shiftRight oldWord ⟨128⟩).toNat < 2 ^ 128 - 1 ∧ ∃ aw' k' C',
      TransferBudget root credit mem aw' C' ∧ RD midnightBytecode I g s0 ⟨7694⟩
        (fee :: oldWord :: complement128 loss :: R) mem aw' rdata σ' k' C') ∨
    (¬ (UInt256.shiftRight oldWord ⟨128⟩).toNat < 2 ^ 128 - 1 ∧ ∃ aw' k' C',
      TransferBudget root credit mem aw' C' ∧ RD midnightBytecode I g s0 ⟨7735⟩
        (⟨0⟩ :: ⟨7768⟩ :: R) mem aw' rdata σ' k' C') := by
  dsimp only
  by_cases hl : (UInt256.shiftRight oldWord ⟨128⟩).toNat < 2 ^ 128 - 1
  · have hlt : UInt256.lt (UInt256.shiftRight oldWord ⟨128⟩) uint128Mask = ⟨1⟩ := ult_one hl
    obtain ⟨k1, C1, hb1, rd1⟩ := liquidate_block_7603_fallthrough_budget (R := R)
      (by omega) hp (by
        rw [uint128Mask_computed]
        change UInt256.eq ⟨0⟩ (UInt256.lt (UInt256.shiftRight oldWord ⟨128⟩) uint128Mask) = _
        rw [hlt]; decide) hb rd
    simp only [midnightBlocks.midnight_block_7603_fallthrough_stack, uint128Mask_computed] at rd1
    obtain ⟨k2, C2, hb2, rd2⟩ := liquidate_block_7650_fallthrough_budget hstack
      (by rw [uint128Mask_computed]; exact complement128_guard (shiftRight128_lt _)) hb1 rd1
    refine Or.inl ⟨hl, _, k2, C2, hb2, ?_⟩
    simpa only [midnightBlocks.midnight_block_7650_fallthrough_stack, uint128Mask_computed,
      complement128, storeLow128Accounts, setUint128LowWord] using rd2
  · have hlt : UInt256.lt (UInt256.shiftRight oldWord ⟨128⟩) uint128Mask = ⟨0⟩ := ult_zero (by
      change 340282366920938463463374607431768211455 ≤ _; omega)
    obtain ⟨k1, C1, hb1, rd1⟩ := liquidate_block_7603_taken_budget (R := R)
      (by omega) hp (by
        rw [uint128Mask_computed]
        change UInt256.eq ⟨0⟩ (UInt256.lt (UInt256.shiftRight oldWord ⟨128⟩) uint128Mask) ≠ _
        rw [hlt]; decide) (by jump_dest) hb rd
    simp only [midnightBlocks.midnight_block_7603_taken_stack, uint128Mask_computed] at rd1
    have rd2 := midnightBlocks.midnight_block_7774 (R := R) (by omega) (by jump_dest) rd1
    have hb2 := transferBudgetAt (root := root) (credit := credit) rd2 (by transfer_budget hb1)
    refine Or.inr ⟨hl, _, k1 + 7, _, hb2, ?_⟩
    simpa only [midnightBlocks.midnight_block_7774_stack, hzero,
      storeLow128Accounts, setUint128LowWord] using rd2

end Benchmarks.Midnight
