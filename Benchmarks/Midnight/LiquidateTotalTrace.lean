import Benchmarks.Midnight.LiquidateStorageGas
import Benchmarks.Midnight.CheckedUint128Gas

/-! Loss-factor storage followed by the checked total-unit deduction. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightLiquidateTotal {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray}
    {aw root newLoss oldWord reverseRep rep maxDebt price pos dp dl borrower badDebt : UInt256}
    {σ : AccountMap} {k C credit : Nat} {R : List UInt256}
    (hstack : R.length + 17 ≤ 1024) (hp : I.perm = true)
    (hb : TransferBudget root credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨7541⟩
      ([newLoss, ⟨7571⟩, oldWord, reverseRep, rep, maxDebt, price, pos, dp, dl, borrower, badDebt] ++ R)
      mem aw rdata σ k C) :
    let σ' := storeHigh128Accounts σ I (memLoad (UInt256.ofNat 672) mem) newLoss
    let total := low128 (solcSlotWordAt (memLoad (UInt256.ofNat 672) mem) σ' I)
    (¬ (badDebt.toNat < 2 ^ 128 ∧ badDebt.toNat ≤ total.toNat) ∧
      RDrev midnightBytecode g s0) ∨
    (badDebt.toNat < 2 ^ 128 ∧ badDebt.toNat ≤ total.toNat ∧ ∃ aw' k' C',
      TransferBudget root credit mem aw' C' ∧
      RD midnightBytecode I g s0 ⟨7603⟩
        ([UInt256.sub total badDebt, uint128Mask, oldWord, reverseRep, rep,
          maxDebt, price, pos, dp, dl, borrower, badDebt] ++ R) mem aw' rdata σ' k' C') := by
  dsimp only
  let σ' := storeHigh128Accounts σ I (memLoad (UInt256.ofNat 672) mem) newLoss
  let total := low128 (solcSlotWordAt (memLoad (UInt256.ofNat 672) mem) σ' I)
  obtain ⟨k1, C1, hb1, rd1⟩ := liquidate_block_7541_budget
    (R := oldWord :: reverseRep :: rep :: maxDebt :: price :: pos :: dp :: dl :: borrower :: badDebt :: R)
    (by simp only [List.length_cons]; omega) hp (by jump_dest) hb rd
  simp only [midnightBlocks.midnight_block_7541_stack, uint128Mask_computed,
    shiftLeft128_highMask] at rd1
  change RD midnightBytecode I g s0 ⟨7571⟩
    ([oldWord, reverseRep, rep, maxDebt, price, pos, dp, dl, borrower, badDebt] ++ R)
    mem _ rdata σ' k1 C1 at rd1
  have rd2 := midnightBlocks.midnight_block_7571 (R := R)
    (by omega) (by jump_dest) rd1
  simp only [midnightBlocks.midnight_block_7571_stack, uint128Mask_computed] at rd2
  have hb2 := transferBudgetAt rd2 (hb1.mono (by omega))
  by_cases hfit : badDebt.toNat < 2 ^ 128
  · obtain ⟨k3, C3, hc3, rd3⟩ := midnightToUint128_mono
      (by simp only [List.length_cons]; omega) hfit (by jump_dest) rd2
    obtain ⟨k4, C4, hb4, rd4⟩ := liquidate_block_7591_budget
      (R := oldWord :: reverseRep :: rep :: maxDebt :: price :: pos :: dp :: dl :: borrower :: badDebt :: R)
      (by simp only [List.length_cons]; omega) (by jump_dest) (hb2.mono hc3) rd3
    simp only [midnightBlocks.midnight_block_7591_stack] at rd4
    by_cases hle : badDebt.toNat ≤ total.toNat
    · obtain ⟨k5, C5, hc5, rd5⟩ := midnightCheckedSub128_mono
        (by simp only [List.length_cons]; omega) (low128_lt _) hfit hle (by jump_dest) rd4
      exact Or.inr ⟨hfit, hle, _, _, _, hb4.mono hc5, rd5⟩
    · exact Or.inl ⟨fun h ↦ hle h.2, midnightCheckedSub128Revert
        (by simp only [List.length_cons]; omega) (low128_lt _) hfit (Nat.lt_of_not_ge hle) rd4⟩
  · exact Or.inl ⟨fun h ↦ hfit h.1, midnightToUint128Revert
      (by simp only [List.length_cons]; omega) (by omega) rd2⟩

end Benchmarks.Midnight
