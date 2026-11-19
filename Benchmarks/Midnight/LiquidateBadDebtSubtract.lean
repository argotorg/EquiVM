import Benchmarks.Midnight.LiquidatePostLoopGuard
import Benchmarks.Midnight.CheckedUint128Gas

/-! The checked initial subtraction in liquidation's bad-debt branch. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightLiquidateBadDebtSubtract {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw debtWord reverseRep rep maxDebt price pos dp dl borrower badDebt : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (hstack : R.length + 16 ≤ 1024)
    (rd : RD midnightBytecode I g s0 ⟨7431⟩
      ([debtWord, reverseRep, rep, maxDebt, price, pos, dp, dl, borrower, badDebt] ++ R)
      mem aw rdata σ k C) :
    ((low128 debtWord).toNat < (low128 badDebt).toNat ∧ RDrev midnightBytecode g s0) ∨
    ((low128 badDebt).toNat ≤ (low128 debtWord).toNat ∧ ∃ k' C', C ≤ C' ∧
      RD midnightBytecode I g s0 ⟨7454⟩
        ([UInt256.sub (low128 debtWord) (low128 badDebt), uint128Mask, reverseRep, rep,
          maxDebt, price, pos, dp, dl, borrower, badDebt] ++ R) mem aw rdata σ k' C') := by
  have rd1 := midnightBlocks.midnight_block_7431 (R := R) (by omega) (by jump_dest) rd
  simp only [midnightBlocks.midnight_block_7431_stack, uint128Mask_computed] at rd1
  change RD midnightBytecode I g s0 ⟨19743⟩
    ([low128 debtWord, low128 badDebt, ⟨7454⟩, uint128Mask, reverseRep, rep,
      maxDebt, price, pos, dp, dl, borrower, badDebt] ++ R) mem aw rdata σ _ _ at rd1
  by_cases hle : (low128 badDebt).toNat ≤ (low128 debtWord).toNat
  · obtain ⟨k2, C2, hc2, rd2⟩ := midnightCheckedSub128_mono
      (R := [uint128Mask, reverseRep, rep, maxDebt, price, pos, dp, dl, borrower, badDebt] ++ R)
      (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
      (low128_lt _) (low128_lt _) hle (by jump_dest) rd1
    exact Or.inr ⟨hle, k2, C2, by omega, rd2⟩
  · exact Or.inl ⟨Nat.lt_of_not_ge hle, midnightCheckedSub128Revert
      (R := [uint128Mask, reverseRep, rep, maxDebt, price, pos, dp, dl, borrower, badDebt] ++ R)
      (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
      (low128_lt _) (low128_lt _) (Nat.lt_of_not_ge hle) rd1⟩

end Benchmarks.Midnight
