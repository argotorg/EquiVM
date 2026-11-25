import Benchmarks.Midnight.LiquidateLockAllocation
import Benchmarks.Midnight.LiquidateEligibility

variable {fork : Ethereum.Fork}

/-! The runtime lock, maturity, and health checks following the collateral loop. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem decodeCalldataMarket_maturity {bytes : ByteArray} {m : MarketData}
    (hd : decodeCalldataMarket bytes 4 = some m) :
    calldataWord bytes (calldataWord bytes 4 + UInt256.ofNat 132).toNat = m.maturity := by
  obtain ⟨hr, _, hdata⟩ := decodeCalldataMarket_data hd
  obtain ⟨_, _, _, _, _, cs, _, he⟩ := decodeMarketData_success hdata
  rw [he, uadd_word_ofNat_toNat _ 132 (by change _ < 2^256; omega)]
  change calldataWord bytes ((calldataWord bytes 4).toNat + 132) =
    calldataWord bytes (4 + (calldataWord bytes 4).toNat + 128)
  exact congrArg (calldataWord bytes) (by omega)

theorem midnightLiquidateEligibility {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw root id borrower debtWord reverseRep rep maxDebt price pos dp dl
      badDebt receiver mode budgetRoot : UInt256} {credit : Nat} {m : MarketData}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 18 ≤ 1024) (hd : decodeCalldataMarket I.calldata 4 = some m)
    (hlen : memLoad root mem = ⟨96⟩)
    (hhash : keccakWord (root + UInt256.ofNat 32) ⟨96⟩ mem =
      lockSlot liquidationLockBase id borrower)
    (hb : TransferBudget budgetRoot credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨5442⟩
      ([root, debtWord, reverseRep, rep, maxDebt, price, pos, dp, dl, borrower, badDebt,
        receiver, mode] ++ R) mem aw rdata σ k C) :
    let lock := codeOwnerTransientWord I σ (lockSlot liquidationLockBase id borrower)
    (¬ LiquidateEligible I m lock mode (low128 debtWord) maxDebt ∧ RDrev fork midnightBytecode g s0) ∨
    (LiquidateEligible I m lock mode (low128 debtWord) maxDebt ∧ ∃ aw' k' C',
      TransferBudget budgetRoot credit mem aw' C' ∧
      RD fork midnightBytecode I g s0 ⟨5463⟩
        ([debtWord, reverseRep, rep, maxDebt, price, pos, dp, dl, borrower, badDebt,
          receiver, mode] ++ R) mem aw' rdata σ k' C') := by
  dsimp only
  let lock := codeOwnerTransientWord I σ (lockSlot liquidationLockBase id borrower)
  have hread : (σ.get? I.codeOwner |>.option (⟨0⟩ : UInt256)
      (fun ac ↦ ac.tstorage.getD (keccakWord (root + UInt256.ofNat 32) (memLoad root mem) mem)
        ⟨0⟩)) = lock := by rw [hlen, hhash]
  by_cases hl : lock = ⟨0⟩
  · have rd1 := midnightBlocks.midnight_block_5442_taken
      (R := [debtWord, reverseRep, rep, maxDebt, price, pos, dp, dl, borrower, badDebt,
        receiver, mode] ++ R)
      (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
      (by rw [hread, hl]; decide) (by jump_dest) rd
    have hb1 := transferBudgetAt (root := budgetRoot) (credit := credit) rd1
      (by transfer_budget hb)
    simp only [midnightBlocks.midnight_block_5442_taken_stack, hread, hl] at rd1
    by_cases hmode : mode = ⟨0⟩
    · have rd2 := midnightBlocks.midnight_block_7808_taken
        (R := R) (by omega) (by rw [hmode]; decide) (by jump_dest) rd1
      have rd3 := midnightBlocks.midnight_block_7829 (R := [price, pos, dp, dl, borrower,
        badDebt, receiver, mode] ++ R)
        (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
        (by jump_dest) rd2
      have hb3 := transferBudgetAt (root := budgetRoot) (credit := credit) rd3
        (by transfer_budget hb1)
      simp only [midnightBlocks.midnight_block_7829_stack, uint128Mask_computed] at rd3
      change RD fork midnightBytecode I g s0 ⟨5457⟩
        (UInt256.gt (low128 debtWord) maxDebt :: [debtWord, reverseRep, rep, maxDebt,
          price, pos, dp, dl, borrower, badDebt, receiver, mode] ++ R) mem _ rdata σ _ _ at rd3
      by_cases hhealth : maxDebt.toNat < (low128 debtWord).toNat
      · have rd4 := midnightBlocks.midnight_block_5457_fallthrough
          (R := [debtWord, reverseRep, rep, maxDebt, price, pos, dp, dl, borrower, badDebt,
            receiver, mode] ++ R)
          (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
          (by rw [ugt_one hhealth]; rfl) rd3
        exact Or.inr ⟨⟨hl, by simpa only [hmode, ite_true] using hhealth⟩,
          _, _, _, hb3.mono (by omega), rd4⟩
      · have rd4 := midnightBlocks.midnight_block_5457_taken
          (R := [debtWord, reverseRep, rep, maxDebt, price, pos, dp, dl, borrower, badDebt,
            receiver, mode] ++ R)
          (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
          (by rw [ugt_zero (by exact Nat.le_of_not_gt hhealth)]; decide) (by jump_dest) rd3
        exact Or.inl ⟨fun h ↦ hhealth (by simpa only [hmode, ite_true] using h.2),
          midnightBlocks.midnight_block_7787 (R := [debtWord, reverseRep, rep, maxDebt, price,
            pos, dp, dl, borrower, badDebt, receiver, mode] ++ R) (by
            simp only [List.length_append, List.length_cons, List.length_nil]; omega) rd4⟩
    · have rd2 := midnightBlocks.midnight_block_7808_fallthrough (R := R) (by omega)
        (isZero_eq_zero_of_ne hmode) rd1
      have rd3 := midnightBlocks.midnight_block_7816
        (R := [debtWord, reverseRep, rep, maxDebt, price, pos, dp, dl, borrower, badDebt,
          receiver, mode] ++ R) (by
        simp only [List.length_append, List.length_cons, List.length_nil]; omega)
        (by jump_dest) rd2
      have hb3 := transferBudgetAt (root := budgetRoot) (credit := credit) rd3
        (by transfer_budget hb1)
      change RD fork midnightBytecode I g s0 ⟨5457⟩
        (UInt256.gt (UInt256.ofNat I.header.timestamp)
          (calldataWord I.calldata (calldataWord I.calldata 4 + UInt256.ofNat 132).toNat) ::
          [debtWord, reverseRep, rep, maxDebt, price, pos, dp, dl, borrower, badDebt,
            receiver, mode] ++ R) mem _ rdata σ _ _ at rd3
      rw [decodeCalldataMarket_maturity hd] at rd3
      by_cases htime : m.maturity.toNat < (UInt256.ofNat I.header.timestamp).toNat
      · have rd4 := midnightBlocks.midnight_block_5457_fallthrough
          (R := [debtWord, reverseRep, rep, maxDebt, price, pos, dp, dl, borrower, badDebt,
            receiver, mode] ++ R)
          (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
          (by rw [ugt_one htime]; rfl) rd3
        exact Or.inr ⟨⟨hl, by simpa only [if_neg hmode] using htime⟩,
          _, _, _, hb3.mono (by omega), rd4⟩
      · have rd4 := midnightBlocks.midnight_block_5457_taken
          (R := [debtWord, reverseRep, rep, maxDebt, price, pos, dp, dl, borrower, badDebt,
            receiver, mode] ++ R)
          (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
          (by rw [ugt_zero (by exact Nat.le_of_not_gt htime)]; decide) (by jump_dest) rd3
        exact Or.inl ⟨fun h ↦ htime (by simpa only [if_neg hmode] using h.2),
          midnightBlocks.midnight_block_7787 (R := [debtWord, reverseRep, rep, maxDebt, price,
            pos, dp, dl, borrower, badDebt, receiver, mode] ++ R) (by
            simp only [List.length_append, List.length_cons, List.length_nil]; omega) rd4⟩
  · have rd1 := midnightBlocks.midnight_block_5442_fallthrough
      (R := [debtWord, reverseRep, rep, maxDebt, price, pos, dp, dl, borrower, badDebt,
        receiver, mode] ++ R)
      (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
      (by rw [hread]; exact isZero_eq_zero_of_ne hl) rd
    simp only [midnightBlocks.midnight_block_5442_fallthrough_stack, hread,
      isZero_eq_zero_of_ne hl] at rd1
    have rd2 := midnightBlocks.midnight_block_5457_taken
      (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
      (by decide) (by jump_dest) rd1
    exact Or.inl ⟨fun h ↦ hl h.1, midnightBlocks.midnight_block_7787
      (R := [debtWord, reverseRep, rep, maxDebt, price, pos, dp, dl, borrower, badDebt,
        receiver, mode] ++ R) (by
      simp only [List.length_append, List.length_cons, List.length_nil]; omega) rd2⟩

end Benchmarks.Midnight
