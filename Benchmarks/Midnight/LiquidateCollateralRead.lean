import Benchmarks.Midnight.LiquidateCollateralHead
import Benchmarks.Midnight.CollateralCalldataBudget
import Benchmarks.Midnight.CollateralRecordMemory

variable {fork : Ethereum.Fork}

/-! The liquidation loop checks its collateral index and copies the selected record. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightLiquidateCollateralRead {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray}
    {aw debtWord reverseRep rep maxDebt price pos dp dl borrower badDebt bitmap root budgetRoot : UInt256}
    {credit : Nat} {m : MarketData} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 24 ≤ 1024) (hfork : fork ≥ .osaka)
    (hd : decodeCalldataMarket I.calldata 4 = some m)
    (hbitmap : memLoad (UInt256.ofNat 704) mem = bitmap)
    (hbits : bitmap.toNat < 2^128) (hnz : bitmap.toNat ≠ 0)
    (hroot : root.toNat + 128 < 2^64) (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (hb : TransferBudget budgetRoot credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨7846⟩
      ([debtWord, reverseRep, rep, maxDebt, price, pos, dp, dl, borrower, badDebt] ++ R)
      mem aw rdata σ k C) :
    (¬ (bitmapMsb bitmap).toNat < m.collaterals.length ∧ RDrev fork midnightBytecode g s0) ∨
    ∃ (hi : (bitmapMsb bitmap).toNat < m.collaterals.length) (aw' : UInt256) (k' C' : Nat),
      TransferBudget budgetRoot credit
        (collateralRecordMemory mem root m.collaterals[(bitmapMsb bitmap).toNat]) aw' C' ∧
      RD fork midnightBytecode I g s0 ⟨7896⟩
        ([root, maxDebt, badDebt, reverseRep, rep, ⟨4⟩, price, pos, dp, dl, borrower, debtWord] ++ R)
        (collateralRecordMemory mem root m.collaterals[(bitmapMsb bitmap).toNat]) aw' rdata σ k' C' := by
  let index := bitmapMsb bitmap
  have hi128 : index.toNat < 128 := bitmapMsb_lt hnz hbits
  have hs := (decodeCalldataMarket_data hd).2.1
  obtain ⟨hstart, hc⟩ := decodeCalldataMarket_collateralsAt hd
  have hn : m.collaterals.length < 2^64 := by
    obtain ⟨_, hn, _, hl, _⟩ := decodeCalldataMarket_collateralArray hd
    rw [hl]
    exact hn
  have hcount : (UInt256.ofNat m.collaterals.length).toNat = m.collaterals.length :=
    UInt256.toNat_ofNat_of_lt (by change _ < 2^256; omega)
  have hp : (UInt256.ofNat (marketCollateralDataStart I.calldata)).toNat =
      marketCollateralDataStart I.calldata :=
    UInt256.toNat_ofNat_of_lt (by change _ < 2^256; omega)
  obtain ⟨aw1, k1, C1, hb1, rd1⟩ := midnightLiquidateCollateralHead
    hstack hfork hd hbitmap hb rd
  by_cases hi : index.toNat < m.collaterals.length
  · obtain ⟨hbound, hcanon, hat⟩ := decodeCollateralElements_get hc index.toNat hi
    have hindex : (UInt256.shiftLeft index ⟨7⟩ +
        UInt256.ofNat (marketCollateralDataStart I.calldata)).toNat =
        marketCollateralDataStart I.calldata + 128 * index.toNat := by
      rw [calldataCollateralIndex_toNat (by omega) (by rw [hp]; change _ < 2^256; omega), hp]
    obtain ⟨k2, C2, hc2, rd2⟩ := midnightCalldataCollateralIndex
      (R := [UInt256.ofNat I.calldata.size, ⟨7896⟩, maxDebt, badDebt, reverseRep, rep, ⟨4⟩,
        price, pos, dp, dl, borrower, debtWord] ++ R)
      (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
      (by rw [hcount]; exact hi) (by jump_dest) rd1
    have rd3 := midnightBlocks.midnight_block_7891 (by
      simp only [List.length_append, List.length_cons, List.length_nil]; omega)
      (by jump_dest) rd2
    have hb3 := hb1.mono (show C1 ≤ C2 + 12 by omega)
    rcases midnightCollateralCalldata_budget
        (R := [maxDebt, badDebt, reverseRep, rep, ⟨4⟩, price, pos, dp, dl, borrower, debtWord] ++ R)
        (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
        (by rw [hindex]; exact hbound) hs hfree (by omega) (by jump_dest) hb3 rd3 with
      ⟨hbad, _⟩ | ⟨hbad, _⟩ | ⟨_, _, aw4, k4, C4, hb4, rd4⟩
    · exact False.elim (hbad hroot)
    · exact False.elim (hbad (by rw [hindex]; exact hcanon))
    · have hm : CollateralData.at I.calldata
          (UInt256.shiftLeft index ⟨7⟩ + UInt256.ofNat (marketCollateralDataStart I.calldata)).toNat =
          m.collaterals[index.toNat] := by rw [hindex, ← hat]
      rw [hm] at hb4 rd4
      exact Or.inr ⟨hi, aw4, k4, C4, hb4, rd4⟩
  · have hcond : UInt256.isZero (UInt256.lt index (UInt256.ofNat m.collaterals.length)) ≠ ⟨0⟩ := by
      rw [ult_zero (by rw [hcount]; omega)]
      decide
    have rd2 := midnightBlocks.midnight_block_20541_taken
      (R := [⟨7891⟩, UInt256.ofNat I.calldata.size, ⟨7896⟩, maxDebt, badDebt, reverseRep, rep, ⟨4⟩,
        price, pos, dp, dl, borrower, debtWord] ++ R)
      (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
      hcond (by jump_dest) rd1
    exact Or.inl ⟨hi, midnightBlocks.midnight_block_19161 (by
      simp only [midnightBlocks.midnight_block_20541_taken_stack, List.length_append,
        List.length_cons, List.length_nil]; omega) rd2⟩

end Benchmarks.Midnight
