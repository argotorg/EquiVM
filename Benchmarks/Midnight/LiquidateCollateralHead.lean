import Benchmarks.Midnight.CollateralDecodeIndex
import Benchmarks.Midnight.CollateralArrayReference
import Benchmarks.Midnight.BitmapArithmetic
import Benchmarks.Midnight.TransferBudget
import Benchmarks.Midnight.RuntimeBlocks_031

/-! Reload the validated market's collateral array and select the highest active bit. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def marketCollateralDataStart (bytes : ByteArray) : Nat :=
  let base := 4 + (calldataWord bytes 4).toNat
  base + (calldataWord bytes (base + 96)).toNat + 32

theorem decodeCalldataMarket_collateralsAt {bytes : ByteArray} {m : MarketData}
    (hd : decodeCalldataMarket bytes 4 = some m) :
    marketCollateralDataStart bytes < 2^128 ∧
      decodeCollateralElements m.collaterals.length bytes (marketCollateralDataStart bytes) =
        some m.collaterals := by
  obtain ⟨hr, _, _⟩ := decodeCalldataMarket_data hd
  obtain ⟨ho, _, _, hl, hc⟩ := decodeCalldataMarket_collateralArray hd
  exact ⟨by dsimp only [marketCollateralDataStart]; omega, by rw [hl]; exact hc⟩

theorem midnightLiquidateCollateralHead {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray}
    {aw debtWord reverseRep rep maxDebt price pos dp dl borrower badDebt bitmap budgetRoot : UInt256}
    {credit : Nat} {m : MarketData} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 24 ≤ 1024) (hfork : I.fork ≥ .osaka)
    (hd : decodeCalldataMarket I.calldata 4 = some m)
    (hbitmap : memLoad (UInt256.ofNat 704) mem = bitmap)
    (hb : TransferBudget budgetRoot credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨7846⟩
      ([debtWord, reverseRep, rep, maxDebt, price, pos, dp, dl, borrower, badDebt] ++ R)
      mem aw rdata σ k C) :
    ∃ aw' k' C', TransferBudget budgetRoot credit mem aw' C' ∧
      RD midnightBytecode I g s0 ⟨20541⟩
        ([UInt256.ofNat (marketCollateralDataStart I.calldata),
          UInt256.ofNat m.collaterals.length, bitmapMsb bitmap, ⟨7891⟩,
          UInt256.ofNat I.calldata.size, ⟨7896⟩, maxDebt, badDebt, reverseRep, rep, ⟨4⟩,
          price, pos, dp, dl, borrower, debtWord] ++ R) mem aw' rdata σ k' C' := by
  obtain ⟨hr, hs, _⟩ := decodeCalldataMarket_data hd
  obtain ⟨ho, hn, he, hl, _⟩ := decodeCalldataMarket_collateralArray hd
  let base := UInt256.ofNat 4 + calldataWord I.calldata 4
  let field := calldataWord I.calldata 4 + UInt256.ofNat 100
  have hbase : base.toNat = 4 + (calldataWord I.calldata 4).toNat := by
    dsimp only [base]
    rw [u256_add_comm, uadd_word_ofNat_toNat _ 4 (by change _ < 2^256; omega)]
    omega
  have hfield : field.toNat = 4 + (calldataWord I.calldata 4).toNat + 96 := by
    dsimp only [field]
    rw [uadd_word_ofNat_toNat _ 100 (by change _ < 2^256; omega)]
    omega
  have hhead : (base + calldataWord I.calldata field.toNat).toNat =
      4 + (calldataWord I.calldata 4).toNat +
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat + 96)).toNat := by
    rw [uadd_toNat, hbase, hfield, Nat.mod_eq_of_lt (by change _ < 2^256; omega)]
  have hp : UInt256.ofNat 32 + (base + calldataWord I.calldata field.toNat) =
      UInt256.ofNat (marketCollateralDataStart I.calldata) := by
    apply u256_inj
    rw [u256_add_comm, uadd_word_ofNat_toNat _ 32 (by rw [hhead]; change _ < 2^256; omega),
      hhead, UInt256.toNat_ofNat_of_lt (by
        dsimp only [marketCollateralDataStart]; change _ < 2^256; omega)]
    rfl
  have hcount : calldataWord I.calldata (base + calldataWord I.calldata field.toNat).toNat =
      UInt256.ofNat m.collaterals.length := by
    rw [hhead, hl, u256_ofNat_toNat]
  have rd1 := midnightBlocks.midnight_block_7846 (R := R) (by omega) (by jump_dest) rd
  change RD midnightBytecode I g s0 ⟨20488⟩
    ([base, field, ⟨7873⟩, ⟨7891⟩, ⟨7896⟩, maxDebt, badDebt, reverseRep, rep, ⟨4⟩,
      price, pos, dp, dl, borrower, debtWord] ++ R) mem aw rdata σ _ _ at rd1
  obtain ⟨k2, C2, hc2, rd2⟩ := midnightCollateralArrayReference
    (R := [⟨7891⟩, ⟨7896⟩, maxDebt, badDebt, reverseRep, rep, ⟨4⟩,
      price, pos, dp, dl, borrower, debtWord] ++ R)
    (by simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add]; omega) hs (by rw [hbase]; omega)
    (by rw [hfield]; exact ho) (by rw [hhead]; exact hn)
    (by rw [hhead]; exact he) (by jump_dest) rd1
  rw [hp, hcount] at rd2
  have rd3 := midnightBlocks.midnight_block_7873
    (R := [⟨7896⟩, maxDebt, badDebt, reverseRep, rep, ⟨4⟩,
      price, pos, dp, dl, borrower, debtWord] ++ R)
    (by simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add]; omega) hfork (by jump_dest) rd2
  have hb2 : TransferBudget budgetRoot credit mem aw C2 := hb.mono (by omega)
  have hb3 := transferBudgetAt (root := budgetRoot) (credit := credit) rd3
    (by transfer_budget hb2)
  simp only [midnightBlocks.midnight_block_7873_stack, hbitmap] at rd3
  exact ⟨_, _, _, hb3, rd3⟩

end Benchmarks.Midnight
