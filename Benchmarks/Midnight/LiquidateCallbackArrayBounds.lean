import Benchmarks.Midnight.LiquidateCollateralHead
import Benchmarks.Midnight.WordComplementSub

/-! The callback encoder's repeated bounds checks on the decoded collateral array. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

-- LIBRARY CANDIDATE: a signed dynamic-offset check with a constant trailing header size.
theorem calldataOffsetCheckWithHeader {bytes : ByteArray} {base relative : UInt256} {n : Nat}
    (hs : bytes.size < 2^255)
    (hb : base.toNat + relative.toNat + (n + 2) ≤ bytes.size) :
    UInt256.isZero (UInt256.slt relative
      (UInt256.lnot (UInt256.ofNat n) + UInt256.sub (UInt256.ofNat bytes.size) base)) = ⟨0⟩ := by
  have hs' : (UInt256.ofNat bytes.size).toNat = bytes.size :=
    UInt256.toNat_ofNat_of_lt (by change _ < 2^256; omega)
  have hd : (UInt256.sub (UInt256.ofNat bytes.size) base).toNat = bytes.size - base.toNat := by
    rw [usub_toNat (by rw [hs']; omega), hs']
  have hn : n + 1 < UInt256.size := by change _ < 2^256; omega
  have hn' : (UInt256.ofNat (n + 1)).toNat = n + 1 := UInt256.toNat_ofNat_of_lt hn
  have he : UInt256.lnot (UInt256.ofNat n) + UInt256.sub (UInt256.ofNat bytes.size) base =
      UInt256.ofNat (bytes.size - base.toNat - (n + 1)) := by
    rw [u256_add_comm, wordAddLnotOfNat _ n hn]
    apply u256_inj
    rw [usub_toNat (by rw [hd, hn']; omega), hd, hn',
      UInt256.toNat_ofNat_of_lt (by change _ < 2^256; omega)]
  rw [he, slt_lit_one_low (by omega) (by omega)]
  rfl

def liquidateCallbackArrayOffset (bytes : ByteArray) : UInt256 :=
  calldataWord bytes (calldataWord bytes 4 + UInt256.ofNat 100).toNat

def liquidateCallbackArrayBase (bytes : ByteArray) : UInt256 :=
  calldataWord bytes 4 + liquidateCallbackArrayOffset bytes

theorem liquidateCallbackArrayFacts {bytes : ByteArray} {m : MarketData}
    (hd : decodeCalldataMarket bytes 4 = some m) :
    let relative := liquidateCallbackArrayOffset bytes
    let base := liquidateCallbackArrayBase bytes
    let count := calldataWord bytes (base + UInt256.ofNat 4).toNat
    UInt256.isZero (UInt256.slt relative
      (UInt256.lnot (UInt256.ofNat 34) + UInt256.sub (UInt256.ofNat bytes.size)
        (calldataWord bytes 4))) = ⟨0⟩ ∧
    UInt256.gt count (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
      (UInt256.ofNat 1)) = ⟨0⟩ ∧
    UInt256.sgt (base + UInt256.ofNat 36)
      (UInt256.sub (UInt256.ofNat bytes.size) (UInt256.shiftLeft count (UInt256.ofNat 7))) = ⟨0⟩ ∧
    base + UInt256.ofNat 36 = UInt256.ofNat (marketCollateralDataStart bytes) ∧
    count = UInt256.ofNat m.collaterals.length := by
  dsimp only
  obtain ⟨hr, hs, _⟩ := decodeCalldataMarket_data hd
  obtain ⟨ho, hn, he, hl, _⟩ := decodeCalldataMarket_collateralArray hd
  have hfield : (calldataWord bytes 4 + UInt256.ofNat 100).toNat =
      4 + (calldataWord bytes 4).toNat + 96 := by
    rw [uadd_word_ofNat_toNat _ 100 (by change _ < 2^256; omega)]
    omega
  have hoff : liquidateCallbackArrayOffset bytes =
      calldataWord bytes (4 + (calldataWord bytes 4).toNat + 96) := by
    rw [liquidateCallbackArrayOffset, hfield]
  have hb : (liquidateCallbackArrayBase bytes).toNat =
      (calldataWord bytes 4).toNat + (liquidateCallbackArrayOffset bytes).toNat := by
    rw [liquidateCallbackArrayBase, uadd_toNat, Nat.mod_eq_of_lt]
    rw [hoff]
    change _ < 2^256
    omega
  have hb4 : (liquidateCallbackArrayBase bytes + UInt256.ofNat 4).toNat =
      4 + (calldataWord bytes 4).toNat + (liquidateCallbackArrayOffset bytes).toNat := by
    rw [uadd_word_ofNat_toNat _ 4 (by rw [hb, hoff]; change _ < 2^256; omega), hb]
    omega
  have hb36 : (liquidateCallbackArrayBase bytes + UInt256.ofNat 36).toNat =
      marketCollateralDataStart bytes := by
    rw [uadd_word_ofNat_toNat _ 36 (by rw [hb, hoff]; change _ < 2^256; omega), hb, hoff]
    dsimp only [marketCollateralDataStart]
    omega
  have hhead : (UInt256.ofNat 32 + (liquidateCallbackArrayBase bytes + UInt256.ofNat 4)) =
      liquidateCallbackArrayBase bytes + UInt256.ofNat 36 := by
    apply u256_inj
    rw [u256_add_comm, uadd_word_ofNat_toNat _ 32
      (by rw [hb4, hoff]; change _ < 2^256; omega), hb4, hb36]
    unfold marketCollateralDataStart
    rw [hoff]
  refine ⟨calldataOffsetCheckWithHeader hs (by rw [hoff]; omega),
    ugt_zero (by rw [hb4, hoff]; change _ ≤ 2^64 - 1; omega), ?_, ?_, ?_⟩
  · have hx := collateralArrayExtentCheck (head := liquidateCallbackArrayBase bytes + UInt256.ofNat 4)
      (count := calldataWord bytes (liquidateCallbackArrayBase bytes + UInt256.ofNat 4).toNat)
      hs (by rw [hb4, hoff]; exact hn) (by rw [hb4, hoff]; exact he)
    rw [hhead] at hx
    exact hx
  · apply u256_inj
    rw [hb36, UInt256.toNat_ofNat_of_lt (by
      have := (decodeCalldataMarket_collateralsAt hd).1; change _ < 2^256; omega)]
  · rw [hb4, hoff, hl, u256_ofNat_toNat]

end Benchmarks.Midnight
