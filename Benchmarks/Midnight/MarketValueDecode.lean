import Benchmarks.Midnight.MarketData
import Benchmarks.Midnight.CollateralDecode

/-! A typed view of stored-market decoding, with all rejection guards retained. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def decodeMarketData (bytes : ByteArray) (start : Nat) : Option MarketData := do
  if ¬ (start + 256 ≤ bytes.size ∧ MarketData.canonicalAt bytes start) then none else
    let relative := (calldataWord bytes (start + 96)).toNat
    if solcMaxU64 < relative then none else
      let n ← readNat? bytes.toList (start + relative)
      if solcMaxU64 < n then none else
        let values ← decodeCollateralElements n bytes (start + relative + 32)
        pure (MarketData.at bytes start values)

theorem decodeMarketTail {bytes : ByteArray} {start maxEnd : Nat}
    (hlen : start + 256 ≤ bytes.size) :
    decodeABIValues? [Model.u256, Model.u256, Model.addr, Model.addr]
      bytes.toList start 128 256 maxEnd =
      if (calldataWord bytes (start + 192)).toNat < EVM.addressModulus ∧
          (calldataWord bytes (start + 224)).toNat < EVM.addressModulus then
        some ([.int (Int.ofNat (calldataWord bytes (start + 128)).toNat),
          .int (Int.ofNat (calldataWord bytes (start + 160)).toNat),
          .address (AccountAddress.ofNat (calldataWord bytes (start + 192)).toNat),
          .address (AccountAddress.ofNat (calldataWord bytes (start + 224)).toNat)],
          max maxEnd (start + 256)) else none := by
  rw [decodeABIValues_word (by rfl) (by omega), decodeABIWord_u256]
  simp only [bind, Option.bind, Nat.reduceAdd]
  rw [decodeABIValues_word (by rfl) (by omega), decodeABIWord_u256]
  simp only [bind, Option.bind, Nat.reduceAdd]
  rw [decodeABIValues_word (by rfl) (by omega), decodeABIWord_address]
  by_cases he : (calldataWord bytes (start + 192)).toNat < EVM.addressModulus
  · simp only [he, if_true, bind, Option.bind, Nat.reduceAdd]
    rw [decodeABIValues_word (by rfl) (by omega), decodeABIWord_address]
    by_cases hl : (calldataWord bytes (start + 224)).toNat < EVM.addressModulus
    · simp only [hl, if_true, bind, Option.bind, decodeABIValues?, and_self]
      congr 2
      omega
    · simp [hl]
  · simp [he]

theorem decodeMarketData_eq {bytes : ByteArray} {start : Nat} :
    (decodeABIValue? Model.marketABI bytes.toList start).map Prod.fst =
      (decodeMarketData bytes start).map MarketData.value := by
  by_cases hlen : start + 256 ≤ bytes.size
  · rw [Model.marketABI, decodeABIValue?]
    rw [show abiTupleHeadSize? [Model.u256, Model.addr, Model.addr,
        .dynamicArray Model.collateralABI, Model.u256, Model.u256, Model.addr, Model.addr] =
        some 256 from by
      simp [abiTupleHeadSize?, Model.u256, Model.addr, isDynamicABIType, staticABIEncodedSize?]]
    simp only [bind, Option.bind]
    rw [decodeABIValues_word (by rfl) (by omega), decodeABIWord_u256]
    simp only [bind, Option.bind, Nat.reduceAdd, Nat.add_zero]
    rw [decodeABIValues_word (by rfl) (by omega), decodeABIWord_address]
    by_cases hm : (calldataWord bytes (start + 32)).toNat < EVM.addressModulus
    · simp only [hm, if_true, bind, Option.bind, Nat.reduceAdd]
      rw [decodeABIValues_word (by rfl) (by omega), decodeABIWord_address]
      by_cases hl : (calldataWord bytes (start + 64)).toNat < EVM.addressModulus
      · simp only [hl, if_true, bind, Option.bind, Nat.reduceAdd]
        rw [decodeABIValues?]
        simp only [isDynamicABIType, if_true, solcMaxLen_modern, Nat.reduceAdd]
        rw [readNat_bytes (off := start + 96) (by omega)]
        simp only [bind, Option.bind]
        by_cases ho : solcMaxU64 < (calldataWord bytes (start + 96)).toNat
        · simp [ho, decodeMarketData, MarketData.canonicalAt, hlen, hm, hl]
        · simp only [ho, if_false]
          rw [decodeCollateralArray]
          cases hn : readNat? bytes.toList (start + (calldataWord bytes (start + 96)).toNat) with
          | none => simp [hn, decodeMarketData, MarketData.canonicalAt, hlen, hm, hl, ho]
          | some n =>
            by_cases hcap : solcMaxU64 < n
            · simp [hn, hcap, decodeMarketData, MarketData.canonicalAt, hlen, hm, hl, ho]
            · simp only [bind, Option.bind, hcap, if_false]
              cases hc : decodeCollateralElements n bytes
                  (start + (calldataWord bytes (start + 96)).toNat + 32) with
              | none => simp [hc, hn, hcap, decodeMarketData, MarketData.canonicalAt, hlen, hm, hl, ho]
              | some collaterals =>
                simp only [bind, Option.bind]
                rw [decodeMarketTail hlen]
                by_cases ht : (calldataWord bytes (start + 192)).toNat < EVM.addressModulus ∧
                    (calldataWord bytes (start + 224)).toNat < EVM.addressModulus
                · simp [ht, hc, hn, hcap, decodeMarketData, MarketData.canonicalAt,
                    hlen, hm, hl, ho, MarketData.at, MarketData.value]
                · simp [ht, hc, hn, hcap, decodeMarketData, MarketData.canonicalAt,
                    hlen, hm, hl, ho]
      · simp [hl, decodeMarketData, MarketData.canonicalAt, hlen, hm]
    · simp [hm, decodeMarketData, MarketData.canonicalAt, hlen]
  · rw [decodeMarketHead_short (by
      simpa only [byteArray_toList_eq, Array.length_toList] using Nat.lt_of_not_ge hlen)]
    simp [decodeMarketData, hlen]

def decodeStoredMarketData (bytes : ByteArray) : Option MarketData := do
  let root ← readNat? bytes.toList 0
  if solcMaxU64 < root then none else decodeMarketData bytes root

theorem decodeStoredMarketData_eq {bytes : ByteArray} (hsmall : bytes.size < 2^255) :
    config.externalABI.decodeValue? Model.marketABI bytes =
      (decodeStoredMarketData bytes).map MarketData.value := by
  rw [decodeMarketRoot hsmall]
  simp only [decodeStoredMarketData]
  cases readNat? bytes.toList 0 with
  | none => rfl
  | some root =>
    simp only [bind, Option.bind]
    by_cases hcap : solcMaxU64 < root
    · simp only [hcap, if_true, Option.map_none]
    · simp only [hcap, if_false]
      have he := decodeMarketData_eq (bytes := bytes) (start := root)
      cases hd : decodeABIValue? Model.marketABI bytes.toList root <;>
        simpa only [hd, Option.map] using he

theorem decodeStoredMarketData_root {bytes : ByteArray}
    (hlen : 32 ≤ bytes.size) (hroot : (calldataWord bytes 0).toNat < 2^64) :
    decodeStoredMarketData bytes = decodeMarketData bytes (calldataWord bytes 0).toNat := by
  simp only [decodeStoredMarketData, readNat_bytes hlen, bind, Option.bind]
  rw [if_neg (by change ¬ 18446744073709551615 < _; omega)]

theorem decodeMarketData_success {bytes : ByteArray} {start : Nat} {market : MarketData}
    (h : decodeMarketData bytes start = some market) :
    start + 256 ≤ bytes.size ∧ MarketData.canonicalAt bytes start ∧
      (calldataWord bytes (start + 96)).toNat < 2^64 ∧
      start + (calldataWord bytes (start + 96)).toNat + 32 ≤ bytes.size ∧
      (calldataWord bytes (start + (calldataWord bytes (start + 96)).toNat)).toNat < 2^64 ∧
      ∃ values, decodeCollateralElements
        (calldataWord bytes (start + (calldataWord bytes (start + 96)).toNat)).toNat bytes
        (start + (calldataWord bytes (start + 96)).toNat + 32) = some values ∧
        market = MarketData.at bytes start values := by
  rw [decodeMarketData] at h
  split at h
  · cases h
  · rename_i hhead
    have hh := not_not.mp hhead
    dsimp only at h
    split at h
    · cases h
    · rename_i hoff
      rcases Option.bind_eq_some_iff.mp h with ⟨n, hn, h⟩
      split at h
      · cases h
      · rename_i hcap
        rcases Option.bind_eq_some_iff.mp h with ⟨values, hv, hm⟩
        have hlen := readNat?_some_length hn
        simp only [byteArray_toList_eq, Array.length_toList] at hlen
        rw [readNat_bytes hlen] at hn
        cases Option.some.inj hn
        refine ⟨hh.1, hh.2, ?_, hlen, ?_, values, hv, (Option.some.inj hm).symm⟩
        · change ¬ 18446744073709551615 < _ at hoff
          omega
        · change ¬ 18446744073709551615 < _ at hcap
          omega

theorem decodeMarketData_collateralCount {bytes : ByteArray} {start : Nat} {market : MarketData}
    (h : decodeMarketData bytes start = some market) :
    market.collaterals.length =
      (calldataWord bytes (start + (calldataWord bytes (start + 96)).toNat)).toNat := by
  rcases decodeMarketData_success h with ⟨_, _, _, _, _, values, hv, rfl⟩
  exact decodeCollateralElements_length hv

theorem decodeMarketData_of_elements {bytes : ByteArray} {start : Nat}
    {values : List CollateralData}
    (hhead : start + 256 ≤ bytes.size) (hcanon : MarketData.canonicalAt bytes start)
    (hoff : (calldataWord bytes (start + 96)).toNat < 2^64)
    (harray : start + (calldataWord bytes (start + 96)).toNat + 32 ≤ bytes.size)
    (hn : (calldataWord bytes (start + (calldataWord bytes (start + 96)).toNat)).toNat < 2^64)
    (hc : decodeCollateralElements
      (calldataWord bytes (start + (calldataWord bytes (start + 96)).toNat)).toNat bytes
      (start + (calldataWord bytes (start + 96)).toNat + 32) = some values) :
    decodeMarketData bytes start = some (MarketData.at bytes start values) := by
  have ho : ¬ solcMaxU64 < (calldataWord bytes (start + 96)).toNat := by
    change ¬ 18446744073709551615 < _; omega
  have hn' : ¬ solcMaxU64 <
      (calldataWord bytes (start + (calldataWord bytes (start + 96)).toNat)).toNat := by
    change ¬ 18446744073709551615 < _; omega
  simp only [decodeMarketData, not_and_or, not_le, not_lt_of_ge hhead, hcanon,
    not_true_eq_false, or_self, if_false, ho, readNat_bytes harray, bind, Option.bind,
    hn', hc, pure, Pure.pure]

end Benchmarks.Midnight
