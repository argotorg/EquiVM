import Benchmarks.Midnight.MarketCalldataFields

/-! The market calldata decoder agrees with the typed market representation. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open ABI.Solc08Calldata

namespace Benchmarks.Midnight

theorem solcMarketValue_eq {bytes : ByteArray} {start : Nat}
    (hsize : bytes.size < 2^255) (hstart : start < 2^127) :
    decodeValue? Model.marketABI bytes.toList start {} =
      (decodeMarketData bytes start).map MarketData.value := by
  have hl : bytes.toList.length = bytes.size := by
    simp only [byteArray_toList_eq, Array.length_toList]; rfl
  have hmod : bytes.size < EVM.wordModulus := by change bytes.size < 2^256; omega
  rw [solcMarketValue_shape]
  rw [hl, solcSLT_sub_small hsize (by omega) (by norm_num)]
  by_cases hlen : start + 256 ≤ bytes.size
  · simp only [show ¬ bytes.size < start + 256 from by omega, decide_false,
      Bool.false_eq_true, if_false]
    rw [solcDecodeFields_word Model.u256 (base := start) (cursor := 0)
      (plans := [{}, {}, {}, {}, {}, {}, {}, {}]) rfl rfl (by omega) hmod,
      decodeABIWord_u256]
    simp only [bind, Option.bind, Nat.reduceAdd, Nat.add_zero, List.tail_cons]
    rw [solcDecodeFields_word Model.addr (base := start) (cursor := 32)
      (plans := [{}, {}, {}, {}, {}, {}, {}]) rfl rfl (by omega) hmod,
      decodeABIWord_address]
    by_cases hm : (calldataWord bytes (start + 32)).toNat < EVM.addressModulus
    · simp only [hm, if_true, bind, Option.bind, Nat.reduceAdd, List.tail_cons]
      rw [solcDecodeFields_word Model.addr (base := start) (cursor := 64)
        (plans := [{}, {}, {}, {}, {}, {}]) rfl rfl (by omega) hmod,
        decodeABIWord_address]
      by_cases ht : (calldataWord bytes (start + 64)).toNat < EVM.addressModulus
      · simp only [ht, if_true, bind, Option.bind, Nat.reduceAdd, List.tail_cons]
        rw [decodeFields?]
        have ha : solcAdd start 96 = start + 96 := Nat.mod_eq_of_lt (by
          change start + 96 < 2^256; omega)
        simp only [isDynamicABIType, stride?, if_true, bind, Option.bind, List.headD_cons,
          List.tail_cons, Bool.not_true, solcTailTarget?, Bool.false_eq_true, if_false, ha,
          solcReadNat_bounded (start := start + 96) (by omega) hmod]
        by_cases ho : solcMaxU64 < (calldataWord bytes (start + 96)).toNat
        · simp [ho, retainFailure, decodeMarketData, MarketData.canonicalAt, hlen, hm, ht]
        · have hb : solcAdd start (calldataWord bytes (start + 96)).toNat =
              start + (calldataWord bytes (start + 96)).toNat := Nat.mod_eq_of_lt (by
            change start + (calldataWord bytes (start + 96)).toNat < 2^256
            change ¬ (2^64 - 1 < _) at ho
            omega)
          simp only [ho, if_false, bind, Option.bind, hb, Bool.and_false]
          rw [solcCollateralArrayValue hsize (by
            change ¬ (2^64 - 1 < _) at ho
            omega)]
          simp only [Nat.reduceAdd]
          rw [solcDecodeMarketTail hlen hmod]
          cases hn : readNat? bytes.toList (start + (calldataWord bytes (start + 96)).toNat) with
          | none => simp [hn, retainFailure, decodeMarketData, MarketData.canonicalAt, hlen, hm, ht, ho]
          | some n =>
            by_cases hcap : solcMaxU64 < n
            · simp [hn, hcap, retainFailure, decodeMarketData, MarketData.canonicalAt, hlen, hm, ht, ho]
            · cases hc : decodeCollateralElements n bytes
                (start + (calldataWord bytes (start + 96)).toNat + 32) with
              | none => simp [hc, hn, hcap, retainFailure, decodeMarketData, MarketData.canonicalAt,
                  hlen, hm, ht, ho]
              | some cs =>
                by_cases hlast : (calldataWord bytes (start + 192)).toNat < EVM.addressModulus ∧
                    (calldataWord bytes (start + 224)).toNat < EVM.addressModulus
                · simp [hlast, hc, hn, hcap, retainFailure, decodeMarketData, MarketData.canonicalAt,
                    hlen, hm, ht, ho, MarketData.at, MarketData.value]
                · simp [hlast, hc, hn, hcap, retainFailure, decodeMarketData, MarketData.canonicalAt,
                    hlen, hm, ht, ho]
      · simp [ht, decodeMarketData, MarketData.canonicalAt, hlen, hm]
    · simp [hm, decodeMarketData, MarketData.canonicalAt, hlen]
  · simp [show bytes.size < start + 256 from by omega, decodeMarketData, hlen]

end Benchmarks.Midnight
