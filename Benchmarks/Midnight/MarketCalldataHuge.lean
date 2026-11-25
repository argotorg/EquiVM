import Benchmarks.Midnight.MarketCalldataFields

/-! Signed calldata-end guards reject high-bit-set lengths in materialized markets. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open ABI.Solc08Calldata

namespace Benchmarks.Midnight

theorem solcCollateralArrayValue_huge {bytes : ByteArray} {start : Nat}
    (hhigh : 2^255 ≤ bytes.size) (hsize : bytes.size < UInt256.size)
    (hstart : start < 2^128) :
    decodeValue? (.dynamicArray Model.collateralABI) bytes.toList start {} = none := by
  have hl : bytes.toList.length = bytes.size := by
    simp only [byteArray_toList_eq, Array.length_toList]; rfl
  have ha : solcAdd start 31 = start + 31 := Nat.mod_eq_of_lt (by
    change start + 31 < 2^256; omega)
  have hb : badExtent (isMemory {}) false bytes.toList start
      (solcReadNat bytes.toList start) 128 = true := by
    simp only [badExtent, Bool.not_false, Bool.true_and, ha, hl,
      solcSLT_low_high (a := start + 31) (by omega) hhigh hsize, Bool.not_false,
      Bool.true_or]
  rw [decodeValue?]
  simp only [stride?, show isDynamicABIType Model.collateralABI = false from rfl,
    Bool.false_eq_true, if_false, collateralABI_staticSize, bind, Option.bind,
    hb, Bool.or_true, if_true]

theorem solcMarketValue_huge {bytes : ByteArray} {start : Nat}
    (hhigh : 2^255 ≤ bytes.size) (hsize : bytes.size < UInt256.size)
    (hstart : start < 2^127) :
    decodeValue? Model.marketABI bytes.toList start {} = none := by
  have hlen : start + 256 ≤ bytes.size := by omega
  have hmod : bytes.size < EVM.wordModulus := hsize
  rw [solcMarketValue_shape]
  split
  · rfl
  · rw [solcDecodeFields_word Model.u256 (base := start) (cursor := 0)
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
        rw [solcDecodeFields_dynamic (.dynamicArray Model.collateralABI)
          (base := start) (cursor := 96) (plans := [{}, {}, {}, {}, {}])
          rfl rfl (by omega) hmod (by change start + 2^64 < 2^256; omega)]
        by_cases hc : solcMaxU64 < (calldataWord bytes (start + 96)).toNat
        · simp only [hc, if_true, bind, Option.bind]
        · rw [if_neg hc, solcCollateralArrayValue_huge hhigh hsize (by
            change ¬ (2^64 - 1 < _) at hc
            omega)]
          rfl
      · simp only [ht, if_false, bind, Option.bind]
    · simp only [hm, if_false, bind, Option.bind]

end Benchmarks.Midnight
