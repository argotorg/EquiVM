import Benchmarks.Midnight.CalldataBounds
import Benchmarks.Midnight.CollateralDecodeSlice

/-! The materialized collateral-array calldata decoder in typed form. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open ABI.Solc08Calldata

namespace Benchmarks.Midnight

theorem solcCollateralBadExtent {bytes : ByteArray} {start n : Nat}
    (hsize : bytes.size < 2^255) (hstart : start < 2^128) (hn : n < 2^64) :
    badExtent true false bytes.toList start n 128 =
      decide (bytes.size < start + 32 + 128 * n) := by
  have hl : bytes.toList.length = bytes.size := by
    simp only [byteArray_toList_eq, Array.length_toList]; rfl
  have ha : solcAdd start 31 = start + 31 := Nat.mod_eq_of_lt (by
    change start + 31 < 2^256; omega)
  have hb : solcAdd start 32 = start + 32 := Nat.mod_eq_of_lt (by
    change start + 32 < 2^256; omega)
  have hc : solcAdd (start + 32) (n * 128) = start + 32 + n * 128 :=
    Nat.mod_eq_of_lt (by change start + 32 + n * 128 < 2^256; omega)
  have hm : bytes.size % EVM.wordModulus = bytes.size := Nat.mod_eq_of_lt (by
    change bytes.size < 2^256; omega)
  simp only [badExtent, hl, Bool.not_false, Bool.true_and, Bool.false_and,
    Bool.false_eq_true, if_false, ha, hb, hc, hm,
    solcSLT_small (a := start + 31) (by omega) hsize]
  by_cases h : bytes.size < start + 32 + 128 * n
  · simp only [show bytes.size < start + 32 + n * 128 from by omega,
      h, decide_true, Bool.or_true]
  · simp only [show ¬ bytes.size < start + 32 + n * 128 from by omega,
      show start + 31 < bytes.size from by omega, h, decide_false, decide_true,
      Bool.not_true, Bool.false_or]

theorem solcCollateralArrayValue {bytes : ByteArray} {start : Nat}
    (hsize : bytes.size < 2^255) (hstart : start < 2^128) :
    decodeValue? (.dynamicArray Model.collateralABI) bytes.toList start {} = (do
      let n ← readNat? bytes.toList start
      if solcMaxU64 < n then none else
        let values ← decodeCollateralElements n bytes (start + 32)
        pure (.array (values.map CollateralData.value))) := by
  have hl : bytes.toList.length = bytes.size := by
    simp only [byteArray_toList_eq, Array.length_toList]; rfl
  have hmod : bytes.size < EVM.wordModulus := by change bytes.size < 2^256; omega
  rw [decodeValue?]
  simp only [stride?, show isDynamicABIType Model.collateralABI = false from rfl,
    Bool.false_eq_true, if_false, collateralABI_staticSize, bind, Option.bind]
  by_cases hhead : start + 32 ≤ bytes.size
  · rw [readNat_bytes hhead, solcReadNat_bounded hhead hmod]
    simp only [bind, Option.bind]
    by_cases hn : solcMaxU64 < (calldataWord bytes start).toNat
    · simp only [hn, decide_true, Bool.true_or, if_true]
    · have hcap : (calldataWord bytes start).toNat < 2^64 := by
        change ¬ (2^64 - 1 < _) at hn
        omega
      simp only [hn, decide_false, Bool.false_or, if_false,
        show isMemory ({} : CalldataPlan) = true from rfl,
        solcCollateralBadExtent hsize hstart hcap]
      by_cases he : start + 32 + 128 * (calldataWord bytes start).toNat ≤ bytes.size
      · simp only [show ¬ bytes.size < start + 32 + 128 * (calldataWord bytes start).toNat
          from by omega, decide_false, Bool.false_eq_true, if_false]
        have ha : solcAdd start 32 = start + 32 := Nat.mod_eq_of_lt (by
          change start + 32 < 2^256; omega)
        simp only [show (child ({} : CalldataPlan) .element).deferErrors.isEmpty = true from rfl,
          Bool.not_false, Bool.true_and, if_true, ha,
          show (calldataWord bytes start).toNat * 128 / 32 =
            4 * (calldataWord bytes start).toNat by omega]
        rw [decodeCollateralWords he hmod]
        cases decodeCollateralElements (calldataWord bytes start).toNat bytes (start + 32) <;> rfl
      · have hp : 0 < (calldataWord bytes start).toNat := by omega
        rw [decodeCollateralElements_short hp (by omega)]
        simp only [show bytes.size < start + 32 + 128 * (calldataWord bytes start).toNat
          from by omega, decide_true, if_true, bind, Option.bind]
  · have hs : readNat? bytes.toList start = none := readNat_bytes_short (by omega)
    rw [hs]
    simp only [bind, Option.bind]
    have ha : solcAdd start 31 = start + 31 := Nat.mod_eq_of_lt (by
      change start + 31 < 2^256; omega)
    have hb : badExtent (isMemory {}) false bytes.toList start
        (solcReadNat bytes.toList start) 128 = true := by
      simp only [badExtent, Bool.not_false, Bool.true_and, ha, hl,
        solcSLT_small (a := start + 31) (by omega) hsize,
        show ¬ start + 31 < bytes.size from by omega,
        decide_false, Bool.not_false, Bool.true_or]
    simp only [hb, Bool.or_true, if_true]

end Benchmarks.Midnight
