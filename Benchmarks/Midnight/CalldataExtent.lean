import Benchmarks.Midnight.CalldataBounds

/-! Natural-number bounds for a materialized ABI tail with bounded element stride. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open ABI.Solc08Calldata

namespace Benchmarks.Midnight

-- LIBRARY CANDIDATE: generalizes solcCollateralBadExtent to any stride at most 128.
theorem solcMaterializedBadExtent {bytes : ByteArray} {start n stride : Nat}
    (hsize : bytes.size < 2^255) (hstart : start < 2^128) (hn : n < 2^64)
    (hstride : stride ≤ 128) :
    badExtent true false bytes.toList start n stride =
      decide (bytes.size < start + 32 + stride * n) := by
  have hmul : n * stride ≤ 128 * n := by
    simpa only [Nat.mul_comm] using Nat.mul_le_mul_left n hstride
  have hl : bytes.toList.length = bytes.size := by
    simp only [byteArray_toList_eq, Array.length_toList]; rfl
  have ha : solcAdd start 31 = start + 31 := Nat.mod_eq_of_lt (by
    change start + 31 < 2^256; omega)
  have hb : solcAdd start 32 = start + 32 := Nat.mod_eq_of_lt (by
    change start + 32 < 2^256; omega)
  have hc : solcAdd (start + 32) (stride * n) = start + 32 + stride * n :=
    Nat.mod_eq_of_lt (by
      change start + 32 + stride * n < 2^256
      rw [Nat.mul_comm stride n]
      omega)
  have hm : bytes.size % EVM.wordModulus = bytes.size := Nat.mod_eq_of_lt (by
    change bytes.size < 2^256; omega)
  simp only [badExtent, hl, Bool.not_false, Bool.true_and, Bool.false_and,
    Bool.false_eq_true, if_false, ha, hb, hc, hm,
    solcSLT_small (a := start + 31) (by omega) hsize, Nat.mul_comm n stride]
  by_cases h : bytes.size < start + 32 + stride * n
  · simp only [h, decide_true, Bool.or_true]
  · simp only [h, decide_false, show start + 31 < bytes.size from by omega,
      decide_true, Bool.not_true, Bool.false_or]

theorem solcMaterializedHead_reject {bytes : ByteArray} {start : Nat}
    (hsize : bytes.size < UInt256.size) (hstart : start < 2^128)
    (hbad : ¬ (bytes.size < 2^255 ∧ start + 32 ≤ bytes.size)) (n stride : Nat) :
    badExtent true false bytes.toList start n stride = true := by
  have hl : bytes.toList.length = bytes.size := by
    simp only [byteArray_toList_eq, Array.length_toList]; rfl
  have ha : solcAdd start 31 = start + 31 := Nat.mod_eq_of_lt (by
    change start + 31 < 2^256; omega)
  have hc : solcSLT (start + 31) bytes.size = false := by
    by_cases hs : bytes.size < 2^255
    · rw [solcSLT_small (by omega) hs, decide_eq_false (by omega)]
    · exact solcSLT_low_high (by omega) (by omega) hsize
  simp only [badExtent, Bool.not_false, Bool.true_and, ha, hl, hc,
    Bool.not_false, Bool.true_or]

end Benchmarks.Midnight
