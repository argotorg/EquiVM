import Benchmarks.Midnight.Common

/-! Signed ABI bounds checks on ordinary bounded memory addresses. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

-- LIBRARY CANDIDATE: signed subtraction also rejects a head beyond the buffer's end.
theorem signedDecodeCheck {finish start : UInt256} {need : Nat}
    (he : finish.toNat < 2^255) (hs : start.toNat < 2^255) (hn : need < 2^255) :
    UInt256.slt (UInt256.sub finish start) (UInt256.ofNat need) =
      UInt256.fromBool (decide (finish.toNat < start.toNat + need)) := by
  have hn' : need < 2^255 := by omega
  by_cases hle : start.toNat ≤ finish.toNat
  · have hd := usub_toNat hle
    by_cases hshort : finish.toNat < start.toNat + need
    · rw [decide_eq_true hshort]
      exact slt_lit_one_low hn' (by rw [hd]; omega)
    · rw [decide_eq_false hshort]
      exact slt_lit_zero hn' (by rw [hd]; omega) (by rw [hd]; omega)
  · rw [decide_eq_true (by omega)]
    exact slt_lit_one_high hn' (by
      rw [usub_toNat_underflow (by omega)]
      change 2^255 ≤ 2^256 + finish.toNat - start.toNat
      omega)

theorem memoryDecodeCheck {finish start : UInt256} {need : Nat}
    (he : finish.toNat < 2^128) (hs : start.toNat < 2^128) (hn : need < 2^128) :
    UInt256.slt (UInt256.sub finish start) (UInt256.ofNat need) =
      UInt256.fromBool (decide (finish.toNat < start.toNat + need)) :=
  signedDecodeCheck (by omega) (by omega) (by omega)

end Benchmarks.Midnight
