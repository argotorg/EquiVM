import Benchmarks.CompoundIII.Comet.CollateralLoopModel
import Benchmarks.CompoundIII.Comet.SignedDebtWords
import Benchmarks.CompoundIII.Comet.BoolWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

-- LIBRARY CANDIDATE: increment a canonical uint8 without truncation when it remains in range.
theorem uint8IncrementWord (i : Nat) (hi : i + 1 < 256) :
    UInt256.land (⟨255⟩ : UInt256) ((UInt256.ofNat 1) + UInt256.ofNat i) =
      UInt256.ofNat (i + 1) := by
  rw [show UInt256.ofNat 1 + UInt256.ofNat i = UInt256.ofNat (i + 1) from
    uInt256_one_add_ofNat_of_lt (by change i + 1 < 2^256; omega), u256_land_comm]
  apply lowByteClean
  rwa [UInt256.toNat_ofNat_of_lt (by change i + 1 < 2^256; omega)]

-- LIBRARY CANDIDATE: the two canonical signed-zero comparison words.
theorem signedSltZeroWord (w : UInt256) :
    UInt256.slt w ⟨0⟩ = boolWord (decide (signedWord w < 0)) := by
  rw [signedWord_slt]
  rfl

theorem signedNonnegWord (w : UInt256) :
    UInt256.isZero (UInt256.slt w ⟨0⟩) = boolWord (decide (0 ≤ signedWord w)) := by
  rw [signedSltZeroWord]
  by_cases h : 0 ≤ signedWord w
  · rw [decide_eq_true h, decide_eq_false (by omega)]
    rfl
  · rw [decide_eq_false h, decide_eq_true (by omega)]
    rfl

theorem collateralSum_bounds {liquidity value : UInt256}
    (hl : signedWord liquidity < 0) (hv : value.toNat < 2^255) :
    -(2^255 : Int) ≤ signedWord liquidity + Int.ofNat value.toNat ∧
      signedWord liquidity + Int.ofNat value.toNat < (2^255 : Int) := by
  have hb := signedWord_bounds liquidity
  simp only [Int.ofNat_eq_natCast]
  omega

end Benchmarks.CompoundIII.Comet
