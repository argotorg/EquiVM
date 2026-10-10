import Benchmarks.UniswapV4PoolManager.WordOperationsSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: the magnitude of a signed word always fits in an unsigned word.
theorem signedNatAbs_lt_size (w : UInt256) : (EVM.signed w).natAbs < 2^256 := by
  have hw : w.toNat < 2^256 := w.val.isLt
  change (if w.toNat < 2^255 then (w.toNat : Int) else (w.toNat : Int)-2^256).natAbs < _
  split
  · change w.toNat < 2^256
    exact hw
  · have hn := Int.ofNat_natAbs_of_nonpos (a := (w.toNat : Int)-2^256) (by omega)
    omega

-- LIBRARY CANDIDATE: the unsigned value of the EVM word complement.
theorem wordComplementNat (w : UInt256) :
    (UInt256.complement w).toNat = 2^256 - 1 - w.toNat := by
  have hw : w.toNat < 2^256 := w.val.isLt
  change ((0 : Fin UInt256.size) - (w.val + 1)).val = _
  rw [Fin.val_sub, Fin.val_add]
  change (2^256 + 0 - ((w.toNat + 1) % 2^256)) % 2^256 = _
  omega

-- LIBRARY CANDIDATE: XOR with the full word mask is the unsigned complement.
theorem wordXorAllOnesNat (w : UInt256) :
    (UInt256.xor w (UInt256.ofNat (2^256-1))).toNat = 2^256-1-w.toNat := by
  have h := congrArg BitVec.toNat (BitVec.xor_allOnes (x := (BitVec.ofFin w.val : BitVec 256)))
  simp only [BitVec.toNat_xor, BitVec.toNat_allOnes, BitVec.toNat_not, BitVec.toNat_ofFin] at h
  change w.toNat ^^^ (2^256-1) = 2^256-1-w.toNat at h
  change (w.toNat ^^^ (2^256-1)) % 2^256 = _
  rw [h, Nat.mod_eq_of_lt (by omega)]

-- LIBRARY CANDIDATE: the signed zero comparison tests the high bit.
theorem wordSltZeroBool (w : UInt256) : UInt256.sltBool w ⟨0⟩ = decide (2^255 ≤ w.toNat) := by
  unfold UInt256.sltBool
  change (if w.toNat ≥ 2^255 then if 0 ≥ 2^255 then decide (w.toNat < 0) else true
    else if 0 ≥ 2^255 then false else decide (w.toNat < 0)) = _
  simp only [show ¬ (0 : Nat) ≥ 2^255 by decide, if_false, Nat.not_lt_zero, decide_false]
  split <;> simp_all only [decide_true, decide_false]

-- LIBRARY CANDIDATE: SAR by 255 extracts the signed word mask.
theorem wordSarSignMask (w : UInt256) :
    UInt256.sar (UInt256.ofNat 255) w =
      if 2^255 ≤ w.toNat then UInt256.ofNat (2^256-1) else ⟨0⟩ := by
  rw [UInt256.sar, wordSltZeroBool]
  by_cases hh : 2^255 ≤ w.toNat
  · simp only [hh, decide_true, if_true]
    have hz : UInt256.shiftRight (UInt256.complement w) (UInt256.ofNat 255) = ⟨0⟩ := by
      apply u256_inj
      rw [wordShiftRightNat _ (by decide), wordComplementNat]
      change (2^256-1-w.toNat) / 2^255 = 0
      omega
    change UInt256.complement (UInt256.shiftRight (UInt256.complement w) (UInt256.ofNat 255)) = _
    rw [hz]
    rfl
  · simp only [hh, decide_false, Bool.false_eq_true, if_false]
    apply u256_inj
    change (UInt256.shiftRight w (UInt256.ofNat 255)).toNat = 0
    rw [wordShiftRightNat _ (by decide)]
    change w.toNat / 2^255 = 0
    omega

-- LIBRARY CANDIDATE: the standard SAR/ADD/XOR absolute-value idiom.
theorem wordAbsolute (w : UInt256) :
    UInt256.xor (UInt256.sar (UInt256.ofNat 255) w + w) (UInt256.sar (UInt256.ofNat 255) w) =
      UInt256.ofNat (EVM.signed w).natAbs := by
  have hw : w.toNat < 2^256 := w.val.isLt
  rw [wordSarSignMask]
  by_cases hh : 2^255 ≤ w.toNat
  · rw [if_pos hh]
    apply u256_inj
    rw [wordXorAllOnesNat, uadd_toNat]
    have ha : (EVM.signed w).natAbs = 2^256-w.toNat := by
      change (if w.toNat < 2^255 then (w.toNat : Int) else (w.toNat : Int)-2^256).natAbs = _
      rw [if_neg (by omega)]
      have hn := Int.ofNat_natAbs_of_nonpos
        (a := (w.toNat : Int)-2^256) (by omega)
      omega
    rw [ha]
    change 2^256-1-((2^256-1+w.toNat)%2^256) = (2^256-w.toNat)%2^256
    omega
  · rw [if_neg hh, u256_zero_add]
    have ha : (EVM.signed w).natAbs = w.toNat := by
      change (if w.toNat < 2^255 then (w.toNat : Int) else (w.toNat : Int)-2^256).natAbs = _
      rw [if_pos (by omega)]
      rfl
    rw [ha, u256_ofNat_toNat]
    apply u256_inj
    change (w.toNat ^^^ 0) % 2^256 = w.toNat
    rw [Nat.xor_zero, Nat.mod_eq_of_lt hw]

end Benchmarks.UniswapV4PoolManager
