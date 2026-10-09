import Benchmarks.CompoundIII.Comet.AccountMagnitude

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

-- GENERALIZES evalUint8And: typed unsigned AND at any width on canonical naturals.
theorem evalUintAndNat (width : BitWidth) (x y : Nat)
    (hx : x < 2^width.val) (hy : y < 2^width.val) :
    evalIntBitwise (.uint width) Nat.land (Int.ofNat x) (Int.ofNat y) =
      .int (Int.ofNat (Nat.land x y)) := by
  have hnorm (z : Nat) (hz : z < 2^width.val) :
      normalizeInt (.uint width) (Int.ofNat z) = Int.ofNat z :=
    normalizeInt_uint_eq_self _ _ (Int.natCast_nonneg _) (Int.ofNat_lt.mpr hz)
  unfold evalIntBitwise
  dsimp only [IntType.bitWidth]
  rw [hnorm x hx, hnorm y hy]
  exact congrArg Value.int (hnorm _ (lt_of_le_of_lt (nat_land_le_right _ _) hy))

-- LIBRARY CANDIDATE: a typed shift of one constructs a bit mask within the type width.
theorem evalUintBitMask {cfg frame evm bitExpr} (width : BitWidth) (bit : Nat)
    (hbit : bit < width.val)
    (he : evalExpr? cfg frame evm bitExpr = .ok (.int (Int.ofNat bit))) :
    evalExpr? cfg frame evm
      (.binary (.shl (.uint width)) (.cast (.intLit 1) (.elem (.int (.uint width)))) bitExpr) =
      .ok (.int (Int.ofNat (2^bit))) := by
  have hp : 2^bit < 2^width.val := Nat.pow_lt_pow_right (by decide) hbit
  have h1 : 1 < 2^width.val := lt_of_le_of_lt (Nat.one_le_pow _ _ (by decide)) hp
  have hc : evalExpr? cfg frame evm (.cast (.intLit 1) (.elem (.int (.uint width)))) =
      .ok (.int 1) := castUintSourceOk width (by simp only [evalExpr?, pure]; rfl) h1
  simp only [evalExpr?, hc, he, bind, EvalResult.bind, evalBinaryOp?, Int.ofNat_eq_natCast]
  rw [if_neg (not_lt.mpr (Int.natCast_nonneg bit))]
  change (if width.val ≤ bit then _ else _) = _
  rw [if_neg (by omega)]
  change EvalResult.ok (Value.int (normalizeInt (.uint width) (1 * Int.ofNat (2^bit)))) = _
  simp only [one_mul, Int.ofNat_eq_natCast]
  rw [normalizeInt_uint_eq_self width _ (Int.natCast_nonneg _)
    (Int.ofNat_lt.mpr hp)]

-- LIBRARY CANDIDATE: the EVM shift of one agrees with its natural-number bit mask.
theorem wordBitMask (bit : UInt256) (hb : bit.toNat < 256) :
    UInt256.shiftLeft (UInt256.ofNat 1) bit = UInt256.ofNat (2^bit.toNat) := by
  unfold UInt256.shiftLeft
  rw [if_neg (by change ¬ 256 ≤ bit.toNat; omega)]
  apply u256_inj
  change (1 <<< bit.toNat) % UInt256.size = 2^bit.toNat % UInt256.size
  rw [Nat.shiftLeft_eq, one_mul]

end Benchmarks.CompoundIII.Comet
