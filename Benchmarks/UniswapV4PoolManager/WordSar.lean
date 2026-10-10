import Benchmarks.UniswapV4PoolManager.WordAbsolute
import Benchmarks.UniswapV4PoolManager.WordSignedSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

-- LIBRARY CANDIDATE: a negative word is the negative successor of its complemented value.
theorem signedNegativeComplement (w : UInt256) (hw : 2^255 ≤ w.toNat) :
    EVM.signed w = Int.negSucc (UInt256.complement w).toNat := by
  have hlt : w.toNat < 2^256 := w.val.isLt
  change (if w.toNat < 2^255 then (w.toNat : Int) else (w.toNat : Int)-2^256) = _
  rw [if_neg (by omega), wordComplementNat]
  simp only [Int.negSucc_eq]
  omega

-- LIBRARY CANDIDATE: complementing a nonnegative signed word gives its negative successor.
theorem signedComplementSmall (w : UInt256) (hw : w.toNat < 2^255) :
    EVM.signed (UInt256.complement w) = Int.negSucc w.toNat := by
  change (if (UInt256.complement w).toNat < 2^255 then ((UInt256.complement w).toNat : Int)
    else ((UInt256.complement w).toNat : Int)-2^256) = _
  rw [wordComplementNat, if_neg (by omega)]
  simp only [Int.negSucc_eq]
  omega

-- LIBRARY CANDIDATE: signed division by a positive power of two is EVM SAR.
theorem wordSarSigned (w : UInt256) {n : Nat} (hn : n < 256) :
    EVM.signed (UInt256.sar (UInt256.ofNat n) w) = EVM.signed w / Int.ofNat (2^n) := by
  rw [UInt256.sar, wordSltZeroBool]
  by_cases hh : 2^255 ≤ w.toNat
  · simp only [hh, decide_true, if_true]
    change EVM.signed (UInt256.complement (UInt256.shiftRight (UInt256.complement w) (UInt256.ofNat n))) = _
    have hs : (UInt256.shiftRight (UInt256.complement w) (UInt256.ofNat n)).toNat < 2^255 := by
      rw [wordShiftRightNat _ hn, wordComplementNat]
      exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
    rw [signedComplementSmall _ hs, signedNegativeComplement w hh, wordShiftRightNat _ hn]
    have hp : (0 : Int) < Int.ofNat (2^n) := Int.natCast_pos.mpr (Nat.pow_pos (by decide))
    rw [Int.negSucc_ediv _ hp]
    simp only [Int.negSucc_eq, Int.ofNat_eq_natCast, Int.natCast_ediv]
    rfl
  · simp only [hh, decide_false, Bool.false_eq_true, if_false]
    change EVM.signed (UInt256.shiftRight w (UInt256.ofNat n)) = _
    have hs : (UInt256.shiftRight w (UInt256.ofNat n)).toNat < 2^255 := by
      rw [wordShiftRightNat _ hn]
      exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
    rw [signed_eq_normalize, normalizeInt_sint256_word_of_lt _ hs,
      signed_eq_normalize w, normalizeInt_sint256_word_of_lt _ (by change w.toNat < 2^255; omega), wordShiftRightNat _ hn]
    simp only [Int.ofNat_eq_natCast, Int.natCast_ediv]

-- LIBRARY CANDIDATE: signed right shift in arbitrary source expression contexts.
theorem evalSignedWordSar {cfg : Config} {f : Frame} {evm : EVM.State} {a b : Expr} {x : UInt256} {n : Nat}
    (hn : n < 256) (hx : evalExpr? cfg f evm a = .ok (.int (EVM.signed x)))
    (hy : evalExpr? cfg f evm b = .ok (.int (Int.ofNat n))) :
    evalExpr? cfg f evm (.binary (.shr (.sint ⟨256, by decide⟩)) a b) =
      .ok (.int (EVM.signed (UInt256.sar (UInt256.ofNat n) x))) := by
  rw [evalExpr_binary_nonshort (by decide) (by decide), hx, hy]
  have hc : normalizeInt (.sint ⟨256, by decide⟩) (EVM.signed x) = EVM.signed x := by
    rw [normalizeSignedWordOfInt, wordOfInt_signed]
  simp only [bind, EvalResult.bind, evalBinaryOp?, IntType.bitWidth, hc, Int.ofNat_eq_natCast,
    Int.not_lt.mpr (Int.natCast_nonneg n), if_false, Int.toNat_natCast, Nat.not_le.mpr hn]
  rw [wordSarSigned x hn]
  rfl

end Benchmarks.UniswapV4PoolManager
