import Benchmarks.UniswapV4PoolManager.WordSignedRepresentation

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: unsigned casts of signed words retain their low field bits.
theorem normalizeUintSignedWord (bits : BitWidth) (w mask : UInt256) (hm : mask.toNat = 2^bits.val-1) :
    normalizeInt (.uint bits) (EVM.signed w) = Int.ofNat (UInt256.land w mask).toNat := by
  have he : EVM.signed w % (2^256 : Int) = Int.ofNat w.toNat := normalizeUnsignedSigned w
  calc
    normalizeInt (.uint bits) (EVM.signed w) = EVM.signed w % (2 : Int)^bits.val := by
      simp only [normalizeInt, EVM.twoPow, Int.ofNat_eq_natCast, Int.natCast_pow, Int.cast_ofNat_Int]
    _ = (EVM.signed w % (2^256 : Int)) % (2 : Int)^bits.val :=
      (Int.emod_emod_of_dvd _ (pow_dvd_pow (2 : Int) bits.property.2.1)).symm
    _ = normalizeInt (.uint bits) (Int.ofNat w.toNat) := by
      rw [he]
      simp only [normalizeInt, EVM.twoPow, Int.ofNat_eq_natCast, Int.natCast_pow, Int.cast_ofNat_Int]
    _ = Int.ofNat (UInt256.land w mask).toNat := normalizeUintWord bits w mask hm

-- LIBRARY CANDIDATE: wrapping signed multiplication in arbitrary expression contexts.
theorem evalSignedWordMul {cfg : Config} {f : Frame} {evm : EVM.State} {a b : Expr} {x y : UInt256}
    (hx : evalExpr? cfg f evm a = .ok (.int (EVM.signed x)))
    (hy : evalExpr? cfg f evm b = .ok (.int (EVM.signed y))) :
    evalExpr? cfg f evm (.cast (.binary .mul a b) (.elem (.int (.sint ⟨256, by decide⟩)))) =
      .ok (.int (EVM.signed (UInt256.mul x y))) := by
  have he : evalExpr? cfg f evm (.binary .mul a b) = .ok (.int (EVM.signed x * EVM.signed y)) := by
    rw [evalExpr_binary_nonshort (by decide) (by decide), hx, hy]
    rfl
  have hc := evalExpr_cast_int (intType := .sint ⟨256, by decide⟩) he
  simpa only [normalizeSignedWordOfInt, wordOfInt_signed_mul] using hc

-- LIBRARY CANDIDATE: wrapping signed addition in arbitrary expression contexts.
theorem evalSignedWordAdd {cfg : Config} {f : Frame} {evm : EVM.State} {a b : Expr} {x y : UInt256}
    (hx : evalExpr? cfg f evm a = .ok (.int (EVM.signed x)))
    (hy : evalExpr? cfg f evm b = .ok (.int (EVM.signed y))) :
    evalExpr? cfg f evm (.cast (.binary .add a b) (.elem (.int (.sint ⟨256, by decide⟩)))) =
      .ok (.int (EVM.signed (x + y))) := by
  have he : evalExpr? cfg f evm (.binary .add a b) = .ok (.int (EVM.signed x + EVM.signed y)) := by
    rw [evalExpr_binary_nonshort (by decide) (by decide), hx, hy]
    rfl
  have hc := evalExpr_cast_int (intType := .sint ⟨256, by decide⟩) he
  simpa only [normalizeSignedWordOfInt, wordOfInt_signed_add] using hc

-- LIBRARY CANDIDATE: wrapping signed subtraction in arbitrary expression contexts.
theorem evalSignedWordSub {cfg : Config} {f : Frame} {evm : EVM.State} {a b : Expr} {x y : UInt256}
    (hx : evalExpr? cfg f evm a = .ok (.int (EVM.signed x)))
    (hy : evalExpr? cfg f evm b = .ok (.int (EVM.signed y))) :
    evalExpr? cfg f evm (.cast (.binary .sub a b) (.elem (.int (.sint ⟨256, by decide⟩)))) =
      .ok (.int (EVM.signed (UInt256.sub x y))) := by
  have he : evalExpr? cfg f evm (.binary .sub a b) = .ok (.int (EVM.signed x - EVM.signed y)) := by
    rw [evalExpr_binary_nonshort (by decide) (by decide), hx, hy]
    rfl
  have hc := evalExpr_cast_int (intType := .sint ⟨256, by decide⟩) he
  simpa only [normalizeSignedWordOfInt, wordOfInt_signed_sub] using hc

-- LIBRARY CANDIDATE: signed left shift, including negative inputs.
theorem evalSignedWordShl {cfg : Config} {f : Frame} {evm : EVM.State} {a b : Expr} {x : UInt256} {n : Nat}
    (hn : n < 256) (hx : evalExpr? cfg f evm a = .ok (.int (EVM.signed x)))
    (hy : evalExpr? cfg f evm b = .ok (.int (Int.ofNat n))) :
    evalExpr? cfg f evm (.binary (.shl (.sint ⟨256, by decide⟩)) a b) =
      .ok (.int (EVM.signed (UInt256.shiftLeft x (UInt256.ofNat n)))) := by
  rw [evalExpr_binary_nonshort (by decide) (by decide), hx, hy]
  simp only [bind, EvalResult.bind, evalBinaryOp?, IntType.bitWidth, Int.ofNat_eq_natCast,
    Int.not_lt.mpr (Int.natCast_nonneg n), if_false, Int.toNat_natCast, Nat.not_le.mpr hn]
  change EvalResult.ok (Value.int (normalizeInt (.sint ⟨256, by decide⟩)
    (EVM.signed x * Int.ofNat (2^n)))) = _
  rw [normalizeSignedWordOfInt, wordOfInt_signed_shl x hn]

end Benchmarks.UniswapV4PoolManager
