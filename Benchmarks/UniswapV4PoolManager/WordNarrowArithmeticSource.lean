import Benchmarks.UniswapV4PoolManager.WordSignedCast

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: a narrow unsigned cast can be taken from the integer's EVM word encoding.
theorem normalizeUintInteger (bits : BitWidth) (n : Int) (mask : UInt256)
    (hm : mask.toNat = 2^bits.val-1) :
    normalizeInt (.uint bits) n = Int.ofNat (UInt256.land (EVM.wordOfInt n) mask).toNat := by
  rw [← normalizeUintWord bits (EVM.wordOfInt n) mask hm, wordOfIntResidue]
  change n % Int.ofNat (2^bits.val) = (n % (2^256 : Int)) % Int.ofNat (2^bits.val)
  apply (Int.emod_emod_of_dvd _ _).symm
  simpa only [Int.ofNat_eq_natCast, Int.natCast_pow, Int.cast_ofNat_Int] using
    pow_dvd_pow (2 : Int) bits.property.2.1

-- GENERALIZES evalWordSub to arbitrary unsigned cast widths.
theorem evalUintWordSubWidth {cfg : Config} {f : Frame} {evm : EVM.State}
    {a b : Expr} {x y : UInt256} (bits : BitWidth) (mask : UInt256)
    (hm : mask.toNat = 2^bits.val-1)
    (hx : evalExpr? cfg f evm a = .ok (.int (Int.ofNat x.toNat)))
    (hy : evalExpr? cfg f evm b = .ok (.int (Int.ofNat y.toNat))) :
    evalExpr? cfg f evm (.cast (.binary .sub a b) (.elem (.int (.uint bits)))) =
      .ok (.int (Int.ofNat (UInt256.land (UInt256.sub x y) mask).toNat)) := by
  have he : evalExpr? cfg f evm (.binary .sub a b) = .ok (.int (Int.ofNat x.toNat - Int.ofNat y.toNat)) := by
    rw [evalExpr_binary_nonshort (by decide) (by decide), hx, hy]
    rfl
  have hc := evalExpr_cast_int (intType := .uint bits) he
  simpa only [normalizeUintInteger bits _ mask hm, wordOfInt_sub_natCasts] using hc

-- LIBRARY CANDIDATE: int24 addition followed by truncation agrees with the word operation.
theorem evalSigned24Add {cfg : Config} {f : Frame} {evm : EVM.State} {a b : Expr} {x y : UInt256}
    (hx : evalExpr? cfg f evm a = .ok (.int (EVM.signed x)))
    (hy : evalExpr? cfg f evm b = .ok (.int (EVM.signed y))) :
    evalExpr? cfg f evm (.cast (.binary .add a b) (.elem (.int (.sint ⟨24, by decide⟩)))) =
      .ok (.int (EVM.signed (UInt256.signextend (UInt256.ofNat 2) (x+y)))) := by
  have he : evalExpr? cfg f evm (.binary .add a b) = .ok (.int (EVM.signed x+EVM.signed y)) := by
    rw [evalExpr_binary_nonshort (by decide) (by decide), hx, hy]
    rfl
  have hc := evalExpr_cast_int (intType := .sint ⟨24, by decide⟩) he
  simpa only [normalizeSigned24Integer, wordOfInt_signed_add] using hc

-- LIBRARY CANDIDATE: int24 subtraction followed by truncation agrees with the word operation.
theorem evalSigned24Sub {cfg : Config} {f : Frame} {evm : EVM.State} {a b : Expr} {x y : UInt256}
    (hx : evalExpr? cfg f evm a = .ok (.int (EVM.signed x)))
    (hy : evalExpr? cfg f evm b = .ok (.int (EVM.signed y))) :
    evalExpr? cfg f evm (.cast (.binary .sub a b) (.elem (.int (.sint ⟨24, by decide⟩)))) =
      .ok (.int (EVM.signed (UInt256.signextend (UInt256.ofNat 2) (UInt256.sub x y)))) := by
  have he : evalExpr? cfg f evm (.binary .sub a b) = .ok (.int (EVM.signed x-EVM.signed y)) := by
    rw [evalExpr_binary_nonshort (by decide) (by decide), hx, hy]
    rfl
  have hc := evalExpr_cast_int (intType := .sint ⟨24, by decide⟩) he
  simpa only [normalizeSigned24Integer, wordOfInt_signed_sub] using hc

-- LIBRARY CANDIDATE: int24 multiplication followed by truncation agrees with the word operation.
theorem evalSigned24Mul {cfg : Config} {f : Frame} {evm : EVM.State} {a b : Expr} {x y : UInt256}
    (hx : evalExpr? cfg f evm a = .ok (.int (EVM.signed x)))
    (hy : evalExpr? cfg f evm b = .ok (.int (EVM.signed y))) :
    evalExpr? cfg f evm (.cast (.binary .mul a b) (.elem (.int (.sint ⟨24, by decide⟩)))) =
      .ok (.int (EVM.signed (UInt256.signextend (UInt256.ofNat 2) (UInt256.mul x y)))) := by
  have he : evalExpr? cfg f evm (.binary .mul a b) = .ok (.int (EVM.signed x*EVM.signed y)) := by
    rw [evalExpr_binary_nonshort (by decide) (by decide), hx, hy]
    rfl
  have hc := evalExpr_cast_int (intType := .sint ⟨24, by decide⟩) he
  simpa only [normalizeSigned24Integer, wordOfInt_signed_mul] using hc

end Benchmarks.UniswapV4PoolManager
