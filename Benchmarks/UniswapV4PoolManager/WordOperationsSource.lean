import Benchmarks.UniswapV4PoolManager.Slot0Source
import Benchmarks.UniswapV4PoolManager.SignedWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- GENERALIZES Reasoning.Theory.rpowShiftRight128_toNat to arbitrary bounded shifts.
theorem wordShiftRightNat (x : UInt256) {n : Nat} (hn : n < 256) :
    (UInt256.shiftRight x (UInt256.ofNat n)).toNat = x.toNat / 2^n := by
  have hn' : (UInt256.ofNat n).toNat = n := UInt256.toNat_ofNat_of_lt (by
    change _ < 2^256; omega)
  unfold UInt256.shiftRight
  rw [if_neg (by change ¬(UInt256.ofNat n).toNat ≥ 256; rw [hn']; omega)]
  change (x.val >>> (UInt256.ofNat n).val).val = _
  rw [Fin.shiftRight_val]
  change x.toNat >>> (UInt256.ofNat n).toNat = _
  rw [hn', Nat.shiftRight_eq_div_pow]

-- LIBRARY CANDIDATE: composition of bounded logical right shifts.
theorem wordShiftRightCompose (w : UInt256) {a b : Nat} (hab : a+b < 256) :
    UInt256.shiftRight (UInt256.shiftRight w (UInt256.ofNat a)) (UInt256.ofNat b) =
      UInt256.shiftRight w (UInt256.ofNat (a+b)) := by
  apply u256_inj
  rw [wordShiftRightNat _ (by omega), wordShiftRightNat _ (by omega), wordShiftRightNat _ hab,
    Nat.div_div_eq_div_mul, ← Nat.pow_add]

-- LIBRARY CANDIDATE: logical right shift distributes over word masks.
theorem wordShiftRightAnd (x y : UInt256) {n : Nat} (hn : n < 256) :
    UInt256.shiftRight (UInt256.land x y) (UInt256.ofNat n) =
      UInt256.land (UInt256.shiftRight x (UInt256.ofNat n)) (UInt256.shiftRight y (UInt256.ofNat n)) := by
  apply u256_inj
  simp only [wordShiftRightNat _ hn, uland_toNat, ← Nat.shiftRight_eq_div_pow,
    Nat.shiftRight_and_distrib]

-- LIBRARY CANDIDATE: bounded unsigned right shift at an arbitrary source width.
theorem evalUintWordShr {cfg : Config} {f : Frame} {evm : EVM.State} {a b : Expr} {x : UInt256} {n : Nat}
    (bits : BitWidth) (hc : x.toNat < 2^bits.val) (hn : n < bits.val)
    (hx : evalExpr? cfg f evm a = .ok (.int (Int.ofNat x.toNat)))
    (hy : evalExpr? cfg f evm b = .ok (.int (Int.ofNat n))) :
    evalExpr? cfg f evm (.binary (.shr (.uint bits)) a b) =
      .ok (.int (Int.ofNat (UInt256.shiftRight x (UInt256.ofNat n)).toNat)) := by
  rw [evalExpr_binary_nonshort (by simp) (by simp), hx, hy]
  simp only [bind, EvalResult.bind, evalBinaryOp?, IntType.bitWidth]
  simp only [Int.ofNat_eq_natCast,
    Int.not_lt.mpr (Int.natCast_nonneg n), if_false, Int.toNat_natCast,
    Nat.not_le.mpr hn]
  change EvalResult.ok (Value.int ((Int.ofNat x.toNat % Int.ofNat (2^bits.val)) / Int.ofNat (2^n))) = _
  have hm : Int.ofNat x.toNat % Int.ofNat (2^bits.val) = Int.ofNat x.toNat :=
    Int.emod_eq_of_lt (Int.natCast_nonneg _) (Int.ofNat_lt.mpr hc)
  simpa only [wordShiftRightNat x (lt_of_lt_of_le hn bits.property.2.1),
    Int.ofNat_eq_natCast, Int.natCast_ediv] using
    congrArg (fun z : Int => EvalResult.ok (Value.int (z / Int.ofNat (2^n)))) hm

theorem evalWordShr {cfg : Config} {f : Frame} {evm : EVM.State} {a b : Expr} {x : UInt256} {n : Nat}
    (hn : n < 256) (hx : evalExpr? cfg f evm a = .ok (.int (Int.ofNat x.toNat)))
    (hy : evalExpr? cfg f evm b = .ok (.int (Int.ofNat n))) :
    evalExpr? cfg f evm (.binary (.shr (.uint ⟨256, by decide⟩)) a b) =
      .ok (.int (Int.ofNat (UInt256.shiftRight x (UInt256.ofNat n)).toNat)) :=
  evalUintWordShr ⟨256, by decide⟩ x.val.isLt hn hx hy

-- LIBRARY CANDIDATE: wrapping multiplication in arbitrary expression contexts.
theorem evalWordMul {cfg : Config} {f : Frame} {evm : EVM.State} {a b : Expr} {x y : UInt256}
    (hx : evalExpr? cfg f evm a = .ok (.int (Int.ofNat x.toNat)))
    (hy : evalExpr? cfg f evm b = .ok (.int (Int.ofNat y.toNat))) :
    evalExpr? cfg f evm (.cast (.binary .mul a b) (.elem (.int (.uint ⟨256, by decide⟩)))) =
      .ok (.int (Int.ofNat (UInt256.mul x y).toNat)) := by
  have he : evalExpr? cfg f evm (.binary .mul a b) =
      .ok (.int (Int.ofNat x.toNat * Int.ofNat y.toNat)) := by
    rw [evalExpr_binary_nonshort (by decide) (by decide), hx, hy]
    rfl
  have hc := evalExpr_cast_int (intType := .uint ⟨256, by decide⟩) he
  convert hc using 2

-- LIBRARY CANDIDATE: wrapping addition in arbitrary expression contexts.
theorem evalWordAdd {cfg : Config} {f : Frame} {evm : EVM.State} {a b : Expr} {x y : UInt256}
    (hx : evalExpr? cfg f evm a = .ok (.int (Int.ofNat x.toNat)))
    (hy : evalExpr? cfg f evm b = .ok (.int (Int.ofNat y.toNat))) :
    evalExpr? cfg f evm (.cast (.binary .add a b) (.elem (.int (.uint ⟨256, by decide⟩)))) =
      .ok (.int (Int.ofNat (x + y).toNat)) := by
  have he : evalExpr? cfg f evm (.binary .add a b) =
      .ok (.int (Int.ofNat x.toNat + Int.ofNat y.toNat)) := by
    rw [evalExpr_binary_nonshort (by decide) (by decide), hx, hy]
    rfl
  have hc := evalExpr_cast_int (intType := .uint ⟨256, by decide⟩) he
  convert hc using 2

-- GENERALIZES Reasoning.Theory.evalExpr_div_uint256_ok to arbitrary frames.
theorem evalWordDiv {cfg : Config} {f : Frame} {evm : EVM.State} {a b : Expr} {x y : UInt256}
    (hx : evalExpr? cfg f evm a = .ok (.int (Int.ofNat x.toNat)))
    (hy : evalExpr? cfg f evm b = .ok (.int (Int.ofNat y.toNat))) (hn : y ≠ ⟨0⟩) :
    evalExpr? cfg f evm (.binary .div a b) = .ok (.int (Int.ofNat (UInt256.div x y).toNat)) := by
  have hz : y.toNat ≠ 0 := fun h => hn (uint256_toNat_eq_zero h)
  rw [evalExpr_binary_nonshort (by decide) (by decide), hx, hy]
  simp only [bind, EvalResult.bind, evalBinaryOp?, Int.ofNat_eq_natCast,
    Int.natCast_eq_zero, hz, if_false, udiv_toNat, Int.natCast_ediv]

-- LIBRARY CANDIDATE: changing signed interpretation preserves the 256-bit pattern.
theorem normalizeUnsignedSigned (w : UInt256) :
    normalizeInt (.uint ⟨256, by decide⟩) (EVM.signed w) = Int.ofNat w.toNat := by
  dsimp only [EVM.signed]
  split
  · exact normalizeInt_uint256_word w
  · change (Int.ofNat w.toNat-Int.ofNat EVM.wordModulus) % Int.ofNat EVM.wordModulus = _
    rw [Int.sub_emod, Int.emod_self, sub_zero, Int.emod_emod]
    exact normalizeInt_uint256_word w

-- LIBRARY CANDIDATE: signed bitwise OR has the same word result as EVM OR.
theorem evalSignedWordOr {cfg : Config} {f : Frame} {evm : EVM.State} {a b : Expr} {x y : UInt256}
    (hx : evalExpr? cfg f evm a = .ok (.int (EVM.signed x)))
    (hy : evalExpr? cfg f evm b = .ok (.int (EVM.signed y))) :
    evalExpr? cfg f evm (.binary (.bitOr (.sint ⟨256, by decide⟩)) a b) =
      .ok (.int (EVM.signed (UInt256.lor x y))) := by
  rw [evalExpr_binary_nonshort (by decide) (by decide), hx, hy]
  simp only [bind, EvalResult.bind, evalBinaryOp?, evalIntBitwise, IntType.bitWidth,
    normalizeUnsignedSigned, Int.toNat_natCast]
  change EvalResult.ok (Value.int (normalizeInt (.sint ⟨256, by decide⟩)
    (Int.ofNat (x.toNat ||| y.toNat)))) = _
  rw [← u256_lor_toNat_exact, normalizeInt_sint256_word]
  rfl

-- LIBRARY CANDIDATE: a signed left shift of a nonnegative word keeps its modular word semantics.
theorem evalSignedShlOfNat {cfg : Config} {f : Frame} {evm : EVM.State} {a b : Expr} {x : UInt256} {n : Nat}
    (hn : n < 256) (hx : evalExpr? cfg f evm a = .ok (.int (Int.ofNat x.toNat)))
    (hy : evalExpr? cfg f evm b = .ok (.int (Int.ofNat n))) :
    evalExpr? cfg f evm (.binary (.shl (.sint ⟨256, by decide⟩)) a b) =
      .ok (.int (EVM.signed (UInt256.shiftLeft x (UInt256.ofNat n)))) := by
  rw [evalExpr_binary_nonshort (by decide) (by decide), hx, hy]
  simp only [bind, EvalResult.bind, evalBinaryOp?, IntType.bitWidth, Int.ofNat_eq_natCast,
    Int.not_lt.mpr (Int.natCast_nonneg n), if_false, Int.toNat_natCast, Nat.not_le.mpr hn]
  rw [← show normalizeInt (.sint ⟨256, by decide⟩)
      (Int.ofNat (UInt256.shiftLeft x (UInt256.ofNat n)).toNat) =
      EVM.signed (UInt256.shiftLeft x (UInt256.ofNat n)) from normalizeInt_sint256_word _]
  rw [wordShiftLeftNat x hn]
  simp only [normalizeInt, Int.ofNat_eq_natCast, Int.natCast_emod, Int.natCast_mul,
    EVM.twoPow, Int.natCast_pow, Int.cast_ofNat_Int]
  norm_num only [UInt256.size]
  simp only [Int.emod_emod]

end Benchmarks.UniswapV4PoolManager
