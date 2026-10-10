import Benchmarks.UniswapV3.Pool.SourceWordBits

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

-- GENERALIZES shiftLeft_toNat_of_noOverflow to include wrapping shifts.
theorem wordShiftLeft_toNat (w bits : UInt256) (h : bits.toNat < 256) :
    (UInt256.shiftLeft w bits).toNat = w.toNat * 2 ^ bits.toNat % UInt256.size := by
  unfold UInt256.shiftLeft
  rw [if_neg (show ¬ bits.val ≥ 256 from Nat.not_le.mpr h)]
  change (w.toNat <<< bits.toNat) % UInt256.size = _
  rw [Nat.shiftLeft_eq]

-- LIBRARY CANDIDATE: word shifts preserve bitwise conjunction.
theorem wordShiftLeft_land (a b bits : UInt256) (h : bits.toNat < 256) :
    UInt256.land (UInt256.shiftLeft a bits) (UInt256.shiftLeft b bits) =
      UInt256.shiftLeft (UInt256.land a b) bits := by
  apply u256_inj
  rw [uland_toNat, wordShiftLeft_toNat _ _ h, wordShiftLeft_toNat _ _ h,
    wordShiftLeft_toNat _ _ h, uland_toNat]
  change (a.toNat * 2 ^ bits.toNat % 2 ^ 256) &&&
      (b.toNat * 2 ^ bits.toNat % 2 ^ 256) =
    (a.toNat &&& b.toNat) * 2 ^ bits.toNat % 2 ^ 256
  rw [← Nat.and_mod_two_pow, ← Nat.shiftLeft_eq, ← Nat.shiftLeft_eq,
    ← Nat.shiftLeft_and_distrib, Nat.shiftLeft_eq]

-- LIBRARY CANDIDATE: a zero-count right shift is the original word.
theorem wordShiftRight_zero (w : UInt256) : UInt256.shiftRight w ⟨0⟩ = w := by
  apply u256_inj
  rw [wordShiftRight_toNat _ _ (by decide)]
  simp only [show (⟨0⟩ : UInt256).toNat = 0 from rfl, pow_zero, Nat.div_one]

-- LIBRARY CANDIDATE: unsigned source shifts at an evaluated word-sized count.
theorem evalExpr_word_shr_by {cfg : Config} {frame : Frame} {evm : EVM.State}
    {lhs rhs : Expr} {a b : UInt256}
    (ha : evalExpr? cfg frame evm lhs = .ok (.int (Int.ofNat a.toNat)))
    (hb : evalExpr? cfg frame evm rhs = .ok (.int (Int.ofNat b.toNat)))
    (hbits : b.toNat < 256) :
    evalExpr? cfg frame evm (.binary (.shr (.uint ⟨256, by decide⟩)) lhs rhs) =
      .ok (.int (Int.ofNat (UInt256.shiftRight a b).toNat)) := by
  simp only [evalExpr?, ha, hb, evalBinaryOp?, bind, EvalResult.bind, pure,
    show ¬ Int.ofNat b.toNat < 0 from Int.not_lt.mpr (Int.natCast_nonneg _), ↓reduceIte]
  change (if 256 ≤ b.toNat then EvalResult.ok (Value.int 0) else
    EvalResult.ok (Value.int
      (normalizeInt (.uint ⟨256, by decide⟩) (Int.ofNat a.toNat) / EVM.twoPow b.toNat))) = _
  rw [if_neg (Nat.not_le.mpr hbits), normalizeInt_uint256_word,
    wordShiftRight_toNat _ _ hbits]
  simp only [EVM.twoPow, Int.ofNat_eq_natCast, Int.natCast_ediv]

theorem evalExpr_word_shl_by {cfg : Config} {frame : Frame} {evm : EVM.State}
    {lhs rhs : Expr} {a b : UInt256}
    (ha : evalExpr? cfg frame evm lhs = .ok (.int (Int.ofNat a.toNat)))
    (hb : evalExpr? cfg frame evm rhs = .ok (.int (Int.ofNat b.toNat)))
    (hbits : b.toNat < 256) :
    evalExpr? cfg frame evm (.binary (.shl (.uint ⟨256, by decide⟩)) lhs rhs) =
      .ok (.int (Int.ofNat (UInt256.shiftLeft a b).toNat)) := by
  simp only [evalExpr?, ha, hb, evalBinaryOp?, bind, EvalResult.bind, pure,
    show ¬ Int.ofNat b.toNat < 0 from Int.not_lt.mpr (Int.natCast_nonneg _), ↓reduceIte]
  change (if 256 ≤ b.toNat then EvalResult.ok (Value.int 0) else
    EvalResult.ok (Value.int
      (normalizeInt (.uint ⟨256, by decide⟩) (Int.ofNat a.toNat * EVM.twoPow b.toNat)))) = _
  rw [if_neg (Nat.not_le.mpr hbits), wordShiftLeft_toNat _ _ hbits]
  simp only [normalizeInt, IntType.bitWidth, EVM.twoPow, Int.ofNat_eq_natCast,
    Int.natCast_mod, Int.natCast_mul]
  rfl

end Benchmarks.UniswapV3.Pool
