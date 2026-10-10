import Benchmarks.UniswapV3.Pool.FlashProtocolWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

-- GENERALIZES Reasoning.SolmArithmetic wrapping multiplication to arbitrary frames.
theorem evalExpr_word_mul {cfg : Config} {frame : Frame} {evm : EVM.State}
    {lhs rhs : Expr} {a b : UInt256}
    (ha : evalExpr? cfg frame evm lhs = .ok (.int (Int.ofNat a.toNat)))
    (hb : evalExpr? cfg frame evm rhs = .ok (.int (Int.ofNat b.toNat))) :
    evalExpr? cfg frame evm (.cast (.binary .mul lhs rhs)
      (.elem (.int (.uint ⟨256, by decide⟩)))) = .ok (.int (Int.ofNat (a * b).toNat)) := by
  simp only [evalExpr?, ha, hb, bind, EvalResult.bind, castValue?, evalBinaryOp?,
    normalizeUInt256_int, wordOfInt_mul, wordOfInt_ofNat_toNat]
  rfl

-- LIBRARY CANDIDATE: source unsigned bitwise conjunction agrees with EVM AND.
theorem evalExpr_word_land {cfg : Config} {frame : Frame} {evm : EVM.State}
    {lhs rhs : Expr} {a b : UInt256}
    (ha : evalExpr? cfg frame evm lhs = .ok (.int (Int.ofNat a.toNat)))
    (hb : evalExpr? cfg frame evm rhs = .ok (.int (Int.ofNat b.toNat))) :
    evalExpr? cfg frame evm (.binary (.bitAnd (.uint ⟨256, by decide⟩)) lhs rhs) =
      .ok (.int (Int.ofNat (UInt256.land a b).toNat)) := by
  simp only [evalExpr?, ha, hb, bind, EvalResult.bind, evalBinaryOp?, evalIntBitwise,
    IntType.bitWidth, normalizeInt_uint256_word]
  change EvalResult.ok (Value.int (normalizeInt (.uint ⟨256, by decide⟩)
    (Int.ofNat (Nat.land a.toNat b.toNat)))) = _
  have hand := uland_toNat a b
  change (UInt256.land a b).toNat = Nat.land a.toNat b.toNat at hand
  rw [← hand, normalizeInt_uint256_word]

-- LIBRARY CANDIDATE: a full-width right shift at a fixed literal count.
theorem evalExpr_word_shr {cfg : Config} {frame : Frame} {evm : EVM.State}
    {expr : Expr} {a : UInt256} (bits : Nat) (hbits : bits < 256)
    (ha : evalExpr? cfg frame evm expr = .ok (.int (Int.ofNat a.toNat))) :
    evalExpr? cfg frame evm
      (.binary (.shr (.uint ⟨256, by decide⟩)) expr (.intLit (Int.ofNat bits))) =
      .ok (.int (Int.ofNat (UInt256.shiftRight a (UInt256.ofNat bits)).toNat)) := by
  have hb : (UInt256.ofNat bits).toNat = bits :=
    UInt256.toNat_ofNat_of_lt (lt_trans hbits (by decide))
  rw [wordShiftRight_toNat _ _ (by rw [hb]; exact hbits), hb]
  simpa only [normalizeInt_uint256_word, Int.natCast_ediv] using
    evalExpr_uintShiftRight ⟨256, by decide⟩ a.toNat bits ha hbits

end Benchmarks.UniswapV3.Pool
