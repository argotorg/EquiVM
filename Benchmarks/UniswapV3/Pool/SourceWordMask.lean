import Benchmarks.UniswapV3.Pool.WordComplements

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

-- LIBRARY CANDIDATE: a one-bit mask at a bounded integer shift count.
theorem evalExpr_one_shl_int {cfg : Config} {frame : Frame} {evm : EVM.State}
    {expr : Expr} {bit : Int}
    (he : evalExpr? cfg frame evm expr = .ok (.int bit)) (hb : 0 ≤ bit ∧ bit < 256) :
    evalExpr? cfg frame evm (.binary (.shl (.uint ⟨256, by decide⟩)) (.intLit 1) expr) =
      .ok (.int (Int.ofNat (UInt256.ofNat (2 ^ bit.toNat)).toNat)) := by
  simp only [evalExpr?, he, evalBinaryOp?, bind, EvalResult.bind, pure,
    if_neg (show ¬ bit < 0 by omega), IntType.bitWidth,
    if_neg (show ¬ 256 ≤ bit.toNat by omega), one_mul,
    normalizeUInt256_int, wordOfInt_ofNat_eq]
  rfl

-- LIBRARY CANDIDATE: full-width source bitwise negation agrees with EVM NOT.
theorem evalExpr_word_lnot {cfg : Config} {frame : Frame} {evm : EVM.State}
    {expr : Expr} {word : UInt256}
    (he : evalExpr? cfg frame evm expr = .ok (.int (Int.ofNat word.toNat))) :
    evalExpr? cfg frame evm (.unary (.bitNot (.uint ⟨256, by decide⟩)) expr) =
      .ok (.int (Int.ofNat (UInt256.lnot word).toNat)) := by
  simp only [evalExpr?, he, evalUnaryOp?, bind, EvalResult.bind, EvalResult.ofOption,
    IntType.bitWidth, normalizeInt_uint256_word, Int.toNat_natCast]
  change EvalResult.ok (Value.int (normalizeInt (.uint ⟨256, by decide⟩)
    (Int.ofNat (2 ^ 256 - 1 - word.toNat)))) = _
  rw [← lnot_toNat_gen, normalizeInt_uint256_word]

end Benchmarks.UniswapV3.Pool
