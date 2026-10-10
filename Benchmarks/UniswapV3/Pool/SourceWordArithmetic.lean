import Benchmarks.UniswapV3.Pool.ModularWords
import Benchmarks.UniswapV3.Pool.SourceExpressions

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

-- LIBRARY CANDIDATE: the full-width unsigned cast is the EVM word representation.
theorem normalizeUInt256_int (i : Int) :
    normalizeInt (.uint ⟨256, by decide⟩) i = Int.ofNat (EVM.wordOfInt i).toNat := by
  rw [← normalizeInt_wordOfInt (.uint ⟨256, by decide⟩) i, normalizeInt_uint256_word]

-- GENERALIZES Reasoning.SolmArithmetic wrapping arithmetic to arbitrary frames.
theorem evalExpr_word_add {cfg : Config} {frame : Frame} {evm : EVM.State}
    {lhs rhs : Expr} {a b : UInt256}
    (ha : evalExpr? cfg frame evm lhs = .ok (.int (Int.ofNat a.toNat)))
    (hb : evalExpr? cfg frame evm rhs = .ok (.int (Int.ofNat b.toNat))) :
    evalExpr? cfg frame evm (.cast (.binary .add lhs rhs)
      (.elem (.int (.uint ⟨256, by decide⟩)))) = .ok (.int (Int.ofNat (a + b).toNat)) := by
  simp only [evalExpr?, ha, hb, bind, EvalResult.bind, castValue?, evalBinaryOp?,
    normalizeUInt256_int, wordOfInt_add, wordOfInt_ofNat_toNat]
  rfl

theorem evalExpr_word_sub {cfg : Config} {frame : Frame} {evm : EVM.State}
    {lhs rhs : Expr} {a b : UInt256}
    (ha : evalExpr? cfg frame evm lhs = .ok (.int (Int.ofNat a.toNat)))
    (hb : evalExpr? cfg frame evm rhs = .ok (.int (Int.ofNat b.toNat))) :
    evalExpr? cfg frame evm (.cast (.binary .sub lhs rhs)
      (.elem (.int (.uint ⟨256, by decide⟩)))) =
      .ok (.int (Int.ofNat (UInt256.sub a b).toNat)) := by
  simp only [evalExpr?, ha, hb, bind, EvalResult.bind, castValue?, evalBinaryOp?,
    normalizeUInt256_int, wordOfInt_sub, wordOfInt_ofNat_toNat]
  rfl

-- GENERALIZES Reasoning.SolmArithmetic.evalExpr_div_uint256_ok to arbitrary frames.
theorem evalExpr_word_div {cfg : Config} {frame : Frame} {evm : EVM.State}
    {lhs rhs : Expr} {a b : UInt256}
    (ha : evalExpr? cfg frame evm lhs = .ok (.int (Int.ofNat a.toNat)))
    (hb : evalExpr? cfg frame evm rhs = .ok (.int (Int.ofNat b.toNat)))
    (hn : b.toNat ≠ 0) :
    evalExpr? cfg frame evm (.binary .div lhs rhs) =
      .ok (.int (Int.ofNat (UInt256.div a b).toNat)) := by
  simp [evalExpr?, ha, hb, bind, EvalResult.bind, evalBinaryOp?, hn, udiv_toNat,
    Int.natCast_ediv]

-- LIBRARY CANDIDATE: EVM remainder at a nonzero denominator.
theorem umod_toNat_of_ne_zero (a b : UInt256) (hn : b.toNat ≠ 0) :
    (UInt256.mod a b).toNat = a.toNat % b.toNat := by
  have hz : b.val ≠ 0 := fun h ↦ hn (congrArg Fin.val h)
  simp only [UInt256.mod, beq_iff_eq, if_neg hz]
  rfl

-- GENERALIZES Reasoning.SolmArithmetic.evalExpr_mod_int_ok to arbitrary frames.
theorem evalExpr_word_mod {cfg : Config} {frame : Frame} {evm : EVM.State}
    {lhs rhs : Expr} {a b : UInt256}
    (ha : evalExpr? cfg frame evm lhs = .ok (.int (Int.ofNat a.toNat)))
    (hb : evalExpr? cfg frame evm rhs = .ok (.int (Int.ofNat b.toNat)))
    (hn : b.toNat ≠ 0) :
    evalExpr? cfg frame evm (.binary .mod lhs rhs) =
      .ok (.int (Int.ofNat (UInt256.mod a b).toNat)) := by
  simp [evalExpr?, ha, hb, bind, EvalResult.bind, evalBinaryOp?, hn,
    umod_toNat_of_ne_zero a b hn, Int.natCast_emod]

end Benchmarks.UniswapV3.Pool
