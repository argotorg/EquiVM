import Benchmarks.Midnight.Uint128Arithmetic
import Benchmarks.Midnight.InternalCall

/-! Source semantics of the checked uint128 conversion and fee addition. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def toUint128Function : FunctionDecl := contract.functions[3]!

theorem toUint128BodyReturns {cfg : Config} {frame : Frame} {evm : EVM.State} {value : UInt256}
    (hget : frame.locals.get? "x" = some (.int value.toNat)) (hvalue : value.toNat < 2^128) :
    ExecFuncBody cfg frame evm toUint128Function.body
      (.returned frame evm (some [.int value.toNat])) := by
  apply ExecFuncBody.execBlockRet
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · have hle : (value.toNat : Int) ≤ 340282366920938463463374607431768211455 := by omega
    simp only [evalExpr?, hget, evalBinaryOp?, EvalResult.ofOption, EvalResult.bind, pure, bind]
    norm_num only
    simp only [hle, decide_true]
  apply ExecBlock.consReturn
  apply ExecStmt.return
  have he : evalExpr? cfg frame evm (.var "x") = .ok (.int value.toNat) := by
    simp only [evalExpr?, hget, EvalResult.ofOption]
  have hcast := evalCast128 he
  rw [low128, uint128Mask_clean hvalue] at hcast
  simpa only [evalExprs?, EvalResult.bind, pure, bind] using
    congrArg (fun r ↦ r.bind (fun v ↦ EvalResult.ok [v])) hcast

theorem toUint128BodyReverts {cfg : Config} {frame : Frame} {evm : EVM.State} {value : UInt256}
    (hget : frame.locals.get? "x" = some (.int value.toNat)) (hvalue : 2^128 ≤ value.toNat) :
    ExecFuncBody cfg frame evm toUint128Function.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply ExecBlock.consRevert (ExecStmt.requireFalse ?_)
  have hle : ¬ (value.toNat : Int) ≤ 340282366920938463463374607431768211455 := by omega
  simp only [evalExpr?, hget, evalBinaryOp?, EvalResult.ofOption, EvalResult.bind, pure, bind]
  norm_num only
  simp only [hle, decide_false]

theorem callToUint128 {cfg : Config} {frame : Frame} {evm : EVM.State}
    {value : UInt256} {args : List Expr} {name : Ident}
    (hc : frame.contract = contract) (he : evalExprs? cfg frame evm args = .ok [.int value.toNat])
    (hvalue : value.toNat < 2^128) :
    ExecStmt cfg frame evm (.internalCall "UtilsLib_toUint128" args name)
      (.ok (resumeAfterInternalCall frame name (some [.int value.toNat])) evm) := by
  apply internalCallFunctionReturn (callee := toUint128Function)
    (locals := (∅ : Store).insert "x" (.int value.toNat)) he
  · rw [hc]; rfl
  · rfl
  · exact toUint128BodyReturns (store_get_self _ _ _) hvalue

theorem callToUint128Revert {cfg : Config} {frame : Frame} {evm : EVM.State}
    {value : UInt256} {args : List Expr} {name : Ident}
    (hc : frame.contract = contract) (he : evalExprs? cfg frame evm args = .ok [.int value.toNat])
    (hvalue : 2^128 ≤ value.toNat) :
    ExecStmt cfg frame evm (.internalCall "UtilsLib_toUint128" args name) .reverted := by
  apply internalCallFunctionRevert (callee := toUint128Function)
    (locals := (∅ : Store).insert "x" (.int value.toNat)) he
  · rw [hc]; rfl
  · rfl
  · exact toUint128BodyReverts (store_get_self _ _ _) hvalue

theorem evalCheckedAdd128 {cfg : Config} {frame : Frame} {evm : EVM.State}
    {lhs rhs : Expr} {a b : UInt256}
    (ha : evalExpr? cfg frame evm lhs = .ok (.int a.toNat))
    (hb : evalExpr? cfg frame evm rhs = .ok (.int b.toNat))
    (hsum : a.toNat + b.toNat < 2^128) :
    evalExpr? cfg frame evm (.inRange packedUInt128Int (.binary .add lhs rhs)) =
      .ok (.int (a + b).toNat) := by
  have hn : (a + b).toNat = a.toNat + b.toNat := addWord_toNat a b (by change _ < 2^256; omega)
  apply evalInRange128
  · rw [evalExpr_binary_nonshort (by decide) (by decide), ha, hb]
    simp only [EvalResult.bind, bind, evalBinaryOp?, hn, Int.natCast_add]
  · rw [hn]; exact hsum

theorem evalCheckedAdd128Overflow {cfg : Config} {frame : Frame} {evm : EVM.State}
    {lhs rhs : Expr} {a b : UInt256}
    (ha : evalExpr? cfg frame evm lhs = .ok (.int a.toNat))
    (hb : evalExpr? cfg frame evm rhs = .ok (.int b.toNat))
    (hsum : 2^128 ≤ a.toNat + b.toNat) :
    evalExpr? cfg frame evm (.inRange packedUInt128Int (.binary .add lhs rhs)) = .revert := by
  rw [evalExpr?, evalExpr_binary_nonshort (by decide) (by decide), ha, hb]
  simp only [EvalResult.bind, bind, evalBinaryOp?, packedUInt128Int]
  have hh : (a.toNat : Int) + b.toNat ≥ 2^128 := by exact_mod_cast hsum
  simp only [hh, decide_true, Bool.or_true, if_true]

end Benchmarks.Midnight
