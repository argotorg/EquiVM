import Benchmarks.UniswapV4PoolManager.WordOperationsSource
import Benchmarks.UniswapV4PoolManager.WordArrayLoop

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

abbrev wordByteFunction : FunctionDecl := contract.functions[0]!
theorem wordByte_lookup : lookupCallable? contract "wordByte" = some wordByteFunction.toCallable := rfl

theorem wordByteBody {f : Frame} {evm : EVM.State} {word index : UInt256}
    (hw : f.locals.get? "word" = some (.int (Int.ofNat word.toNat)))
    (hi : f.locals.get? "index" = some (.int (Int.ofNat index.toNat))) :
    ExecFuncBody config f evm wordByteFunction.body
      (.returned f evm (some [.int (Int.ofNat (UInt256.byteAt index word).toNat)])) := by
  have hcond := evalNatLt (evalLocalValue (cfg := config) (evm := evm) hi)
    (show evalExpr? config f evm (.intLit 32) = .ok (.int (Int.ofNat 32)) by simp only [evalExpr?, pure]; rfl)
  apply ExecFuncBody.execBlockRet
  apply ABlock.start.returns
  change evalExpr? config f evm (.ite _ _ _) = _
  by_cases hb : index.toNat < 32
  · rw [evalExpr?, hcond, decide_eq_true hb]
    have hsub : evalExpr? config f evm (.binary .sub (.intLit 31) (.var "index")) =
        .ok (.int (Int.ofNat (31-index.toNat))) := by
      rw [evalExpr_binary_nonshort (by decide) (by decide)]
      simp only [evalExpr?, evalLocalValue hi, bind, EvalResult.bind, evalBinaryOp?, pure]
      simp only [Int.ofNat_eq_natCast, Int.natCast_sub (by omega : index.toNat ≤ 31)]
      rfl
    have hshift : evalExpr? config f evm
        (.binary .mul (.binary .sub (.intLit 31) (.var "index")) (.intLit 8)) =
        .ok (.int (Int.ofNat ((31-index.toNat)*8))) := by
      rw [evalExpr_binary_nonshort (by decide) (by decide), hsub]
      simp only [evalExpr?, bind, EvalResult.bind, evalBinaryOp?, pure,
        Int.ofNat_eq_natCast, Int.natCast_mul]
      rfl
    have hread := evalWordAnd (evalWordShr (by omega : (31-index.toNat)*8 < 256)
      (evalLocalValue (cfg := config) (evm := evm) hw) hshift)
      (show evalExpr? config f evm (.intLit 255) = .ok (.int (Int.ofNat (⟨255⟩ : UInt256).toNat)) by
        simp only [evalExpr?, pure]; rfl)
    rw [UInt256.byteAt, if_neg (by change ¬index.toNat > 31; omega)]
    exact hread
  · rw [evalExpr?, hcond, decide_eq_false hb]
    rw [UInt256.byteAt, if_pos (by change index.toNat > 31; omega)]
    simp only [bind, EvalResult.bind, evalExpr?, pure]
    rfl

theorem wordByteCall {f : Frame} {evm : EVM.State} {ew ei : Expr} {word index : UInt256}
    (hf : f.contract = contract)
    (hw : evalExpr? config f evm ew = .ok (.int (Int.ofNat word.toNat)))
    (hi : evalExpr? config f evm ei = .ok (.int (Int.ofNat index.toNat))) (retVar : Ident) :
    ExecStmt config f evm (.internalCall "wordByte" [ew, ei] retVar)
      (.ok {f with locals := f.locals.insert retVar (.int (Int.ofNat (UInt256.byteAt index word).toNat))} evm) := by
  apply internalCallFunctionReturn (argVals := [.int (Int.ofNat word.toNat), .int (Int.ofNat index.toNat)])
    (value := some [.int (Int.ofNat (UInt256.byteAt index word).toNat)])
    (by simp only [evalExprs?, hw, hi, bind, EvalResult.bind, pure])
    (by rw [hf]; exact wordByte_lookup) rfl
  exact wordByteBody (store_get_self _ _ _)
    ((store_get_ne _ _ (by decide : ("word" == "index") = false)).trans (store_get_self _ _ _))

end Benchmarks.UniswapV4PoolManager
