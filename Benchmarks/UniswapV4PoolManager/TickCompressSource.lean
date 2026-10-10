import Benchmarks.UniswapV4PoolManager.TickCompressWords
import Benchmarks.UniswapV4PoolManager.SignedQuotientSource
import Benchmarks.UniswapV4PoolManager.ValueLocals

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

abbrev tickCompressFunction : FunctionDecl := contract.functions[111]!
theorem tickCompress_lookup : lookupCallable? contract "TickBitmap_compress" =
    some tickCompressFunction.toCallable := rfl

def tickCompressExpr : Expr :=
  .cast (.binary .sub (.binary .sdiv (.var "tick") (.var "tickSpacing"))
    (.ite (.binary .lt (.binary .srem (.var "tick") (.var "tickSpacing")) (.intLit 0))
      (.intLit 1) (.intLit 0))) (.elem (.int (.sint ⟨24, by decide⟩)))

theorem tickCompress_body_eq : tickCompressFunction.body =
    [.ite (.binary .eq (.var "tickSpacing") (.intLit 0)) [.return [.intLit 0]] [],
     .return [tickCompressExpr]] := rfl

theorem tickCompressBody {f : Frame} {evm : EVM.State} {tick spacing : Int}
    (ht : f.locals.get? "tick" = some (.int tick))
    (hs : f.locals.get? "tickSpacing" = some (.int spacing)) :
    ExecFuncBody config f evm tickCompressFunction.body
      (.returned f evm (some [.int (tickCompressValue tick spacing)])) := by
  have hcond := evalIntEq (evalLocalValue (cfg := config) (evm := evm) hs)
    (show evalExpr? config f evm (.intLit 0) = .ok (.int 0) by simp only [evalExpr?, pure])
  rw [tickCompress_body_eq]
  apply ExecFuncBody.execBlockRet
  by_cases hz : spacing = 0
  · rw [tickCompressValue, if_pos hz]
    exact ExecBlock.consReturn (ExecStmt.iteTrue (by simpa only [decide_eq_true hz] using hcond)
      (ABlock.start.returns (by simp only [evalExpr?, pure])))
  · rw [tickCompressValue, if_neg hz]
    have hret := evalExpr_cast_int (intType := .sint ⟨24, by decide⟩)
      (evalSignedQuotientCorrection (evalLocalValue (cfg := config) (evm := evm) ht) (evalLocalValue hs) hz)
    exact ExecBlock.consNormal
      (ExecStmt.iteFalse (by simpa only [decide_eq_false hz] using hcond) ExecBlock.nil)
      (ABlock.start.returns hret)

theorem tickCompressCall {f : Frame} {evm : EVM.State} {et es : Expr} {tick spacing : Int}
    (hf : f.contract = contract)
    (ht : evalExpr? config f evm et = .ok (.int tick))
    (hs : evalExpr? config f evm es = .ok (.int spacing)) (ret : Ident) :
    ExecStmt config f evm (.internalCall "TickBitmap_compress" [et, es] ret)
      (.ok (valueLocal f ret (.int (tickCompressValue tick spacing))) evm) := by
  apply internalCallFunctionReturn (argVals := [.int tick, .int spacing])
    (value := some [.int (tickCompressValue tick spacing)])
    (by simp only [evalExprs?, ht, hs, bind, EvalResult.bind, pure])
    (by rw [hf]; exact tickCompress_lookup) rfl
  exact tickCompressBody (store_get_self _ _ _)
    ((store_get_ne _ _ (by decide : ("tick" == "tickSpacing") = false)).trans (store_get_self _ _ _))

end Benchmarks.UniswapV4PoolManager
