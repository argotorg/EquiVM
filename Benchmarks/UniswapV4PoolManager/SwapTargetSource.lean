import Benchmarks.UniswapV4PoolManager.SwapTargetWords
import Benchmarks.UniswapV4PoolManager.WordConditionalSource
import Benchmarks.UniswapV4PoolManager.WordBorrowSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

abbrev swapTargetFunction : FunctionDecl := contract.functions[105]!
theorem swapTarget_lookup : lookupCallable? contract "SwapMath_getSqrtPriceTarget" =
    some swapTargetFunction.toCallable := rfl

def swapTargetBranchStmts (zeroForOne : Bool) : List Stmt :=
  [.return [.ite (.binary (if zeroForOne then .lt else .gt) (.var "sqrtPriceNextX96") (.var "sqrtPriceLimitX96"))
    (.var "sqrtPriceLimitX96") (.var "sqrtPriceNextX96")]]

theorem swapTarget_body_eq : swapTargetFunction.body =
    .ite (.var "zeroForOne") (swapTargetBranchStmts true) [] :: swapTargetBranchStmts false := rfl

theorem swapTargetBranchSource {f : Frame} {evm : EVM.State} {next limit : UInt256}
    (zeroForOne : Bool)
    (hn : f.locals.get? "sqrtPriceNextX96" = some (.int (Int.ofNat next.toNat)))
    (hl : f.locals.get? "sqrtPriceLimitX96" = some (.int (Int.ofNat limit.toNat))) :
    ExecBlock config f evm (swapTargetBranchStmts zeroForOne)
      (.returned f evm (some [.int (Int.ofNat (swapTargetWord zeroForOne next limit).toNat)])) := by
  cases zeroForOne with
  | false =>
    simp only [swapTargetBranchStmts, swapTargetWord, Bool.false_eq_true, if_false]
    exact ABlock.start.returns (evalWordConditional (p := limit.toNat < next.toNat)
      (evalWordGt (evalLocalValue hn) (evalLocalValue hl)) (evalLocalValue hl) (evalLocalValue hn))
  | true =>
    simp only [swapTargetBranchStmts, swapTargetWord, if_true]
    exact ABlock.start.returns (evalWordConditional (p := next.toNat < limit.toNat)
      (evalWordLt (evalLocalValue hn) (evalLocalValue hl)) (evalLocalValue hl) (evalLocalValue hn))

theorem swapTargetBody {f : Frame} {evm : EVM.State} {next limit : UInt256}
    (zeroForOne : Bool)
    (hb : f.locals.get? "zeroForOne" = some (.bool zeroForOne))
    (hn : f.locals.get? "sqrtPriceNextX96" = some (.int (Int.ofNat next.toNat)))
    (hl : f.locals.get? "sqrtPriceLimitX96" = some (.int (Int.ofNat limit.toNat))) :
    ExecFuncBody config f evm swapTargetFunction.body
      (.returned f evm (some [.int (Int.ofNat (swapTargetWord zeroForOne next limit).toNat)])) := by
  rw [swapTarget_body_eq]
  apply ExecFuncBody.execBlockRet
  cases zeroForOne with
  | false =>
    exact ExecBlock.consNormal (ExecStmt.iteFalse (evalLocalValue hb) ExecBlock.nil) (swapTargetBranchSource false hn hl)
  | true =>
    exact ExecBlock.consReturn (ExecStmt.iteTrue (evalLocalValue hb) (swapTargetBranchSource true hn hl))

theorem swapTargetCall {f : Frame} {evm : EVM.State} {next limit : UInt256} {eb en el : Expr}
    (zeroForOne : Bool) (hc : f.contract = contract)
    (hb : evalExpr? config f evm eb = .ok (.bool zeroForOne))
    (hn : evalExpr? config f evm en = .ok (.int (Int.ofNat next.toNat)))
    (hl : evalExpr? config f evm el = .ok (.int (Int.ofNat limit.toNat))) (ret : Ident) :
    ExecStmt config f evm (.internalCall "SwapMath_getSqrtPriceTarget" [eb, en, el] ret)
      (.ok (wordLocal f ret (swapTargetWord zeroForOne next limit)) evm) := by
  let fc : Frame := {f with locals := ((((∅ : Store).insert "sqrtPriceLimitX96" (.int (Int.ofNat limit.toNat))).insert
    "sqrtPriceNextX96" (.int (Int.ofNat next.toNat))).insert "zeroForOne" (.bool zeroForOne))}
  have hargs : evalExprs? config f evm [eb, en, el] =
      .ok [.bool zeroForOne, .int (Int.ofNat next.toNat), .int (Int.ofNat limit.toNat)] := by
    simp only [evalExprs?, hb, hn, hl, bind, EvalResult.bind, pure]
  have hlookup : lookupCallable? f.contract "SwapMath_getSqrtPriceTarget" = some swapTargetFunction.toCallable := by
    rw [hc]; exact swapTarget_lookup
  have hbody := swapTargetBody (f := fc) (evm := evm) zeroForOne (store_get_self _ _ _)
    ((store_get_ne _ _ (by decide : ("zeroForOne" == "sqrtPriceNextX96") = false)).trans (store_get_self _ _ _))
    ((store_get_ne2 _ _ _ (by decide : ("sqrtPriceNextX96" == "sqrtPriceLimitX96") = false)
      (by decide : ("zeroForOne" == "sqrtPriceLimitX96") = false)).trans (store_get_self _ _ _))
  exact internalCallFunctionReturn hargs hlookup rfl hbody

end Benchmarks.UniswapV4PoolManager
