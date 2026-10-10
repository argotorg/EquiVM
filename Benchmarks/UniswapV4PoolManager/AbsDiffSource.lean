import Benchmarks.UniswapV4PoolManager.AbsDiffWords
import Benchmarks.UniswapV4PoolManager.WordLocals
import Benchmarks.UniswapV4PoolManager.PoolCheckSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

abbrev absDiffFunction : FunctionDecl := contract.functions[109]!
theorem absDiff_lookup : lookupCallable? contract "SqrtPriceMath_absDiff" =
    some absDiffFunction.toCallable := rfl

theorem absDiffBody {f : Frame} {evm : EVM.State} {a b : UInt256}
    (ha : f.locals.get? "a" = some (.int (Int.ofNat a.toNat)))
    (hb : f.locals.get? "b" = some (.int (Int.ofNat b.toNat))) :
    ExecFuncBody config f evm absDiffFunction.body
      (.returned f evm (some [.int (Int.ofNat (absDiffWord a b).toNat)])) := by
  have hea := evalLocalValue (cfg := config) (f := f) (evm := evm) ha
  have heb := evalLocalValue (cfg := config) (f := f) (evm := evm) hb
  have hg := naturalGeSource hea heb
  apply ExecFuncBody.execBlockRet
  apply ABlock.start.returns
  by_cases ho : b.toNat ≤ a.toNat
  · have he := subSourceOk hea heb ho
    simpa only [evalExpr?, hg, decide_eq_true ho, bind, EvalResult.bind, if_true,
      absDiffWord, if_pos ho] using he
  · have he := subSourceOk heb hea (by omega)
    simpa only [evalExpr?, hg, decide_eq_false ho, bind, EvalResult.bind, Bool.false_eq_true,
      if_false, absDiffWord, if_neg ho] using he

theorem absDiffCall {f : Frame} {evm : EVM.State} {a b : UInt256} {ea eb : Expr}
    (hf : f.contract = contract)
    (ha : evalExpr? config f evm ea = .ok (.int (Int.ofNat a.toNat)))
    (hb : evalExpr? config f evm eb = .ok (.int (Int.ofNat b.toNat))) (ret : Ident) :
    ExecStmt config f evm (.internalCall "SqrtPriceMath_absDiff" [ea, eb] ret)
      (.ok (wordLocal f ret (absDiffWord a b)) evm) := by
  let fc : Frame := {f with locals := (((∅ : Store).insert "b" (.int (Int.ofNat b.toNat))).insert
    "a" (.int (Int.ofNat a.toNat)))}
  have hbody := absDiffBody (f := fc) (evm := evm) (store_get_self _ _ _)
    ((store_get_ne _ _ (by decide : ("a" == "b") = false)).trans (store_get_self _ _ _))
  have hargs : evalExprs? config f evm [ea, eb] =
      .ok [.int (Int.ofNat a.toNat), .int (Int.ofNat b.toNat)] := by
    simp only [evalExprs?, ha, hb, bind, EvalResult.bind, pure]
  exact internalCallFunctionReturn hargs (by rw [hf]; exact absDiff_lookup) rfl hbody

end Benchmarks.UniswapV4PoolManager
