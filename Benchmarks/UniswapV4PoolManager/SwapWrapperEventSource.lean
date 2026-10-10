import Benchmarks.UniswapV4PoolManager.PoolSwapValues
import Benchmarks.UniswapV4PoolManager.BalanceDeltaComponentSource
import Benchmarks.UniswapV4PoolManager.ValueLocals

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

abbrev swapWrapperFunction : FunctionDecl := contract.functions[20]!

def swapWrapperEventFrame (f : Frame) (delta : UInt256) : Frame :=
  valueLocal (valueLocal f "__c2" (.int (balanceDeltaAmount0 delta))) "__c3"
    (.int (balanceDeltaAmount1 delta))

theorem swapWrapperEmitSource {f : Frame} {evm : State} {id fee delta : UInt256}
    {r : PoolSwapResultWords} (hi : f.locals.get? "id" = some (wordBytes32Value id))
    (h0 : f.locals.get? "__c2" = some (.int (balanceDeltaAmount0 delta)))
    (h1 : f.locals.get? "__c3" = some (.int (balanceDeltaAmount1 delta)))
    (he : f.locals.get? "swapFee" = some (.int (Int.ofNat fee.toNat)))
    (hr : f.locals.get? "result" = some (poolSwapResultValue r)) :
    ExecStmt config f evm swapWrapperFunction.body[9]! (.ok f evm) := by
  have hresult := evalLocalValue (cfg := config) (evm := evm) hr
  have hp := evalStructField hresult (field := "sqrtPriceX96") rfl
  have hl := evalStructField hresult (field := "liquidity") rfl
  have ht := evalStructField hresult (field := "tick") rfl
  apply ExecStmt.emit (vals := [wordBytes32Value id, .address evm.executionEnv.source,
    .int (balanceDeltaAmount0 delta), .int (balanceDeltaAmount1 delta), .int (Int.ofNat r.price.toNat),
    .int (Int.ofNat r.liquidity.toNat), .int (EVM.signed r.tick), .int (Int.ofNat fee.toNat)])
  change evalExprs? config f evm [.var "id", .env .caller, .var "__c2", .var "__c3",
    .field (.var "result") "sqrtPriceX96", .field (.var "result") "liquidity",
    .field (.var "result") "tick", .var "swapFee"] = _
  simp only [evalExprs?, evalLocalValue hi, evalLocalValue h0, evalLocalValue h1,
    evalLocalValue he, hp, hl, ht, evalExpr?, envValue, bind, EvalResult.bind, pure]

theorem swapWrapperEventSource {f : Frame} {evm : State} {id fee delta : UInt256}
    {r : PoolSwapResultWords} (hf : f.contract = contract)
    (hi : f.locals.get? "id" = some (wordBytes32Value id))
    (hd : f.locals.get? "delta" = some (.int (EVM.signed delta)))
    (he : f.locals.get? "swapFee" = some (.int (Int.ofNat fee.toNat)))
    (hr : f.locals.get? "result" = some (poolSwapResultValue r)) :
    ExecFuncBody config f evm (swapWrapperFunction.body.drop 7)
      (if evm.executionEnv.perm = false then .staticViolation else
        .returned (swapWrapperEventFrame f delta) evm (some [.int (EVM.signed delta)])) := by
  let f1 := valueLocal f "__c2" (.int (balanceDeltaAmount0 delta))
  let f2 := swapWrapperEventFrame f delta
  have h0 := balanceDeltaComponentCall (evm := evm) hf (evalLocalValue hd) false "__c2"
  have hd1 : f1.locals.get? "delta" = some (.int (EVM.signed delta)) :=
    (store_get_ne _ _ (by decide : ("__c2" == "delta") = false)).trans hd
  have h1 := balanceDeltaComponentCall (f := f1) (evm := evm) hf (evalLocalValue hd1) true "__c3"
  have hget (name : Ident) (h2 : ("__c2" == name) = false) (h3 : ("__c3" == name) = false) :
      f2.locals.get? name = f.locals.get? name := store_get_ne2 _ _ _ h2 h3
  have hemit := swapWrapperEmitSource (f := f2) (evm := evm)
    ((hget "id" (by decide) (by decide)).trans hi)
    ((store_get_ne _ _ (by decide : ("__c3" == "__c2") = false)).trans (store_get_self _ _ _))
    (store_get_self _ _ _) ((hget "swapFee" (by decide) (by decide)).trans he)
    ((hget "result" (by decide) (by decide)).trans hr)
  by_cases hp : evm.executionEnv.perm = false
  · rw [if_pos hp]
    cases hemit with
    | emit hargs => exact .execBlockStatic (ExecBlock.consNormal h0 (ExecBlock.consNormal h1
        (ExecBlock.consStatic (ExecStmt.emitStatic hargs hp))))
  · rw [if_neg hp]
    exact .execBlockRet (ExecBlock.consNormal h0 (ExecBlock.consNormal h1
      (ExecBlock.consNormal hemit (ABlock.start.returns
        (evalLocalValue ((hget "delta" (by decide) (by decide)).trans hd))))))

end Benchmarks.UniswapV4PoolManager
