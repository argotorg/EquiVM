import Benchmarks.UniswapV4PoolManager.PoolSwapInputsSource
import Benchmarks.UniswapV4PoolManager.Slot0TickSource
import Benchmarks.UniswapV4PoolManager.PoolLiquidityStorage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolSwapInitialResult (packed liquidity : UInt256) : PoolSwapResultWords :=
  ⟨slot0SqrtPriceWord packed, slot0TickWord packed, liquidity⟩

def poolSwapResultInitFrame (f : Frame) (packed liquidity specified : UInt256) : Frame :=
  let f1 := valueLocal f "amountSpecifiedRemaining" (.int (EVM.signed specified))
  let f2 := valueLocal f1 "amountCalculated" (.int 0)
  let f3 := wordLocal f2 "__c4" (slot0SqrtPriceWord packed)
  let f4 := valueLocal f3 "result" (poolSwapResultValue {poolSwapZeroResult with price := slot0SqrtPriceWord packed})
  let f5 := valueLocal f4 "__c5" (.int (EVM.signed (slot0TickWord packed)))
  let f6 := valueLocal f5 "result" (poolSwapResultValue (poolSwapInitialResult packed ⟨0⟩))
  valueLocal f6 "result" (poolSwapResultValue (poolSwapInitialResult packed liquidity))

theorem poolSwapResultInitFrame_contract (f : Frame) (packed liquidity specified : UInt256) :
    (poolSwapResultInitFrame f packed liquidity specified).contract = f.contract := by
  simp only [poolSwapResultInitFrame, valueLocal_contract, wordLocal_contract]

theorem poolSwapResultInitFrame_get (f : Frame) (packed liquidity specified : UInt256) (key : Ident)
    (hr : ("amountSpecifiedRemaining" == key) = false) (hc : ("amountCalculated" == key) = false)
    (h4 : ("__c4" == key) = false) (h5 : ("__c5" == key) = false) (hresult : ("result" == key) = false) :
    (poolSwapResultInitFrame f packed liquidity specified).locals.get? key = f.locals.get? key := by
  simp only [poolSwapResultInitFrame, valueLocal_get, wordLocal_get, hr, hc, h4, h5, hresult,
    Bool.false_eq_true, if_false]

theorem poolSwapResultInitSource {f : Frame} {evm : State} {id packed : UInt256} {p : PoolSwapParamsWords}
    (hf : f.contract = contract) (hs : f.locals.get? "self" = some (poolRefValue id))
    (hp : f.locals.get? "params" = some (poolSwapParamsValue p))
    (hslot : f.locals.get? "slot0Start" = some (wordBytes32Value packed))
    (hr : f.locals.get? "result" = some (poolSwapResultValue poolSwapZeroResult)) :
    ExecBlock config f evm ((poolSwapFunction.body.drop 11).take 7)
      (.ok (poolSwapResultInitFrame f packed (poolLiquidityWord evm id) p.amountSpecified) evm) := by
  let f1 := valueLocal f "amountSpecifiedRemaining" (.int (EVM.signed p.amountSpecified))
  let f2 := valueLocal f1 "amountCalculated" (.int 0)
  let f3 := wordLocal f2 "__c4" (slot0SqrtPriceWord packed)
  let f4 := valueLocal f3 "result" (poolSwapResultValue {poolSwapZeroResult with price := slot0SqrtPriceWord packed})
  let f5 := valueLocal f4 "__c5" (.int (EVM.signed (slot0TickWord packed)))
  let f6 := valueLocal f5 "result" (poolSwapResultValue (poolSwapInitialResult packed ⟨0⟩))
  have h0 : ExecStmt config f evm poolSwapFunction.body[11]! (.ok f1 evm) :=
    ExecStmt.letDecl (evalStructField (field := "amountSpecified") (evalLocalValue hp) rfl)
  have h1 : ExecStmt config f1 evm poolSwapFunction.body[12]! (.ok f2 evm) :=
    ExecStmt.letDecl (by simp only [evalExpr?, pure])
  have hslot2 : f2.locals.get? "slot0Start" = some (wordBytes32Value packed) :=
    (store_get_ne2 _ _ _ (by decide : ("amountSpecifiedRemaining" == "slot0Start") = false)
      (by decide : ("amountCalculated" == "slot0Start") = false)).trans hslot
  have h2 : ExecStmt config f2 evm poolSwapFunction.body[13]! (.ok f3 evm) :=
    slot0SqrtCall (f := f2) hf (evalLocalValue hslot2) "__c4"
  have hr3 : f3.locals.get? "result" = some (poolSwapResultValue poolSwapZeroResult) :=
    (store_get_ne3 _ _ _ _ (by decide : ("amountSpecifiedRemaining" == "result") = false)
      (by decide : ("amountCalculated" == "result") = false) (by decide : ("__c4" == "result") = false)).trans hr
  have h3 : ExecStmt config f3 evm poolSwapFunction.body[14]! (.ok f4 evm) :=
    ExecStmt.assign (evalLocalValue (store_get_self _ _ _)) (assignLocalField hr3 rfl rfl)
  have hslot4 : f4.locals.get? "slot0Start" = some (wordBytes32Value packed) :=
    (store_get_ne2 _ _ _ (by decide : ("__c4" == "slot0Start") = false)
      (by decide : ("result" == "slot0Start") = false)).trans hslot2
  have h4 : ExecStmt config f4 evm poolSwapFunction.body[15]! (.ok f5 evm) :=
    slot0TickCall (f := f4) hf (evalLocalValue hslot4) "__c5"
  have hr5 : f5.locals.get? "result" = some (poolSwapResultValue {poolSwapZeroResult with price := slot0SqrtPriceWord packed}) :=
    (store_get_ne _ _ (by decide : ("__c5" == "result") = false)).trans (store_get_self _ _ _)
  have h5 : ExecStmt config f5 evm poolSwapFunction.body[16]! (.ok f6 evm) :=
    ExecStmt.assign (evalLocalValue (store_get_self _ _ _)) (assignLocalField hr5 rfl rfl)
  have hs6 : f6.locals.get? "self" = some (poolRefValue id) := by
    simp only [f6, f5, f4, f3, f2, f1, valueLocal_get, wordLocal_get, beq_iff_eq, String.reduceEq,
      if_false, hs]
  have h6 : ExecStmt config f6 evm poolSwapFunction.body[17]!
      (.ok (poolSwapResultInitFrame f packed (poolLiquidityWord evm id) p.amountSpecified) evm) :=
    ExecStmt.assign (poolLiquidity_read hs6) (assignLocalField (store_get_self _ _ _) rfl rfl)
  exact ExecBlock.consNormal h0 (ExecBlock.consNormal h1 (ExecBlock.consNormal h2
    (ExecBlock.consNormal h3 (ExecBlock.consNormal h4 (ExecBlock.consNormal h5 (execBlock_singleton h6))))))

end Benchmarks.UniswapV4PoolManager
