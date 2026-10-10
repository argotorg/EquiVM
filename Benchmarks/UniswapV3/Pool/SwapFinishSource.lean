import Benchmarks.UniswapV3.Pool.SwapPayment
import Benchmarks.UniswapV3.Pool.Slot0Storage
import Benchmarks.UniswapV3.Pool.TupleReturn

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem swapFinishSource (frame : Frame) (evm : EVM.State) (recipient : AccountAddress)
    (amount0 amount1 : Int) (s : SwapStateData)
    (hf : frame.contract = contract)
    (hr : frame.locals.get? "recipient" = some (.address recipient))
    (h0 : frame.locals.get? "amount0" = some (.int amount0))
    (h1 : frame.locals.get? "amount1" = some (.int amount1))
    (hs : frame.locals.get? "state" = some s.value)
    (hslot : frame.locals.get? "slot0" = none) :
    ExecBlock config frame evm (swapTransition.body.drop 19)
      (.returned frame (storeSlot0Unlocked evm true) (some [.int amount0, .int amount1])) := by
  have hp : evalExpr? config frame evm (.field (.var "state") "sqrtPriceX96") =
      .ok (.int (Int.ofNat s.price.toNat)) :=
    evalExpr_structField (evalExpr_var_get hs) rfl
  have hl : evalExpr? config frame evm (.field (.var "state") "liquidity") =
      .ok (.int (Int.ofNat s.liquidity.toNat)) :=
    evalExpr_structField (evalExpr_var_get hs) rfl
  have ht : evalExpr? config frame evm (.field (.var "state") "tick") = .ok (.int s.tick) :=
    evalExpr_structField (evalExpr_var_get hs) rfl
  refine ExecBlock.consNormal (ExecStmt.emit (vals :=
    [.address evm.executionEnv.source, .address recipient, .int amount0, .int amount1,
      .int (Int.ofNat s.price.toNat), .int (Int.ofNat s.liquidity.toNat), .int s.tick]) ?_) ?_
  · simp only [evalExprs?, hp, hl, ht, evalExpr_var_get hr, evalExpr_var_get h0,
      evalExpr_var_get h1, evalExpr?, envValue, bind, EvalResult.bind, pure]
  have hass : assignStorageRef? config frame evm .storage ⟨"slot0", [.field "unlocked"]⟩
      (.bool true) = .ok (frame, storeSlot0Unlocked evm true) := by
    rw [frame_eq_of_parts hf rfl]
    exact assignSlot0Unlocked evm frame.locals frame.immutables true hslot
  refine ExecBlock.consNormal (ExecStmt.assign (by simp only [evalExpr?, pure]) hass) ?_
  exact ExecBlock.consReturn (ExecStmt.return (by
    simp only [evalExprs?, evalExpr_var_get h0, evalExpr_var_get h1,
      bind, EvalResult.bind, pure]))

theorem swapReturnEncoding (amount0 amount1 : Int)
    (h0 : -(2 ^ 255 : Int) ≤ amount0 ∧ amount0 < 2 ^ 255)
    (h1 : -(2 ^ 255 : Int) ≤ amount1 ∧ amount1 < 2 ^ 255) :
    encodeReturnValues? swapTransition.returnType [.int amount0, .int amount1] =
      some ((EVM.wordOfInt amount0).toByteArray ++ (EVM.wordOfInt amount1).toByteArray) := by
  have h := staticWordsReturnEncoding
    [(.elem (.int (.sint ⟨256, by decide⟩)), .int amount0, EVM.wordOfInt amount0),
     (.elem (.int (.sint ⟨256, by decide⟩)), .int amount1, EVM.wordOfInt amount1)] 64
    (by simp only [List.map_cons, List.map_nil, abiTupleHeadSize?, staticABIEncodedSize?,
      isDynamicABIType, Bool.false_eq_true, if_false, bind, Option.bind])
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> rfl)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact encodeABIValue_sint_of_bounds ⟨256, by decide⟩ amount0 h0
      · exact encodeABIValue_sint_of_bounds ⟨256, by decide⟩ amount1 h1)
  simpa only [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.toByteArray_append, word_toBytesBE_toByteArray_eq_toByteArray] using h

end Benchmarks.UniswapV3.Pool
