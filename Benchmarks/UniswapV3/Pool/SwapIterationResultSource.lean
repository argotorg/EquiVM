import Benchmarks.UniswapV3.Pool.SwapIterationSource
import Benchmarks.UniswapV3.Pool.SwapStateSource
import Benchmarks.UniswapV3.Pool.SourceTuples

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def swapStateFrame (frame : Frame) (s : SwapStateData) : Frame :=
  {frame with locals := frame.locals.insert "state" s.value}

def swapIterationResultData (d : SwapIterationData) (amountIn amountOut fee : UInt256) :
    SwapIterationData :=
  {d with amountIn := amountIn, amountOut := amountOut, feeAmount := fee}

def swapIterationResultFrame (frame : Frame) (s : SwapStateData) (d : SwapIterationData)
    (price amountIn amountOut fee : UInt256) : Frame :=
  swapIterationFrame
    (swapIterationFrame
      (swapIterationFrame (swapStateFrame frame {s with price := price})
        {d with amountIn := amountIn})
      {d with amountIn := amountIn, amountOut := amountOut})
    (swapIterationResultData d amountIn amountOut fee)

theorem swapIterationResultSource {frame : Frame} {evm : EVM.State}
    (s : SwapStateData) (d : SwapIterationData) (price amountIn amountOut fee : UInt256)
    (hs : frame.locals.get? "state" = some s.value)
    (hd : frame.locals.get? "step" = some d.value)
    (hr : frame.locals.get? "__c4" = some (.tuple [.int (Int.ofNat price.toNat),
      .int (Int.ofNat amountIn.toNat), .int (Int.ofNat amountOut.toNat),
      .int (Int.ofNat fee.toNat)])) :
    ExecBlock config frame evm ((swapLoopBody.drop 9).take 4)
      (.ok (swapIterationResultFrame frame s d price amountIn amountOut fee) evm) := by
  let f1 := swapStateFrame frame {s with price := price}
  let f2 := swapIterationFrame f1 {d with amountIn := amountIn}
  let f3 := swapIterationFrame f2 {d with amountIn := amountIn, amountOut := amountOut}
  have hr1 : f1.locals.get? "__c4" = some (.tuple [.int (Int.ofNat price.toNat),
      .int (Int.ofNat amountIn.toNat), .int (Int.ofNat amountOut.toNat),
      .int (Int.ofNat fee.toNat)]) := by
    simpa only [f1, swapStateFrame, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
      using hr
  have hd1 : f1.locals.get? "step" = some d.value := by
    simpa only [f1, swapStateFrame, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
      using hd
  have hr2 : f2.locals.get? "__c4" = some (.tuple [.int (Int.ofNat price.toNat),
      .int (Int.ofNat amountIn.toNat), .int (Int.ofNat amountOut.toNat),
      .int (Int.ofNat fee.toNat)]) := by
    simpa only [f2, swapIterationFrame, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
      using hr1
  have hr3 : f3.locals.get? "__c4" = some (.tuple [.int (Int.ofNat price.toNat),
      .int (Int.ofNat amountIn.toNat), .int (Int.ofNat amountOut.toNat),
      .int (Int.ofNat fee.toNat)]) := by
    simpa only [f3, swapIterationFrame, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
      using hr2
  have h1 : ExecStmt config frame evm swapLoopBody[9]! (.ok f1 evm) :=
    ExecStmt.assign (evalExpr_tupleGet (evalExpr_var_get hr) rfl)
      (assignLocalField_frame hs rfl rfl)
  have h2 : ExecStmt config f1 evm swapLoopBody[10]! (.ok f2 evm) :=
    ExecStmt.assign (evalExpr_tupleGet (evalExpr_var_get hr1) rfl)
      (assignLocalField_frame hd1 rfl rfl)
  have h3 : ExecStmt config f2 evm swapLoopBody[11]! (.ok f3 evm) :=
    ExecStmt.assign (evalExpr_tupleGet (evalExpr_var_get hr2) rfl)
      (assignLocalField_frame Std.HashMap.getElem?_insert_self rfl rfl)
  have h4 : ExecStmt config f3 evm swapLoopBody[12]!
      (.ok (swapIterationResultFrame frame s d price amountIn amountOut fee) evm) :=
    ExecStmt.assign (evalExpr_tupleGet (evalExpr_var_get hr3) rfl)
      (assignLocalField_frame Std.HashMap.getElem?_insert_self rfl rfl)
  exact ExecBlock.consNormal h1 (ExecBlock.consNormal h2
    (ExecBlock.consNormal h3 (ExecBlock.consNormal h4 ExecBlock.nil)))

end Benchmarks.UniswapV3.Pool
