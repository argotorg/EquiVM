import Benchmarks.UniswapV4PoolManager.LocalStruct

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

structure PoolSwapStepWords where
  priceStart : UInt256
  tickNext : UInt256
  initialized : Bool
  priceNext : UInt256
  amountIn : UInt256
  amountOut : UInt256
  feeAmount : UInt256
  feeGrowthGlobal : UInt256

def poolSwapStepValue (s : PoolSwapStepWords) : Value :=
  .struct "StepComputations"
    [("sqrtPriceStartX96", .int (Int.ofNat s.priceStart.toNat)),
     ("tickNext", .int (EVM.signed s.tickNext)),
     ("initialized", .bool s.initialized),
     ("sqrtPriceNextX96", .int (Int.ofNat s.priceNext.toNat)),
     ("amountIn", .int (Int.ofNat s.amountIn.toNat)),
     ("amountOut", .int (Int.ofNat s.amountOut.toNat)),
     ("feeAmount", .int (Int.ofNat s.feeAmount.toNat)),
     ("feeGrowthGlobalX128", .int (Int.ofNat s.feeGrowthGlobal.toNat))]

theorem poolSwapStep_tick_eval {cfg : Config} {f : Frame} {evm : State} {s : PoolSwapStepWords}
    (hs : f.locals.get? "step" = some (poolSwapStepValue s)) :
    evalExpr? cfg f evm (.field (.var "step") "tickNext") = .ok (.int (EVM.signed s.tickNext)) :=
  evalStructField (evalLocalValue hs) rfl

theorem poolSwapStep_tick_assign {cfg : Config} {f : Frame} {evm : State} {s : PoolSwapStepWords}
    (hs : f.locals.get? "step" = some (poolSwapStepValue s)) (tick : UInt256) :
    assignStorageRef? cfg f evm .localVar {base := "step", steps := [.field "tickNext"]}
      (.int (EVM.signed tick)) =
      .ok ({f with locals := f.locals.insert "step" (poolSwapStepValue {s with tickNext := tick})}, evm) :=
  assignLocalField hs rfl rfl

end Benchmarks.UniswapV4PoolManager
