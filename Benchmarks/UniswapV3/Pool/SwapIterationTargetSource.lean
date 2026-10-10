import Benchmarks.UniswapV3.Pool.SwapIterationSource
import Benchmarks.UniswapV3.Pool.SwapMemoryModel
import Benchmarks.UniswapV3.Pool.SwapStepModel
import Benchmarks.UniswapV3.Pool.FlashFeesSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def swapIterationChooseLimit (a : SwapArgs) (d : SwapIterationData) : Bool :=
  if a.zeroForOne then decide (d.priceNext.toNat < a.priceLimit.toNat)
  else decide (a.priceLimit.toNat < d.priceNext.toNat)

def swapIterationTarget (a : SwapArgs) (d : SwapIterationData) : UInt256 :=
  if swapIterationChooseLimit a d then a.priceLimit else d.priceNext

def swapIterationChooseExpr : Expr :=
  .ite (.var "zeroForOne")
    (.binary .lt (.field (.var "step") "sqrtPriceNextX96") (.var "sqrtPriceLimitX96"))
    (.binary .gt (.field (.var "step") "sqrtPriceNextX96") (.var "sqrtPriceLimitX96"))

def swapIterationTargetExpr : Expr :=
  .ite swapIterationChooseExpr (.var "sqrtPriceLimitX96") (.field (.var "step") "sqrtPriceNextX96")

def swapIterationStepArgs (v : UniswapV3PoolImmutables) (a : SwapArgs) (s : SwapStateData)
    (d : SwapIterationData) : SwapStepArgs :=
  {current := s.price, target := swapIterationTarget a d, liquidity := s.liquidity,
    remaining := s.remaining, fee := poolFeeWord v}

def swapIterationStepExprs : List Expr :=
  [.field (.var "state") "sqrtPriceX96", swapIterationTargetExpr,
    .field (.var "state") "liquidity", .field (.var "state") "amountSpecifiedRemaining",
    .cast (.immutable "fee") (.elem (.int (.uint ⟨24, by decide⟩)))]

theorem swapIterationTarget_fits (a : SwapArgs) (d : SwapIterationData)
    (ha : a.Fits) (hd : d.priceNext.toNat < 2 ^ 160) :
    (swapIterationTarget a d).toNat < 2 ^ 160 := by
  unfold swapIterationTarget
  split
  · exact ha.2
  · exact hd

theorem swapIterationStepArgs_fits (v : UniswapV3PoolImmutables) (a : SwapArgs)
    (s : SwapStateData) (d : SwapIterationData)
    (ha : a.Fits) (hs : s.Fits) (hd : d.priceNext.toNat < 2 ^ 160) :
    (swapIterationStepArgs v a s d).Fits := by
  exact ⟨hs.2.2.1, swapIterationTarget_fits a d ha hd, hs.2.2.2.2.2, hs.1,
    u256LandMaskToNatLtOfToNat (bits := 24) _ _ (by decide)⟩

theorem evalSwapIterationChoose {frame : Frame} {evm : EVM.State} (a : SwapArgs)
    (d : SwapIterationData) (hd : frame.locals.get? "step" = some d.value)
    (hz : frame.locals.get? "zeroForOne" = some (.bool a.zeroForOne))
    (hl : frame.locals.get? "sqrtPriceLimitX96" = some (.int (Int.ofNat a.priceLimit.toNat))) :
    evalExpr? config frame evm swapIterationChooseExpr =
      .ok (.bool (swapIterationChooseLimit a d)) := by
  have hp := evalExpr_structField (name := "sqrtPriceNextX96")
    (evalExpr_var_get (cfg := config) (evm := evm) hd) rfl
  have hez := evalExpr_var_get (cfg := config) (evm := evm) hz
  have hel := evalExpr_var_get (cfg := config) (evm := evm) hl
  rw [swapIterationChooseExpr, evalExpr?, hez]
  cases hdir : a.zeroForOne
  · simpa only [bind, EvalResult.bind, swapIterationChooseLimit, hdir,
      Bool.false_eq_true, if_false] using evalExpr_word_gt hp hel
  · have he := evalExpr_int_lt hp hel
    simpa only [bind, EvalResult.bind, swapIterationChooseLimit, hdir, if_true,
      Int.ofNat_eq_natCast, Int.ofNat_lt] using he

theorem evalSwapIterationTarget {frame : Frame} {evm : EVM.State} (a : SwapArgs)
    (d : SwapIterationData) (hd : frame.locals.get? "step" = some d.value)
    (hz : frame.locals.get? "zeroForOne" = some (.bool a.zeroForOne))
    (hl : frame.locals.get? "sqrtPriceLimitX96" = some (.int (Int.ofNat a.priceLimit.toNat))) :
    evalExpr? config frame evm swapIterationTargetExpr =
      .ok (.int (Int.ofNat (swapIterationTarget a d).toNat)) := by
  rw [swapIterationTargetExpr, evalExpr?, evalSwapIterationChoose a d hd hz hl]
  have hp := evalExpr_structField (name := "sqrtPriceNextX96")
    (evalExpr_var_get (cfg := config) (evm := evm) hd) rfl
  have hel := evalExpr_var_get (cfg := config) (evm := evm) hl
  cases he : swapIterationChooseLimit a d <;>
    simp only [bind, EvalResult.bind, hp, hel, swapIterationTarget, he,
      Bool.false_eq_true, if_false, if_true]

theorem evalSwapIterationStepArgs {frame : Frame} {evm : EVM.State}
    (v : UniswapV3PoolImmutables) (a : SwapArgs) (s : SwapStateData) (d : SwapIterationData)
    (hs : frame.locals.get? "state" = some s.value)
    (hd : frame.locals.get? "step" = some d.value)
    (hz : frame.locals.get? "zeroForOne" = some (.bool a.zeroForOne))
    (hl : frame.locals.get? "sqrtPriceLimitX96" = some (.int (Int.ofNat a.priceLimit.toNat)))
    (hf : frame = {contract := contract, locals := frame.locals, immutables := immStore v}) :
    evalExprs? config frame evm swapIterationStepExprs =
      .ok (swapIterationStepArgs v a s d).values := by
  have he := evalExpr_var_get (cfg := config) (evm := evm) hs
  have hp := evalExpr_structField (name := "sqrtPriceX96") he rfl
  have hliq := evalExpr_structField (name := "liquidity") he rfl
  have hrem := evalExpr_structField (name := "amountSpecifiedRemaining") he rfl
  have htar := evalSwapIterationTarget (evm := evm) a d hd hz hl
  have hfee := evalPoolFee v frame.locals evm
  rw [← hf] at hfee
  simp only [swapIterationStepExprs, evalExprs?, hp, htar, hliq, hrem, hfee,
    bind, EvalResult.bind, pure, swapIterationStepArgs, SwapStepArgs.values]

theorem swapIterationStepStmt : swapLoopBody[8]! =
    .internalCall "SwapMath_computeSwapStep" swapIterationStepExprs "__c4" := rfl

end Benchmarks.UniswapV3.Pool
