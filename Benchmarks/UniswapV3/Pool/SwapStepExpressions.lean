import Benchmarks.UniswapV3.Pool.SwapStepModel
import Benchmarks.UniswapV3.Pool.LiquidityDeltaModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

def swapStepComplementExpr : Expr :=
  .cast (.binary .sub (.intLit 1000000) (.var "feePips"))
    (.elem (.int (.uint ⟨24, by decide⟩)))

def swapStepAbsExpr : Expr :=
  .cast (.cast (.binary .sub (.intLit 0) (.var "amountRemaining"))
    (.elem (.int (.sint ⟨256, by decide⟩)))) (.elem (.int (.uint ⟨256, by decide⟩)))

theorem evalSwapStepComplement (frame : Frame) (evm : EVM.State) (a : SwapStepArgs)
    (hf : frame.locals.get? "feePips" = some (.int (Int.ofNat a.fee.toNat))) :
    evalExpr? config frame evm swapStepComplementExpr =
      .ok (.int (Int.ofNat (swapStepComplement a).toNat)) := by
  have he := evalExpr_var_get (cfg := config) (evm := evm) hf
  simp only [swapStepComplementExpr, evalExpr?, he, evalBinaryOp?, castValue?,
    bind, EvalResult.bind, pure,
    normalizeUIntInt_mask ⟨24, by decide⟩ _ (UInt256.ofNat (2 ^ 24 - 1)) (by decide),
    wordOfInt_sub, wordOfInt_ofNat_toNat]
  rfl

theorem evalSwapStepRemainingWord (frame : Frame) (evm : EVM.State) (a : SwapStepArgs)
    (hr : frame.locals.get? "amountRemaining" = some (.int a.remaining)) :
    evalExpr? config frame evm
      (.cast (.var "amountRemaining") (.elem (.int (.uint ⟨256, by decide⟩)))) =
      .ok (.int (Int.ofNat (EVM.wordOfInt a.remaining).toNat)) := by
  have he := evalExpr_intCast (.uint ⟨256, by decide⟩)
    (evalExpr_var_get (cfg := config) (evm := evm) hr)
  simpa only [normalizeUInt256_int] using he

theorem evalSwapStepAbs (frame : Frame) (evm : EVM.State) (a : SwapStepArgs)
    (hr : frame.locals.get? "amountRemaining" = some (.int a.remaining)) :
    evalExpr? config frame evm swapStepAbsExpr =
      .ok (.int (Int.ofNat (swapStepAbsRemaining a).toNat)) := by
  have he := evalExpr_var_get (cfg := config) (evm := evm) hr
  simp only [swapStepAbsExpr, evalExpr?, he, evalBinaryOp?, castValue?, bind, EvalResult.bind,
    EvalResult.ofOption, pure, normalizeUInt_sint, normalizeUInt256_int, wordOfInt_sub]
  rfl

end Benchmarks.UniswapV3.Pool
