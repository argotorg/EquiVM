import Benchmarks.UniswapV3.Pool.SwapStepModel
import Benchmarks.UniswapV3.Pool.AmountDeltaRoutines

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

def swapStepDeltaCallArgs (a : SwapStepArgs) (input : Bool) (priceName : Ident) : List Expr :=
  [.var (if swapStepZeroForOne a then priceName else "sqrtRatioCurrentX96"),
   .var (if swapStepZeroForOne a then "sqrtRatioCurrentX96" else priceName),
   .var "liquidity", .boolLit input]

theorem evalSwapStepDeltaArgs (locals imms : Store) (evm : EVM.State) (a : SwapStepArgs)
    (price : UInt256) (input : Bool) (priceName : Ident)
    (hc : locals.get? "sqrtRatioCurrentX96" = some (.int (Int.ofNat a.current.toNat)))
    (hp : locals.get? priceName = some (.int (Int.ofNat price.toNat)))
    (hl : locals.get? "liquidity" = some (.int (Int.ofNat a.liquidity.toNat))) :
    evalExprs? config {contract := contract, locals := locals, immutables := imms} evm
      (swapStepDeltaCallArgs a input priceName) =
      .ok [.int (Int.ofNat (swapStepDeltaArgs a price input).sqrtA.toNat),
        .int (Int.ofNat (swapStepDeltaArgs a price input).sqrtB.toNat),
        .int (Int.ofNat a.liquidity.toNat), .bool input] := by
  let f : Frame := {contract := contract, locals := locals, immutables := imms}
  have ec := evalExpr_var_get (cfg := config) (frame := f) (evm := evm) hc
  have ep := evalExpr_var_get (cfg := config) (frame := f) (evm := evm) hp
  have el := evalExpr_var_get (cfg := config) (frame := f) (evm := evm) hl
  dsimp only [f] at ec ep el
  cases hz : swapStepZeroForOne a <;>
    simp only [swapStepDeltaCallArgs, swapStepDeltaArgs, hz, Bool.false_eq_true, if_false,
      if_true, evalExprs?, ec, ep, el, evalExpr?, bind, EvalResult.bind, pure]

theorem swapStepDeltaCallReturns (locals imms : Store) (evm : EVM.State) (a : SwapStepArgs)
    (price : UInt256) (input : Bool) (priceName retName : Ident)
    (hc : locals.get? "sqrtRatioCurrentX96" = some (.int (Int.ofNat a.current.toNat)))
    (hp : locals.get? priceName = some (.int (Int.ofNat price.toNat)))
    (hl : locals.get? "liquidity" = some (.int (Int.ofNat a.liquidity.toNat)))
    (hfit : (swapStepDeltaArgs a price input).Fits)
    (hv : amountDeltaValid (swapStepDeltaOne a input) (swapStepDeltaArgs a price input)) :
    ExecStmt config {contract := contract, locals := locals, immutables := imms} evm
      (.internalCall (amountDeltaName (swapStepDeltaOne a input))
        (swapStepDeltaCallArgs a input priceName) retName)
      (.ok {
        contract := contract
        immutables := imms
        locals := locals.insert retName (.int (Int.ofNat
          (amountDeltaResult (swapStepDeltaOne a input) (swapStepDeltaArgs a price input)).toNat))}
        evm) := by
  exact internalCallFunctionReturn (callee := amountDeltaFunction (swapStepDeltaOne a input))
    (calleeSolm := amountDeltaReturnFrame imms (swapStepDeltaOne a input)
      (swapStepDeltaArgs a price input))
    (locals := amountDeltaLocals (swapStepDeltaArgs a price input))
    (value := some [.int (Int.ofNat (amountDeltaResult (swapStepDeltaOne a input)
      (swapStepDeltaArgs a price input)).toNat)])
    (evalSwapStepDeltaArgs locals imms evm a price input priceName hc hp hl)
    (amountDeltaLookup _) (amountDeltaBind _ _)
    (amountDeltaReturns imms evm _ _ hfit hv)

theorem swapStepDeltaCallReverts (locals imms : Store) (evm : EVM.State) (a : SwapStepArgs)
    (price : UInt256) (input : Bool) (priceName retName : Ident)
    (hc : locals.get? "sqrtRatioCurrentX96" = some (.int (Int.ofNat a.current.toNat)))
    (hp : locals.get? priceName = some (.int (Int.ofNat price.toNat)))
    (hl : locals.get? "liquidity" = some (.int (Int.ofNat a.liquidity.toNat)))
    (hfit : (swapStepDeltaArgs a price input).Fits)
    (hv : ¬amountDeltaValid (swapStepDeltaOne a input) (swapStepDeltaArgs a price input)) :
    ExecStmt config {contract := contract, locals := locals, immutables := imms} evm
      (.internalCall (amountDeltaName (swapStepDeltaOne a input))
        (swapStepDeltaCallArgs a input priceName) retName) .reverted := by
  exact internalCallFunctionRevert (callee := amountDeltaFunction (swapStepDeltaOne a input))
    (locals := amountDeltaLocals (swapStepDeltaArgs a price input))
    (evalSwapStepDeltaArgs locals imms evm a price input priceName hc hp hl)
    (amountDeltaLookup _) (amountDeltaBind _ _)
    (amountDeltaReverts imms evm _ _ hfit hv)

end Benchmarks.UniswapV3.Pool
