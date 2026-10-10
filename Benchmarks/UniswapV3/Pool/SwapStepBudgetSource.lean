import Benchmarks.UniswapV3.Pool.SwapStepPrefix
import Benchmarks.UniswapV3.Pool.SwapStepExpressions

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

def swapStepPriceBranch (input : Bool) : List Stmt :=
  match swapStepFunction.body[6]! with
  | .ite _ yes no => if input then yes else no
  | _ => []

def swapStepBudgetArgs : List Expr :=
  [.cast (.var "amountRemaining") (.elem (.int (.uint ⟨256, by decide⟩))),
   swapStepComplementExpr, .intLit 1000000]

noncomputable def swapStepBudgetFrame (imms : Store) (a : SwapStepArgs) : Frame :=
  {swapStepReadyFrame imms a with
    locals := (swapStepReadyFrame imms a).locals.insert "amountRemainingLessFee"
      (.int (Int.ofNat (fullMathResult (EVM.wordOfInt a.remaining)
        (swapStepComplement a) (UInt256.ofNat 1000000)).toNat))}

theorem evalSwapStepBudgetArgs (imms : Store) (evm : EVM.State) (a : SwapStepArgs) :
    evalExprs? config (swapStepReadyFrame imms a) evm swapStepBudgetArgs =
      .ok [.int (Int.ofNat (EVM.wordOfInt a.remaining).toNat),
        .int (Int.ofNat (swapStepComplement a).toNat),
        .int (Int.ofNat (UInt256.ofNat 1000000).toNat)] := by
  rw [show Int.ofNat (UInt256.ofNat 1000000).toNat = 1000000 from by decide]
  have hr := evalSwapStepRemainingWord (swapStepReadyFrame imms a) evm a
    (swapStepReadyGet imms a).2.2.2.1
  have hf := evalSwapStepComplement (swapStepReadyFrame imms a) evm a
    (swapStepReadyGet imms a).2.2.2.2.1
  simp only [swapStepBudgetArgs, evalExprs?, hr, hf, evalExpr?, bind, EvalResult.bind, pure]

theorem swapStepBudgetSource (imms : Store) (evm : EVM.State) (a : SwapStepArgs)
    (hv : fullMathValid (EVM.wordOfInt a.remaining) (swapStepComplement a)
      (UInt256.ofNat 1000000)) :
    ExecStmt config (swapStepReadyFrame imms a) evm (swapStepPriceBranch true)[0]!
      (.ok (swapStepBudgetFrame imms a) evm) := by
  exact internalCallFunctionReturn (callee := fullMathFunction)
    (calleeSolm := fullMathProductFrame imms (EVM.wordOfInt a.remaining)
      (swapStepComplement a) (UInt256.ofNat 1000000))
    (locals := fullMathLocals (EVM.wordOfInt a.remaining)
      (swapStepComplement a) (UInt256.ofNat 1000000))
    (value := some [.int (Int.ofNat (fullMathResult (EVM.wordOfInt a.remaining)
      (swapStepComplement a) (UInt256.ofNat 1000000)).toNat)])
    (evalSwapStepBudgetArgs imms evm a) fullMathLookup (fullMathBind _ _ _)
    (fullMathReturns imms evm _ _ _ hv)

theorem swapStepBudgetReverts (imms : Store) (evm : EVM.State) (a : SwapStepArgs)
    (hv : ¬fullMathValid (EVM.wordOfInt a.remaining) (swapStepComplement a)
      (UInt256.ofNat 1000000)) :
    ExecStmt config (swapStepReadyFrame imms a) evm (swapStepPriceBranch true)[0]!
      .reverted := by
  exact internalCallFunctionRevert (callee := fullMathFunction)
    (locals := fullMathLocals (EVM.wordOfInt a.remaining)
      (swapStepComplement a) (UInt256.ofNat 1000000))
    (evalSwapStepBudgetArgs imms evm a) fullMathLookup (fullMathBind _ _ _)
    (fullMathReverts imms evm _ _ _ hv)

end Benchmarks.UniswapV3.Pool
