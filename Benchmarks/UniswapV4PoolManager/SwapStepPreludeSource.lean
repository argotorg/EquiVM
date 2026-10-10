import Benchmarks.UniswapV4PoolManager.SwapStepWords
import Benchmarks.UniswapV4PoolManager.ValueLocals

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

abbrev swapStepFunction : FunctionDecl := contract.functions[104]!
theorem swapStep_lookup : lookupCallable? contract "SwapMath_computeSwapStep" =
    some swapStepFunction.toCallable := rfl

def swapStepPreludeStmts : List Stmt :=
  [.letDecl "sqrtPriceNextX96" (some (.elem (.int (.uint ⟨160, by decide⟩)))) (.intLit 0),
   .letDecl "amountIn" (some abiUInt256) (.intLit 0),
   .letDecl "amountOut" (some abiUInt256) (.intLit 0),
   .letDecl "feeAmount" (some abiUInt256) (.intLit 0),
   .letDecl "_feePips" (some abiUInt256) (.var "feePips"),
   .letDecl "zeroForOne" (some (.elem .bool))
     (.binary .ge (.var "sqrtPriceCurrentX96") (.var "sqrtPriceTargetX96")),
   .letDecl "exactIn" (some (.elem .bool)) (.binary .lt (.var "amountRemaining") (.intLit 0))]

theorem swapStepPrelude_eq : swapStepFunction.body.take 7 = swapStepPreludeStmts := rfl

def swapStepPreludeWordsFrame (f : Frame) (fee : UInt256) : Frame :=
  wordLocal (wordLocal (wordLocal (wordLocal (wordLocal f "sqrtPriceNextX96" ⟨0⟩)
    "amountIn" ⟨0⟩) "amountOut" ⟨0⟩) "feeAmount" ⟨0⟩) "_feePips" fee

def swapStepPreludeFrame (f : Frame) (price target remaining fee : UInt256) : Frame :=
  valueLocal (valueLocal (swapStepPreludeWordsFrame f fee) "zeroForOne" (.bool (swapStepDirection price target)))
    "exactIn" (.bool (swapStepExactInput remaining))

theorem swapStepPreludeFrame_contract (f : Frame) (price target remaining fee : UInt256) :
    (swapStepPreludeFrame f price target remaining fee).contract = f.contract := by
  simp only [swapStepPreludeFrame, valueLocal_contract, swapStepPreludeWordsFrame, wordLocal_contract]

theorem swapStepPreludeFrame_get (f : Frame) (price target remaining fee : UInt256) (name : Ident) :
    (swapStepPreludeFrame f price target remaining fee).locals.get? name =
      if "exactIn" == name then some (.bool (swapStepExactInput remaining))
      else if "zeroForOne" == name then some (.bool (swapStepDirection price target))
      else (swapStepPreludeWordsFrame f fee).locals.get? name := by
  simp only [swapStepPreludeFrame, valueLocal_get]

theorem swapStepPreludeSource {f : Frame} {evm : EVM.State} {price target remaining fee : UInt256}
    (hp : f.locals.get? "sqrtPriceCurrentX96" = some (.int (Int.ofNat price.toNat)))
    (ht : f.locals.get? "sqrtPriceTargetX96" = some (.int (Int.ofNat target.toNat)))
    (hr : f.locals.get? "amountRemaining" = some (.int (EVM.signed remaining)))
    (hf : f.locals.get? "feePips" = some (.int (Int.ofNat fee.toNat))) :
    ExecBlock config f evm (swapStepFunction.body.take 7)
      (.ok (swapStepPreludeFrame f price target remaining fee) evm) := by
  rw [swapStepPrelude_eq]
  let f1 := wordLocal f "sqrtPriceNextX96" ⟨0⟩
  let f2 := wordLocal f1 "amountIn" ⟨0⟩
  let f3 := wordLocal f2 "amountOut" ⟨0⟩
  let f4 := wordLocal f3 "feeAmount" ⟨0⟩
  let f5 := swapStepPreludeWordsFrame f fee
  let f6 := valueLocal f5 "zeroForOne" (.bool (swapStepDirection price target))
  have h0 : ExecStmt config f evm swapStepPreludeStmts[0]! (.ok f1 evm) :=
    ExecStmt.letDecl (by simp only [evalExpr?, pure]; rfl)
  have h1 : ExecStmt config f1 evm swapStepPreludeStmts[1]! (.ok f2 evm) :=
    ExecStmt.letDecl (by simp only [evalExpr?, pure]; rfl)
  have h2 : ExecStmt config f2 evm swapStepPreludeStmts[2]! (.ok f3 evm) :=
    ExecStmt.letDecl (by simp only [evalExpr?, pure]; rfl)
  have h3 : ExecStmt config f3 evm swapStepPreludeStmts[3]! (.ok f4 evm) :=
    ExecStmt.letDecl (by simp only [evalExpr?, pure]; rfl)
  have hf4 : f4.locals.get? "feePips" = some (.int (Int.ofNat fee.toNat)) := by
    simp only [f4, f3, f2, f1, wordLocal_get, beq_iff_eq, String.reduceEq, ↓reduceIte, hf]
  have h4 : ExecStmt config f4 evm swapStepPreludeStmts[4]! (.ok f5 evm) :=
    ExecStmt.letDecl (evalLocalValue hf4)
  have hp5 : f5.locals.get? "sqrtPriceCurrentX96" = some (.int (Int.ofNat price.toNat)) := by
    simp only [f5, swapStepPreludeWordsFrame, wordLocal_get, beq_iff_eq, String.reduceEq, ↓reduceIte, hp]
  have ht5 : f5.locals.get? "sqrtPriceTargetX96" = some (.int (Int.ofNat target.toNat)) := by
    simp only [f5, swapStepPreludeWordsFrame, wordLocal_get, beq_iff_eq, String.reduceEq, ↓reduceIte, ht]
  have hge := naturalGeSource (evalLocalValue (cfg := config) (evm := evm) hp5) (evalLocalValue ht5)
  have h5 : ExecStmt config f5 evm swapStepPreludeStmts[5]! (.ok f6 evm) := by
    change ExecStmt config f5 evm
      (.letDecl "zeroForOne" (some (.elem .bool))
        (.binary .ge (.var "sqrtPriceCurrentX96") (.var "sqrtPriceTargetX96"))) (.ok f6 evm)
    exact ExecStmt.letDecl hge
  have hr5 : f5.locals.get? "amountRemaining" = some (.int (EVM.signed remaining)) := by
    simp only [f5, swapStepPreludeWordsFrame, wordLocal_get, beq_iff_eq, String.reduceEq, ↓reduceIte, hr]
  have hr6 : f6.locals.get? "amountRemaining" = some (.int (EVM.signed remaining)) :=
    (store_get_ne _ _ (by decide : ("zeroForOne" == "amountRemaining") = false)).trans hr5
  have h6 : ExecStmt config f6 evm swapStepPreludeStmts[6]!
      (.ok (swapStepPreludeFrame f price target remaining fee) evm) := by
    apply ExecStmt.letDecl
    change evalExpr? config f6 evm (.binary .lt (.var "amountRemaining") (.intLit 0)) = _
    rw [evalExpr_binary_nonshort (by decide) (by decide), evalLocalValue hr6]
    simp only [evalExpr?, bind, EvalResult.bind, pure, evalBinaryOp?]
    rfl
  exact ExecBlock.consNormal h0 (ExecBlock.consNormal h1 (ExecBlock.consNormal h2
    (ExecBlock.consNormal h3 (ExecBlock.consNormal h4 (ExecBlock.consNormal h5 (execBlock_singleton h6))))))

end Benchmarks.UniswapV4PoolManager
