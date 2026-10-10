import Benchmarks.UniswapV4PoolManager.SwapStepFeeWords
import Benchmarks.UniswapV4PoolManager.FullMathRoundSource
import Benchmarks.UniswapV4PoolManager.WordWrappingSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def swapStepFeeComplementExpr : Expr :=
  .cast (.binary .sub (.intLit 1000000) (.var "_feePips")) (.elem (.int (.uint ⟨256, by decide⟩)))

theorem swapStepFeeComplementSource {f : Frame} {evm : EVM.State} {fee : UInt256}
    (hf : f.locals.get? "_feePips" = some (.int (Int.ofNat fee.toNat))) :
    evalExpr? config f evm swapStepFeeComplementExpr =
      .ok (.int (Int.ofNat (swapStepFeeComplement fee).toNat)) :=
  evalWordSub (x := fullMathPPM) (by simp only [evalExpr?, pure]; rfl) (evalLocalValue hf)

def swapStepComputedFeeStmts (name : Ident) : List Stmt :=
  [.internalCall "FullMath_mulDivRoundingUp"
      [.var "amountIn", .var "_feePips", swapStepFeeComplementExpr] name,
   .assign .localVar {base := "feeAmount"} (.var name)]

def swapStepComputedFeeFrame (f : Frame) (name : Ident) (amount fee : UInt256) : Frame :=
  {f with locals := ((f.locals.insert name (.int (Int.ofNat (swapStepFeeWord amount fee).toNat))).insert
      "feeAmount" (.int (Int.ofNat (swapStepFeeWord amount fee).toNat)))}

theorem swapStepComputedFeeSource {f : Frame} {evm : EVM.State} {amount fee : UInt256} {old : Value}
    (name : Ident) (hf : f.contract = contract)
    (ha : f.locals.get? "amountIn" = some (.int (Int.ofNat amount.toNat)))
    (hp : f.locals.get? "_feePips" = some (.int (Int.ofNat fee.toNat)))
    (ho : f.locals.get? "feeAmount" = some old) (hne : (name == "feeAmount") = false) :
    ExecBlock config f evm (swapStepComputedFeeStmts name)
      (if swapStepFeeFits amount fee then .ok (swapStepComputedFeeFrame f name amount fee) evm else .reverted) := by
  have hc := fullMathRoundCall (f := f) (evm := evm) (a := amount) (b := fee)
    (d := swapStepFeeComplement fee) hf (evalLocalValue ha) (evalLocalValue hp) (swapStepFeeComplementSource hp) name
  by_cases hfit : swapStepFeeFits amount fee
  · rw [if_pos hfit] at hc ⊢
    exact ExecBlock.consNormal hc (ExecBlock.consNormal
      (ExecStmt.assign wordLocal_eval (assignLocalValue ((store_get_ne _ _ hne).trans ho))) ExecBlock.nil)
  · rw [if_neg hfit] at hc ⊢
    exact ExecBlock.consRevert hc

def swapStepTargetFeeStmts : List Stmt :=
  [.assign .localVar {base := "feeAmount"} (.var "amountIn"),
   .ite (.binary .ne (.var "_feePips") (.intLit 1000000)) (swapStepComputedFeeStmts "computedFee") []]

def swapStepTargetFeeFrame (f : Frame) (amount fee : UInt256) : Frame :=
  if fee = fullMathPPM then wordLocal f "feeAmount" amount
  else swapStepComputedFeeFrame (wordLocal f "feeAmount" amount) "computedFee" amount fee

theorem swapStepTargetFeeSource {f : Frame} {evm : EVM.State} {amount fee : UInt256} {old : Value}
    (hf : f.contract = contract)
    (ha : f.locals.get? "amountIn" = some (.int (Int.ofNat amount.toNat)))
    (hp : f.locals.get? "_feePips" = some (.int (Int.ofNat fee.toNat)))
    (ho : f.locals.get? "feeAmount" = some old) :
    ExecBlock config f evm swapStepTargetFeeStmts
      (if swapStepTargetFeeFits amount fee then .ok (swapStepTargetFeeFrame f amount fee) evm else .reverted) := by
  let f0 := wordLocal f "feeAmount" amount
  have h0 : ExecStmt config f evm (.assign .localVar {base := "feeAmount"} (.var "amountIn")) (.ok f0 evm) :=
    ExecStmt.assign (evalLocalValue ha) (assignLocalValue ho)
  have ha0 : f0.locals.get? "amountIn" = some (.int (Int.ofNat amount.toNat)) :=
    (store_get_ne _ _ (by decide : ("feeAmount" == "amountIn") = false)).trans ha
  have hp0 : f0.locals.get? "_feePips" = some (.int (Int.ofNat fee.toNat)) :=
    (store_get_ne _ _ (by decide : ("feeAmount" == "_feePips") = false)).trans hp
  have hg := evalNeWords (evalLocalValue (cfg := config) (f := f0) (evm := evm) hp0)
    (show evalExpr? config f0 evm (.intLit 1000000) = .ok (.int (Int.ofNat fullMathPPM.toNat)) by
      simp only [evalExpr?, pure]; rfl)
  by_cases heq : fee = fullMathPPM
  · simp only [swapStepTargetFeeFits, heq, true_or, if_true, swapStepTargetFeeFrame]
    exact ExecBlock.consNormal h0 (ExecBlock.consNormal
      (ExecStmt.iteFalse (by simpa only [heq, ne_eq, not_true_eq_false, decide_false] using hg) ExecBlock.nil) ExecBlock.nil)
  · simp only [swapStepTargetFeeFits, heq, false_or, swapStepTargetFeeFrame, if_false]
    have hc := swapStepComputedFeeSource (f := f0) (evm := evm) "computedFee" hf ha0 hp0
      (store_get_self _ _ _) (by decide)
    have ht : evalExpr? config f0 evm (.binary .ne (.var "_feePips") (.intLit 1000000)) = .ok (.bool true) := by
      simpa only [decide_eq_true heq] using hg
    by_cases hfit : swapStepFeeFits amount fee
    · rw [if_pos hfit] at hc ⊢
      exact ExecBlock.consNormal h0 (ExecBlock.consNormal (ExecStmt.iteTrue ht hc) ExecBlock.nil)
    · rw [if_neg hfit] at hc ⊢
      exact ExecBlock.consNormal h0 (ExecBlock.consRevert (ExecStmt.iteTrue ht hc))

end Benchmarks.UniswapV4PoolManager
