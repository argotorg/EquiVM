import Benchmarks.UniswapV4PoolManager.SignedArithmetic
import Benchmarks.UniswapV4PoolManager.ValueLocals

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def beforeSwapDirectionValid (amount adjusted : UInt256) : Prop :=
  if EVM.signed amount < 0 then EVM.signed adjusted ≤ 0 else 0 ≤ EVM.signed adjusted
instance (amount adjusted : UInt256) : Decidable (beforeSwapDirectionValid amount adjusted) :=
  inferInstanceAs (Decidable (if EVM.signed amount < 0 then EVM.signed adjusted ≤ 0 else 0 ≤ EVM.signed adjusted))
def beforeSwapAmountFrame (f : Frame) (amount delta : UInt256) : Frame :=
  valueLocal (valueLocal f "exactInput" (.bool (decide (EVM.signed amount < 0))))
    "amountToSwap" (.int (EVM.signed (amount+delta)))
def beforeSwapAmountResult (f : Frame) (evm : State) (amount delta : UInt256) : ExecResult :=
  if int256Fits (EVM.signed amount+EVM.signed delta) then
    if beforeSwapDirectionValid amount (amount+delta) then .ok (beforeSwapAmountFrame f amount delta) evm
    else .reverted
  else .reverted
def beforeSwapAmountStmts : List Stmt :=
  [.letDecl "exactInput" (some (.elem .bool)) (.binary .lt (.var "amountToSwap") (.intLit 0)),
   .assign .localVar {base := "amountToSwap"}
     (.inRange (.sint ⟨256, by decide⟩) (.binary .add (.var "amountToSwap") (.var "hookDeltaSpecified"))),
   .require (.ite (.var "exactInput") (.binary .le (.var "amountToSwap") (.intLit 0))
     (.binary .ge (.var "amountToSwap") (.intLit 0)))]

theorem beforeSwapAmountSource {f : Frame} {evm : State} {amount delta : UInt256}
    (ha : f.locals.get? "amountToSwap" = some (.int (EVM.signed amount)))
    (hd : f.locals.get? "hookDeltaSpecified" = some (.int (EVM.signed delta))) :
    ExecBlock config f evm beforeSwapAmountStmts (beforeSwapAmountResult f evm amount delta) := by
  let f1 := valueLocal f "exactInput" (.bool (decide (EVM.signed amount < 0)))
  have hinput : evalExpr? config f evm (.binary .lt (.var "amountToSwap") (.intLit 0)) =
      .ok (.bool (decide (EVM.signed amount < 0))) := by
    simp only [evalExpr?, ha, EvalResult.ofOption, bind, EvalResult.bind, pure, evalBinaryOp?]
  have ha1 : f1.locals.get? "amountToSwap" = some (.int (EVM.signed amount)) :=
    (store_get_ne _ _ (by decide : ("exactInput" == "amountToSwap") = false)).trans ha
  have hd1 : f1.locals.get? "hookDeltaSpecified" = some (.int (EVM.signed delta)) :=
    (store_get_ne _ _ (by decide : ("exactInput" == "hookDeltaSpecified") = false)).trans hd
  have hadd := evalCheckedInt256Add (evalLocalValue (cfg := config) (evm := evm) ha1) (evalLocalValue hd1)
  by_cases hfit : int256Fits (EVM.signed amount+EVM.signed delta)
  · rw [if_pos hfit] at hadd
    rw [beforeSwapAmountResult, if_pos hfit]
    have hsum : EVM.signed (amount+delta) = EVM.signed amount+EVM.signed delta := by
      rw [← wordOfInt_signed_add, signed_wordOfInt hfit]
    rw [← hsum] at hadd
    have hguard : evalExpr? config (beforeSwapAmountFrame f amount delta) evm
        (.ite (.var "exactInput") (.binary .le (.var "amountToSwap") (.intLit 0))
          (.binary .ge (.var "amountToSwap") (.intLit 0))) =
        .ok (.bool (decide (beforeSwapDirectionValid amount (amount+delta)))) := by
      simp only [beforeSwapAmountFrame, evalExpr?, valueLocal_get,
        show ("amountToSwap" == "exactInput") = false from rfl, beq_self_eq_true,
        Bool.false_eq_true, if_true, if_false, EvalResult.ofOption, bind, EvalResult.bind, pure]
      by_cases hn : EVM.signed amount < 0 <;>
        simp only [beforeSwapDirectionValid, hn, if_true, if_false, decide_true, decide_false,
          evalBinaryOp?]
    by_cases hvalid : beforeSwapDirectionValid amount (amount+delta)
    · rw [if_pos hvalid]
      exact ExecBlock.consNormal (ExecStmt.letDecl hinput)
        (ExecBlock.consNormal (ExecStmt.assign hadd (assignLocalValue ha1))
          (execBlock_singleton (ExecStmt.requireTrue (hguard.trans (by rw [decide_eq_true hvalid])))))
    · rw [if_neg hvalid]
      exact ExecBlock.consNormal (ExecStmt.letDecl hinput)
        (ExecBlock.consNormal (ExecStmt.assign hadd (assignLocalValue ha1))
          (ExecBlock.consRevert (ExecStmt.requireFalse (hguard.trans (by rw [decide_eq_false hvalid])))))
  · rw [if_neg hfit] at hadd
    rw [beforeSwapAmountResult, if_neg hfit]
    exact ExecBlock.consNormal (ExecStmt.letDecl hinput) (ExecBlock.consRevert (ExecStmt.assignExprRevert hadd))

end Benchmarks.UniswapV4PoolManager
