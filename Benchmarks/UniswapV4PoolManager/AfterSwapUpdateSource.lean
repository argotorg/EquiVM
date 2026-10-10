import Benchmarks.UniswapV4PoolManager.SafeCast128Source
import Benchmarks.UniswapV4PoolManager.ValueLocals

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def afterSwapUpdateFrame (f : Frame) (unspecified : Int) (delta : UInt256) : Frame :=
  valueLocal (valueLocal f "delta" (.int (EVM.signed delta)))
    "unspecified" (.int (unspecified+EVM.signed delta))
def afterSwapUpdateResult (f : Frame) (evm : State) (unspecified : Int) (delta : UInt256) : ExecResult :=
  if signedFits ⟨128, by decide⟩ (EVM.signed delta) then
    if signedFits ⟨128, by decide⟩ (unspecified+EVM.signed delta) then
      .ok (afterSwapUpdateFrame f unspecified delta) evm else .reverted
  else .reverted
def afterSwapUpdateStmts : List Stmt :=
  [.internalCall "SafeCast_toInt128" [.var "result"] "delta",
   .assign .localVar {base := "unspecified"}
     (.inRange (.sint ⟨128, by decide⟩) (.binary .add (.var "unspecified") (.var "delta")))]

theorem afterSwapUpdateSource {f : Frame} {evm : State} {unspecified : Int} {delta : UInt256}
    (hf : f.contract = contract)
    (hu : f.locals.get? "unspecified" = some (.int unspecified))
    (hr : f.locals.get? "result" = some (.int (EVM.signed delta))) :
    ExecBlock config f evm afterSwapUpdateStmts (afterSwapUpdateResult f evm unspecified delta) := by
  have hcast := signedToInt128Call (evm := evm) hf (evalLocalValue hr) "delta"
  by_cases hc : signedFits ⟨128, by decide⟩ (EVM.signed delta)
  · rw [if_pos hc] at hcast
    rw [afterSwapUpdateResult, if_pos hc]
    let f1 := valueLocal f "delta" (.int (EVM.signed delta))
    have hu1 : f1.locals.get? "unspecified" = some (.int unspecified) :=
      (store_get_ne _ _ (by decide : ("delta" == "unspecified") = false)).trans hu
    have hadd : evalExpr? config f1 evm (.binary .add (.var "unspecified") (.var "delta")) =
        .ok (.int (unspecified+EVM.signed delta)) := by
      rw [evalExpr_binary_nonshort (by decide) (by decide), evalLocalValue hu1,
        evalLocalValue (store_get_self _ _ _)]; rfl
    have hsum := evalSignedRange ⟨128, by decide⟩ hadd
    by_cases hs : signedFits ⟨128, by decide⟩ (unspecified+EVM.signed delta)
    · rw [if_pos hs] at hsum ⊢
      exact ExecBlock.consNormal hcast (execBlock_singleton (ExecStmt.assign hsum (assignLocalValue hu1)))
    · rw [if_neg hs] at hsum ⊢
      exact ExecBlock.consNormal hcast (ExecBlock.consRevert (ExecStmt.assignExprRevert hsum))
  · rw [if_neg hc] at hcast
    rw [afterSwapUpdateResult, if_neg hc]
    exact ExecBlock.consRevert hcast

theorem afterSwapUpdateResult_normal {f f' : Frame} {evm post : State} {unspecified : Int} {delta : UInt256}
    (hr : afterSwapUpdateResult f evm unspecified delta = .ok f' post) :
    f' = afterSwapUpdateFrame f unspecified delta ∧ post = evm ∧
      signedFits ⟨128, by decide⟩ (unspecified+EVM.signed delta) := by
  rw [afterSwapUpdateResult] at hr
  split_ifs at hr with hc hs <;> cases hr
  exact ⟨rfl, rfl, hs⟩

end Benchmarks.UniswapV4PoolManager
