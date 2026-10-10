import Benchmarks.UniswapV4PoolManager.ApplyDelta

/-! Shared source proof for the PoolManager's currency accounting helper. -/
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem accountDeltaFunction_lookup :
    lookupCallable? contract "_accountDelta" = some accountDeltaFunction.toCallable := rfl

def accountDeltaFrame (f : Frame) (previous next : Int) : Frame :=
  let locals := f.locals.insert "__c0" (.tuple [.int previous, .int next])
  let locals := (locals.insert "previous" (.int previous)).insert "next" (.int next)
  let locals := if next = 0 then locals.insert "__c1" .unit
    else if previous = 0 then locals.insert "__c2" .unit else locals
  {f with locals := locals}

def accountDeltaPost (evm : EVM.State) (target currency : AccountAddress) (delta : Int) : EVM.State :=
  let previous := currencyDeltaValue evm target currency
  let next := previous + delta
  let evm1 := applyDeltaPost evm target currency delta
  if delta = 0 then evm else
  if next = 0 then deltaCountPost evm1 false else
  if previous = 0 then deltaCountPost evm1 true else evm1

def accountDeltaResult (f : Frame) (evm : EVM.State) (target currency : AccountAddress) (delta : Int) : ExecResult :=
  let previous := currencyDeltaValue evm target currency
  let next := previous + delta
  if delta = 0 then .returned f evm (some []) else
  if int256Fits next then
    if evm.executionEnv.perm = false then .staticViolation else
    .returned (accountDeltaFrame f previous next) (accountDeltaPost evm target currency delta) none
  else .reverted

theorem accountDeltaPost_env (evm : EVM.State) (target currency : AccountAddress) (delta : Int) :
    (accountDeltaPost evm target currency delta).executionEnv = evm.executionEnv := by
  unfold accountDeltaPost
  dsimp only
  split
  · rfl
  · split
    · simp only [deltaCountPost, applyDeltaPost, transientStore_executionEnv]
    · split <;> simp only [deltaCountPost, applyDeltaPost, transientStore_executionEnv]

theorem accountDeltaPost_world (evm : EVM.State) (target currency : AccountAddress) (delta : Int) :
    (accountDeltaPost evm target currency delta).σ₀ = evm.σ₀ := by
  unfold accountDeltaPost
  dsimp only
  split
  · rfl
  · split
    · simp only [deltaCountPost, applyDeltaPost, transientStore_σ₀]
    · split <;> simp only [deltaCountPost, applyDeltaPost, transientStore_σ₀]

theorem accountDeltaBodyExec {f : Frame} {evm : EVM.State} {target currency : AccountAddress} {delta : Int}
    (hf : f.contract = contract)
    (hc : f.locals.get? "currency" = some (.address currency))
    (hd : f.locals.get? "delta" = some (.int delta))
    (ht : f.locals.get? "target" = some (.address target)) :
    ExecFuncBody config f evm accountDeltaFunction.body (accountDeltaResult f evm target currency delta) := by
  let previous := currencyDeltaValue evm target currency
  let next := previous + delta
  have heq := evalIntEq (cfg := config) (evm := evm) (evalLocalValue hd)
    (by simp only [evalExpr?]; rfl : evalExpr? config f evm (.intLit 0) = .ok (.int 0))
  rw [accountDeltaResult]
  by_cases hz : delta = 0
  · rw [if_pos hz]
    exact ExecFuncBody.execBlockRet (ExecBlock.consReturn (ExecStmt.iteTrue
      (heq.trans (by rw [decide_eq_true hz])) (ExecBlock.consReturn (ExecStmt.return rfl))))
  · rw [if_neg hz]
    have hguard : ExecStmt config f evm accountDeltaFunction.body[0]! (.ok f evm) :=
      ExecStmt.iteFalse (heq.trans (by rw [decide_eq_false hz])) ExecBlock.nil
    have hcall := applyDeltaCall (evm := evm) hf (evalLocalValue hc) (evalLocalValue ht) (evalLocalValue hd) "__c0"
    rw [applyDeltaCallResult] at hcall
    by_cases hfit : int256Fits next
    · rw [if_pos hfit] at hcall ⊢
      by_cases hp : evm.executionEnv.perm = false
      · rw [if_pos hp] at hcall ⊢
        exact ExecFuncBody.execBlockStatic (ExecBlock.consNormal hguard (ExecBlock.consStatic hcall))
      · rw [if_neg hp] at hcall ⊢
        let evm1 := applyDeltaPost evm target currency delta
        have henv : evm1.executionEnv = evm.executionEnv := transientStore_executionEnv _ _ _ _
        let f1 := {f with locals := f.locals.insert "__c0" (.tuple [.int previous, .int next])}
        let f2 := {f1 with locals := f1.locals.insert "previous" (.int previous)}
        let f3 := {f2 with locals := f2.locals.insert "next" (.int next)}
        have htuple1 : f1.locals.get? "__c0" = some (.tuple [.int previous, .int next]) := store_get_self _ _ _
        have htuple2 : f2.locals.get? "__c0" = some (.tuple [.int previous, .int next]) :=
          (store_get_ne _ _ (by decide : ("previous" == "__c0") = false)).trans htuple1
        have hp3 : f3.locals.get? "previous" = some (.int previous) :=
          (store_get_ne _ _ (by decide : ("next" == "previous") = false)).trans (store_get_self _ _ _)
        have hn3 : f3.locals.get? "next" = some (.int next) := store_get_self _ _ _
        have hnextEq := evalIntEq (cfg := config) (evm := evm1) (evalLocalValue hn3)
          (by simp only [evalExpr?]; rfl : evalExpr? config f3 evm1 (.intLit 0) = .ok (.int 0))
        have hprevEq := evalIntEq (cfg := config) (evm := evm1) (evalLocalValue hp3)
          (by simp only [evalExpr?]; rfl : evalExpr? config f3 evm1 (.intLit 0) = .ok (.int 0))
        apply ExecFuncBody.execBlockOK
        refine ExecBlock.consNormal hguard (ExecBlock.consNormal hcall ?_)
        refine ExecBlock.consNormal (ExecStmt.letDecl (evalTupleProjection (evalLocalValue htuple1) (by rfl))) ?_
        refine ExecBlock.consNormal (ExecStmt.letDecl (evalTupleProjection (evalLocalValue htuple2) (by rfl))) ?_
        by_cases hn : next = 0
        · rw [accountDeltaPost, if_neg hz, if_pos hn, accountDeltaFrame, if_pos hn]
          have hcount := deltaCountCall (f := f3) (evm := evm1) hf false "__c1"
          rw [henv, if_neg hp] at hcount
          exact ExecBlock.consNormal (ExecStmt.iteTrue (hnextEq.trans (by rw [decide_eq_true hn]))
            (ExecBlock.consNormal hcount ExecBlock.nil)) ExecBlock.nil
        · rw [accountDeltaPost, if_neg hz, if_neg hn, accountDeltaFrame, if_neg hn]
          by_cases hpv : previous = 0
          · have hpv' : currencyDeltaValue evm target currency = 0 := hpv
            simp only [if_pos hpv']
            have hcount := deltaCountCall (f := f3) (evm := evm1) hf true "__c2"
            rw [henv, if_neg hp] at hcount
            exact ExecBlock.consNormal (ExecStmt.iteFalse (hnextEq.trans (by rw [decide_eq_false hn]))
              (ExecBlock.consNormal (ExecStmt.iteTrue (hprevEq.trans (by rw [decide_eq_true hpv]))
                (ExecBlock.consNormal hcount ExecBlock.nil)) ExecBlock.nil)) ExecBlock.nil
          · have hpv' : currencyDeltaValue evm target currency ≠ 0 := hpv
            simp only [if_neg hpv']
            exact ExecBlock.consNormal (ExecStmt.iteFalse (hnextEq.trans (by rw [decide_eq_false hn]))
              (ExecBlock.consNormal (ExecStmt.iteFalse (hprevEq.trans (by rw [decide_eq_false hpv]))
                ExecBlock.nil) ExecBlock.nil)) ExecBlock.nil
    · rw [if_neg hfit] at hcall ⊢
      exact ExecFuncBody.execBlockRevert (ExecBlock.consNormal hguard (ExecBlock.consRevert hcall))

def accountDeltaCallResult (f : Frame) (evm : EVM.State) (target currency : AccountAddress)
    (delta : Int) (retVar : Ident) : ExecResult :=
  let f' := {f with locals := f.locals.insert retVar .unit}
  if delta = 0 then .ok f' evm else
  if int256Fits (currencyDeltaValue evm target currency + delta) then
    if evm.executionEnv.perm = false then .staticViolation else
    .ok f' (accountDeltaPost evm target currency delta)
  else .reverted

theorem accountDeltaCall {f : Frame} {evm : EVM.State} {target currency : AccountAddress} {delta : Int}
    {ec ed et : Expr} (hf : f.contract = contract)
    (hc : evalExpr? config f evm ec = .ok (.address currency))
    (hd : evalExpr? config f evm ed = .ok (.int delta))
    (ht : evalExpr? config f evm et = .ok (.address target)) (retVar : Ident) :
    ExecStmt config f evm (.internalCall "_accountDelta" [ec, ed, et] retVar)
      (accountDeltaCallResult f evm target currency delta retVar) := by
  let locals := (((∅ : Store).insert "target" (.address target)).insert "delta" (.int delta)).insert "currency" (.address currency)
  have hbody := accountDeltaBodyExec (f := {f with locals := locals}) (evm := evm) hf
    (store_get_self _ _ _)
    ((store_get_ne _ _ (by decide : ("currency" == "delta") = false)).trans (store_get_self _ _ _))
    ((store_get_ne _ _ (by decide : ("currency" == "target") = false)).trans
      ((store_get_ne _ _ (by decide : ("delta" == "target") = false)).trans (store_get_self _ _ _)))
  have hargs : evalExprs? config f evm [ec, ed, et] = .ok [.address currency, .int delta, .address target] := by
    simp only [evalExprs?, hc, hd, ht, bind, EvalResult.bind, pure]
  have hl : lookupCallable? f.contract "_accountDelta" = some accountDeltaFunction.toCallable := by
    rw [hf]; exact accountDeltaFunction_lookup
  have hb : bindParams? accountDeltaFunction.params [.address currency, .int delta, .address target] = some locals := rfl
  rw [accountDeltaCallResult]
  rw [accountDeltaResult] at hbody
  by_cases hz : delta = 0
  · rw [if_pos hz] at hbody ⊢
    exact internalCallFunctionReturn hargs hl hb hbody
  · rw [if_neg hz] at hbody ⊢
    by_cases hfit : int256Fits (currencyDeltaValue evm target currency + delta)
    · rw [if_pos hfit] at hbody ⊢
      by_cases hp : evm.executionEnv.perm = false
      · rw [if_pos hp] at hbody ⊢
        exact internalCallFunctionStatic hargs hl hb hbody
      · rw [if_neg hp] at hbody ⊢
        exact internalCallFunctionReturn hargs hl hb hbody
    · rw [if_neg hfit] at hbody ⊢
      exact internalCallFunctionRevert hargs hl hb hbody

end Benchmarks.UniswapV4PoolManager
