import Benchmarks.UniswapV4PoolManager.DeltaCount

/-! Applying a signed currency delta preserves the source's read/write order. -/
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 2000000

theorem applyDeltaFunction_lookup :
    lookupCallable? contract "CurrencyDelta_applyDelta" = some applyDeltaFunction.toCallable := rfl

def applyDeltaFrame (f : Frame) (target currency : AccountAddress) (previous next : Int) : Frame :=
  let locals := (f.locals.insert "previous" (.int 0)).insert "next" (.int 0)
  let locals := locals.insert "hashSlot" (wordBytes32Value (currencyDeltaSlot target currency))
  let locals := locals.insert "previous" (.int previous)
  {f with locals := locals.insert "next" (.int next)}

def applyDeltaPost (evm : EVM.State) (target currency : AccountAddress) (delta : Int) : EVM.State :=
  Solm.EVM.transientStore evm evm.executionEnv.codeOwner (currencyDeltaSlot target currency)
    (EVM.wordOfInt (currencyDeltaValue evm target currency + delta))

def applyDeltaResult (f : Frame) (evm : EVM.State) (target currency : AccountAddress) (delta : Int) : ExecResult :=
  let previous := currencyDeltaValue evm target currency
  let next := previous + delta
  if int256Fits next then
    if evm.executionEnv.perm = false then .staticViolation else
    .returned (applyDeltaFrame f target currency previous next) (applyDeltaPost evm target currency delta)
      (some [.int previous, .int next])
  else .reverted

theorem applyDeltaBodyExec {f : Frame} {evm : EVM.State} {target currency : AccountAddress} {delta : Int}
    (hf : f.contract = contract)
    (hc : f.locals.get? "currency" = some (.address currency))
    (ht : f.locals.get? "target" = some (.address target))
    (hd : f.locals.get? "delta" = some (.int delta)) :
    ExecFuncBody config f evm applyDeltaFunction.body (applyDeltaResult f evm target currency delta) := by
  let previous := currencyDeltaValue evm target currency
  let next := previous + delta
  let f1 := {f with locals := f.locals.insert "previous" (.int 0)}
  let f2 := {f1 with locals := f1.locals.insert "next" (.int 0)}
  let f3 := {f2 with locals := f2.locals.insert "hashSlot" (wordBytes32Value (currencyDeltaSlot target currency))}
  let f4 := {f3 with locals := f3.locals.insert "previous" (.int previous)}
  let f5 := {f4 with locals := f4.locals.insert "next" (.int next)}
  have hc2 : f2.locals.get? "currency" = some (.address currency) :=
    (store_get_ne _ _ (by decide : ("next" == "currency") = false)).trans
      ((store_get_ne _ _ (by decide : ("previous" == "currency") = false)).trans hc)
  have ht2 : f2.locals.get? "target" = some (.address target) :=
    (store_get_ne _ _ (by decide : ("next" == "target") = false)).trans
      ((store_get_ne _ _ (by decide : ("previous" == "target") = false)).trans ht)
  have hcall := deltaSlotCall (evm := evm) (f := f2) hf (evalLocalValue ht2) (evalLocalValue hc2) "hashSlot"
  have hslot3 : f3.locals.get? "hashSlot" = some (wordBytes32Value (currencyDeltaSlot target currency)) := store_get_self _ _ _
  have hprev3 : f3.locals.get? "previous" = some (.int 0) :=
    (store_get_ne _ _ (by decide : ("hashSlot" == "previous") = false)).trans
      ((store_get_ne _ _ (by decide : ("next" == "previous") = false)).trans (store_get_self _ _ _))
  have hread := evalExpr_cast_int (intType := .sint ⟨256, by decide⟩)
    (rawTransient_read (f := f3) (evm := evm) hf
      (evalCastValue (evalLocalValue hslot3) (castBytes32ToUint256 _)))
  have hprefix : ABlock config evm f applyDeltaFunction.body f4 (applyDeltaFunction.body.drop 4) := by
    refine ⟨fun h => ?_⟩
    refine ExecBlock.consNormal (ExecStmt.letDecl (by simp only [evalExpr?]; rfl)) ?_
    refine ExecBlock.consNormal (ExecStmt.letDecl (by simp only [evalExpr?]; rfl)) ?_
    exact ExecBlock.consNormal hcall (ExecBlock.consNormal (ExecStmt.assign hread (assignLocalValue hprev3)) h)
  have hd4 : f4.locals.get? "delta" = some (.int delta) :=
    (store_get_ne _ _ (by decide : ("previous" == "delta") = false)).trans
      ((store_get_ne _ _ (by decide : ("hashSlot" == "delta") = false)).trans
        ((store_get_ne _ _ (by decide : ("next" == "delta") = false)).trans
          ((store_get_ne _ _ (by decide : ("previous" == "delta") = false)).trans hd)))
  have hn4 : f4.locals.get? "next" = some (.int 0) :=
    (store_get_ne _ _ (by decide : ("previous" == "next") = false)).trans
      ((store_get_ne _ _ (by decide : ("hashSlot" == "next") = false)).trans (store_get_self _ _ _))
  have hadd := evalCheckedInt256Add (cfg := config) (f := f4) (evm := evm)
    (evalLocalValue (store_get_self _ "previous" (.int previous))) (evalLocalValue hd4)
  rw [applyDeltaResult]
  by_cases hfit : int256Fits next
  · rw [if_pos hfit] at hadd ⊢
    have hslot5 : f5.locals.get? "hashSlot" = some (wordBytes32Value (currencyDeltaSlot target currency)) :=
      (store_get_ne _ _ (by decide : ("next" == "hashSlot") = false)).trans
        ((store_get_ne _ _ (by decide : ("previous" == "hashSlot") = false)).trans hslot3)
    have hn5 : f5.locals.get? "next" = some (.int next) := store_get_self _ _ _
    have hcast := evalExpr_cast_int (cfg := config) (evm := evm) (intType := .uint ⟨256, by decide⟩) (evalLocalValue hn5)
    have hwrite := rawTransient_writeInt (f := f5) (evm := evm) (normalizeInt (.uint ⟨256, by decide⟩) next)
      hf (evalCastValue (evalLocalValue hslot5) (castBytes32ToUint256 _))
    rw [wordOfInt_normalizeUint256] at hwrite
    by_cases hp : evm.executionEnv.perm = false
    · rw [if_pos hp]
      apply ExecFuncBody.execBlockStatic
      exact hprefix.run (ExecBlock.consNormal (ExecStmt.assign hadd (assignLocalValue hn4))
        (ExecBlock.consStatic (ExecStmt.assignTransientStatic hcast hwrite hp)))
    · rw [if_neg hp]
      apply ExecFuncBody.execBlockRet
      refine hprefix.run (ExecBlock.consNormal (ExecStmt.assign hadd (assignLocalValue hn4))
        (ExecBlock.consNormal (ExecStmt.assign hcast hwrite) (ExecBlock.consReturn (ExecStmt.return ?_))))
      have hp5 : f5.locals.get? "previous" = some (.int previous) :=
        (store_get_ne _ _ (by decide : ("next" == "previous") = false)).trans (store_get_self _ _ _)
      simp only [evalExprs?, evalLocalValue hp5, evalLocalValue hn5, bind, EvalResult.bind, pure]
      rfl
  · rw [if_neg hfit] at hadd ⊢
    exact ExecFuncBody.execBlockRevert (hprefix.run (ExecBlock.consRevert (ExecStmt.assignExprRevert hadd)))

def applyDeltaCallResult (f : Frame) (evm : EVM.State) (target currency : AccountAddress)
    (delta : Int) (retVar : Ident) : ExecResult :=
  let previous := currencyDeltaValue evm target currency
  let next := previous + delta
  if int256Fits next then
    if evm.executionEnv.perm = false then .staticViolation else
    .ok {f with locals := f.locals.insert retVar (.tuple [.int previous, .int next])}
      (applyDeltaPost evm target currency delta)
  else .reverted

theorem applyDeltaCall {f : Frame} {evm : EVM.State} {target currency : AccountAddress} {delta : Int}
    {ec et ed : Expr} (hf : f.contract = contract)
    (hc : evalExpr? config f evm ec = .ok (.address currency))
    (ht : evalExpr? config f evm et = .ok (.address target))
    (hd : evalExpr? config f evm ed = .ok (.int delta)) (retVar : Ident) :
    ExecStmt config f evm (.internalCall "CurrencyDelta_applyDelta" [ec, et, ed] retVar)
      (applyDeltaCallResult f evm target currency delta retVar) := by
  let locals := (((∅ : Store).insert "delta" (.int delta)).insert "target" (.address target)).insert "currency" (.address currency)
  have hbody := applyDeltaBodyExec (f := {f with locals := locals}) (evm := evm) hf
    (store_get_self _ _ _)
    ((store_get_ne _ _ (by decide : ("currency" == "target") = false)).trans (store_get_self _ _ _))
    ((store_get_ne _ _ (by decide : ("currency" == "delta") = false)).trans
      ((store_get_ne _ _ (by decide : ("target" == "delta") = false)).trans (store_get_self _ _ _)))
  have hargs : evalExprs? config f evm [ec, et, ed] = .ok [.address currency, .address target, .int delta] := by
    simp only [evalExprs?, hc, ht, hd, bind, EvalResult.bind, pure]
  have hl : lookupCallable? f.contract "CurrencyDelta_applyDelta" = some applyDeltaFunction.toCallable := by
    rw [hf]; exact applyDeltaFunction_lookup
  have hb : bindParams? applyDeltaFunction.params [.address currency, .address target, .int delta] = some locals := rfl
  rw [applyDeltaCallResult]
  rw [applyDeltaResult] at hbody
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
