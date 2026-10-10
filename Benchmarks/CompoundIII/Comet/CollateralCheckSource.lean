import Benchmarks.CompoundIII.Comet.CollateralDebtSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem collateralPrincipal_read (v : CometWithExtendedAssetListImmutables)
    (account : AccountAddress) (evm : EVM.State) :
    ExecStmt config (collateralCheckEntry v account) evm
      (.letDecl "principal" (some (.elem (.int (.sint ⟨104, by decide⟩))))
        collateralPrincipalExpr)
      (.ok (collateralPrincipalFrame v account (collateralBasicWord evm account)) evm) := by
  apply ExecStmt.letDecl
  exact evalUserBasicPrincipalOf evm (collateralCheckEntry v account).locals (immStore v)
    account (.var "account") (by simp [collateralCheckEntry])
    (by simp only [evalExpr?, collateralCheckEntry, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]; rfl)

theorem collateralPrincipalCond_eval (v : CometWithExtendedAssetListImmutables)
    (account : AccountAddress) (basic : UInt256) (evm : EVM.State) :
    evalExpr? config (collateralPrincipalFrame v account basic) evm collateralPrincipalCond =
      .ok (.bool (decide (0 ≤ signed104 basic))) := by
  simp only [collateralPrincipalCond, evalExpr?, collateralPrincipalFrame,
    Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, EvalResult.ofOption,
    pure, bind, EvalResult.bind]
  rfl

theorem collateralBits_read (v : CometWithExtendedAssetListImmutables)
    (account : AccountAddress) (evm : EVM.State) :
    ExecBlock config (collateralPrincipalFrame v account (collateralBasicWord evm account))
      evm collateralBitsBlock
      (.ok (collateralBitsFrame v account (collateralBasicWord evm account)) evm) := by
  let f := collateralPrincipalFrame v account (collateralBasicWord evm account)
  let f' : Frame := { f with
    locals := f.locals.insert "assetsIn"
      (.int (userBasicFieldWord (collateralBasicWord evm account) 2).toNat) }
  have he := evalUserBasicFieldOf f evm account (.var "account") 2 rfl
    (by simp [f, collateralPrincipalFrame, collateralCheckEntry])
    (by simp only [evalExpr?, f, collateralPrincipalFrame, collateralCheckEntry,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, EvalResult.ofOption]; rfl)
  have he' := evalUserBasicFieldOf f' evm account (.var "account") 3 rfl
    (by simp [f', f, collateralPrincipalFrame, collateralCheckEntry])
    (by simp only [evalExpr?, f', f, collateralPrincipalFrame, collateralCheckEntry,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, EvalResult.ofOption]; rfl)
  exact ExecBlock.consNormal (ExecStmt.letDecl he)
    (ExecBlock.consNormal (ExecStmt.letDecl he') .nil)

theorem collateralPresent_call (v : CometWithExtendedAssetListImmutables)
    (account : AccountAddress) (evm : EVM.State)
    (hp : signed104 (collateralBasicWord evm account) < 0) :
    ExecStmt config (collateralBitsFrame v account (collateralBasicWord evm account)) evm
      (.internalCall "presentValue" [.var "principal"] "__c0")
      (if -(2^103 : Int) < signed104 (collateralBasicWord evm account) then
        .ok (collateralPresentFrame v account (collateralBasicWord evm account)
          (signedPresentMagnitude evm (collateralBasicWord evm account) true)) evm
        else .reverted) := by
  have he := signedPresent_call (collateralBitsFrame v account (collateralBasicWord evm account))
    evm (collateralBasicWord evm account) (.var "principal") "__c0" rfl
    (by simp only [evalExpr?, collateralBitsFrame, collateralPrincipalFrame,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, EvalResult.ofOption]; rfl)
  simpa only [signedPresentValueInt, if_neg (show ¬ 0 ≤ signed104
    (collateralBasicWord evm account) by omega)] using he

theorem collateralCheck_source {v : CometWithExtendedAssetListImmutables} {borrow : Bool}
    {account : AccountAddress} {evm : EVM.State} {result : Option (EVM.State × Bool)}
    (ht : CollateralCheckTrace v borrow account evm result) :
    CollateralCheckSourceResult (collateralCheckEntry v account) evm
      (collateralCheckCallable borrow).body result := by
  have hpref := collateralPrincipal_read v account evm
  have hcond := collateralPrincipalCond_eval v account (collateralBasicWord evm account) evm
  cases ht with
  | solvent hp =>
      rw [decide_eq_true hp] at hcond
      exact ⟨_, ExecBlock.consNormal hpref (ExecBlock.consReturn (ExecStmt.iteTrue hcond
        (ABlock.start.returns (by simp only [evalExpr?, pure]))))⟩
  | minimum hp hm =>
      rw [decide_eq_false (by omega)] at hcond
      have hbits := collateralBits_read v account evm
      have hpresent := collateralPresent_call v account evm hp
      rw [if_neg hm] at hpresent
      exact ExecBlock.consNormal hpref (ExecBlock.consNormal (ExecStmt.iteFalse hcond .nil)
        (execBlockAppendOk hbits (ExecBlock.consRevert hpresent)))
  | debt hp hm hdebt =>
      rw [decide_eq_false (by omega)] at hcond
      have hbits := collateralBits_read v account evm
      have hpresent := collateralPresent_call v account evm hp
      rw [if_pos hm] at hpresent
      have htail := collateralDebt_source hdebt
      cases result with
      | none =>
          exact ExecBlock.consNormal hpref (ExecBlock.consNormal (ExecStmt.iteFalse hcond .nil)
            (execBlockAppendOk hbits (ExecBlock.consNormal hpresent htail)))
      | some r =>
          obtain ⟨evm', value⟩ := r
          obtain ⟨final, htail⟩ := htail
          exact ⟨final, ExecBlock.consNormal hpref (ExecBlock.consNormal
            (ExecStmt.iteFalse hcond .nil)
            (execBlockAppendOk hbits (ExecBlock.consNormal hpresent htail)))⟩

theorem collateralCheck_call {v : CometWithExtendedAssetListImmutables} {borrow : Bool}
    {account : AccountAddress} {evm : EVM.State} {result : Option (EVM.State × Bool)}
    (ht : CollateralCheckTrace v borrow account evm result) (frame : Frame) (expr : Expr)
    (ret : Ident) (hc : frame.contract = contract) (hi : frame.immutables = immStore v)
    (he : evalExpr? config frame evm expr = .ok (.address account)) :
    match result with
    | none => ExecStmt config frame evm (.internalCall (collateralCheckName borrow) [expr] ret)
        .reverted
    | some (evm', value) => ExecStmt config frame evm
        (.internalCall (collateralCheckName borrow) [expr] ret)
        (.ok { frame with locals := frame.locals.insert ret (.bool value) } evm') := by
  have hsource := collateralCheck_source ht
  cases result with
  | none =>
      exact ExecStmt.internalCallRevert (callee := collateralCheckCallable borrow)
        (locals := (collateralCheckEntry v account).locals) (evalExprs?_singleton he)
        (by rw [hc]; exact collateralCheckCallable_lookup borrow) rfl
        (by simpa only [hc, hi] using ExecFuncBody.execBlockRevert hsource)
  | some r =>
      obtain ⟨evm', value⟩ := r
      obtain ⟨final, hsource⟩ := hsource
      exact ExecStmt.internalCallReturn (callee := collateralCheckCallable borrow)
        (locals := (collateralCheckEntry v account).locals) (evalExprs?_singleton he)
        (by rw [hc]; exact collateralCheckCallable_lookup borrow) rfl
        (by simpa only [hc, hi] using ExecFuncBody.execBlockRet hsource)

end Benchmarks.CompoundIII.Comet
