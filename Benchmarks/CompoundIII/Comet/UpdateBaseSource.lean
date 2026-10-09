import Benchmarks.CompoundIII.Comet.UpdateBaseFinishSource
import Benchmarks.CompoundIII.Comet.AccountRewardSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem updateBase_block (v : CometWithExtendedAssetListImmutables) (evm : EVM.State)
    (addr : AccountAddress) (basic : UserBasicData) (newPrincipal : UInt256) :
    internalBlockResult config (updateBaseEntry v addr basic newPrincipal) evm
      updateBaseCallable.body (updateBaseOutcome v evm addr basic newPrincipal) := by
  let f0 := updateBaseEntry v addr basic newPrincipal
  let f1 : Frame :=
    { f0 with locals := f0.locals.insert "principal" (.int (signed104 basic.principal)) }
  let f2 := updateBaseRewardEntry v addr basic newPrincipal
  let basic' : UserBasicData := { basic with principal := newPrincipal }
  let borrow := principalBorrow basic.principal
  let f3 := accountRewardFrame f2 v evm basic' basic.principal borrow
  have heb : evalExpr? config f0 evm (.var "basic") = .ok (userBasicValue basic) := by
    simp only [evalExpr?, f0, updateBaseEntry, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]
    rfl
  apply internalBlockResult.prepend (ExecStmt.letDecl (evalBasicPrincipal heb))
  have hepn : evalExpr? config f1 evm (.var "principalNew") =
      .ok (.int (signed104 newPrincipal)) := by
    simp only [evalExpr?, f1, f0, updateBaseEntry, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]
    rfl
  have hb1 : f1.locals.get? "basic" = some (userBasicValue basic) := by
    simp only [f1, f0, updateBaseEntry, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
    rfl
  apply internalBlockResult.prepend (ExecStmt.assign hepn (assignBasicPrincipal newPrincipal hb1))
  have hb2 : f2.locals.get? "basic" = some (userBasicValue basic') := by
    simp only [f2, basic', updateBaseRewardEntry, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert]
    rfl
  have hp2 : f2.locals.get? "principal" = some (.int (signed104 basic.principal)) := by
    simp only [f2, updateBaseRewardEntry, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
    rfl
  have hx2 (b : Bool) : f2.locals.get? (trackingIndexName b) = none := by
    cases b <;> simp only [f2, updateBaseRewardEntry, updateBaseEntry, trackingIndexName,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] <;> simp
  have hguard : evalExpr? config f2 evm (.binary .ge (.var "principal") (.intLit 0)) =
      .ok (.bool (decide (0 ≤ signed104 basic.principal))) := by
    simp only [evalExpr?, hp2, EvalResult.ofOption, pure, bind, EvalResult.bind, evalBinaryOp?]
  have hbranch : ExecStmt config f2 evm
      (.ite (.binary .ge (.var "principal") (.intLit 0))
        (accountRewardBlock false) (accountRewardBlock true))
      (if AccountRewardValid v evm basic basic.principal borrow then
        .ok f3 evm else .reverted) := by
    by_cases hpos : 0 ≤ signed104 basic.principal
    · have hborr : borrow = false := by
        simp [borrow, principalBorrow, show ¬ signed104 basic.principal < 0 by omega]
      rw [decide_eq_true hpos] at hguard
      simp only [f3, hborr]
      exact ExecStmt.iteTrue hguard
        (accountReward_source v false f2 evm basic' basic.principal
          rfl rfl hb2 hp2 (hx2 false) hpos)
    · have hn : signed104 basic.principal < 0 := by omega
      have hborr : borrow = true := by simp [borrow, principalBorrow, hn]
      rw [decide_eq_false hpos] at hguard
      simp only [f3, hborr]
      exact ExecStmt.iteFalse hguard
        (accountReward_source v true f2 evm basic' basic.principal rfl rfl hb2 hp2 (hx2 true) hn)
  by_cases hv : AccountRewardValid v evm basic basic.principal borrow
  · rw [if_pos hv] at hbranch
    unfold updateBaseOutcome
    rw [if_pos hv]
    apply internalBlockResult.prepend hbranch
    apply updateBaseFinish_source f3 evm addr
      (userBasicWithAccrued basic'
        (basic.accrued + accountReward v evm basic basic.principal borrow)) newPrincipal rfl
    · simp only [f3, accountRewardFrame, Std.HashMap.get?_eq_getElem?,
        Std.HashMap.getElem?_insert, beq_self_eq_true, if_true]
      rfl
    · cases hborr : borrow <;>
        simp only [f3, accountRewardFrame, hborr, f2, updateBaseRewardEntry, updateBaseEntry,
          accountRewardName, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] <;> simp
    · cases hborr : borrow <;>
        simp only [f3, accountRewardFrame, hborr, f2, updateBaseRewardEntry, updateBaseEntry,
          accountRewardName, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] <;> simp
    · cases hborr : borrow <;>
        simp only [f3, accountRewardFrame, hborr, f2, updateBaseRewardEntry, updateBaseEntry,
          accountRewardName, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] <;> simp
    · intro b
      cases b <;> cases hborr : borrow <;>
        simp only [f3, accountRewardFrame, hborr, f2, updateBaseRewardEntry, updateBaseEntry,
          accountRewardName, trackingIndexName, Std.HashMap.get?_eq_getElem?,
          Std.HashMap.getElem?_insert] <;> simp
  · rw [if_neg hv] at hbranch
    unfold updateBaseOutcome
    rw [if_neg hv]
    exact ExecBlock.consRevert hbranch

theorem updateBase_source (v : CometWithExtendedAssetListImmutables) (evm : EVM.State)
    (addr : AccountAddress) (basic : UserBasicData) (newPrincipal : UInt256) :
    internalSourceResult config (updateBaseEntry v addr basic newPrincipal) evm
      updateBaseCallable.body (updateBaseOutcome v evm addr basic newPrincipal) :=
  (updateBase_block v evm addr basic newPrincipal).toSource

theorem updateBase_call (v : CometWithExtendedAssetListImmutables) (frame : Frame)
    (evm : EVM.State) (addr : AccountAddress) (basic : UserBasicData) (newPrincipal : UInt256)
    (addrExpr basicExpr principalExpr : Expr) (ret : Ident)
    (hc : frame.contract = contract) (hi : frame.immutables = immStore v)
    (ha : evalExpr? config frame evm addrExpr = .ok (.address addr))
    (hb : evalExpr? config frame evm basicExpr = .ok (userBasicValue basic))
    (hp : evalExpr? config frame evm principalExpr = .ok (.int (signed104 newPrincipal))) :
    ExecStmt config frame evm
      (.internalCall "updateBasePrincipal" [addrExpr, basicExpr, principalExpr] ret)
      (internalStmtResult frame ret (updateBaseOutcome v evm addr basic newPrincipal)) := by
  apply internalVoidCall (callee := updateBaseCallable)
    (locals := (updateBaseEntry v addr basic newPrincipal).locals)
    (argVals := [.address addr, userBasicValue basic, .int (signed104 newPrincipal)])
    (by simp only [evalExprs?, ha, hb, hp, pure, bind, EvalResult.bind])
    (by rw [hc]; exact updateBaseCallable_lookup) rfl
  simpa only [hc, hi] using updateBase_source v evm addr basic newPrincipal

end Benchmarks.CompoundIII.Comet
