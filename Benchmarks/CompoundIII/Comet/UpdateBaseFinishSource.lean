import Benchmarks.CompoundIII.Comet.UpdateBaseModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

theorem basicSetIndex_source (frame : Frame) (evm : EVM.State) (basic : UserBasicData)
    (borrow : Bool) (hc : frame.contract = contract)
    (hb : frame.locals.get? "basic" = some (userBasicValue basic))
    (hx : frame.locals.get? (trackingIndexName borrow) = none) :
    ExecStmt config frame evm (basicSetIndexStmt borrow)
      (.ok { frame with
        locals := frame.locals.insert "basic" (userBasicValue
          { basic with index := accountRewardIndex evm borrow,
                       index_lt := accountRewardIndex_lt evm borrow }) } evm) := by
  apply ExecStmt.assign
  · simpa only [← hc] using evalTrackingIndex evm frame.locals frame.immutables borrow hx
  · exact assignBasicIndex _ (accountRewardIndex_lt evm borrow) hb

theorem updateBaseIndex_source (frame : Frame) (evm : EVM.State) (basic : UserBasicData)
    (principal : UInt256) (hc : frame.contract = contract)
    (hb : frame.locals.get? "basic" = some (userBasicValue basic))
    (hp : frame.locals.get? "principalNew" = some (.int (signed104 principal)))
    (hx : ∀ borrow, frame.locals.get? (trackingIndexName borrow) = none) :
    ExecStmt config frame evm
      (.ite (.binary .ge (.var "principalNew") (.intLit 0))
        [basicSetIndexStmt false] [basicSetIndexStmt true])
      (.ok { frame with
        locals := frame.locals.insert "basic"
          (userBasicValue (basicSetIndex evm basic principal)) } evm) := by
  have hguard : evalExpr? config frame evm (.binary .ge (.var "principalNew") (.intLit 0)) =
      .ok (.bool (decide (0 ≤ signed104 principal))) := by
    simp only [evalExpr?, hp, EvalResult.ofOption, pure, bind, EvalResult.bind, evalBinaryOp?]
  by_cases hpos : 0 ≤ signed104 principal
  · have hborr : principalBorrow principal = false := by
      simp [principalBorrow, show ¬ signed104 principal < 0 by omega]
    rw [decide_eq_true hpos] at hguard
    simp only [basicSetIndex, hborr]
    exact ExecStmt.iteTrue hguard
      (ExecBlock.consNormal (basicSetIndex_source frame evm basic false hc hb (hx false))
        ExecBlock.nil)
  · have hborr : principalBorrow principal = true := by
      simp [principalBorrow, show signed104 principal < 0 by omega]
    rw [decide_eq_false hpos] at hguard
    simp only [basicSetIndex, hborr]
    exact ExecStmt.iteFalse hguard
      (ExecBlock.consNormal (basicSetIndex_source frame evm basic true hc hb (hx true))
        ExecBlock.nil)

theorem updateBaseFinish_source (frame : Frame) (evm : EVM.State) (addr : AccountAddress)
    (basic : UserBasicData) (principal : UInt256) (hc : frame.contract = contract)
    (hb : frame.locals.get? "basic" = some (userBasicValue basic))
    (hp : frame.locals.get? "principalNew" = some (.int (signed104 principal)))
    (ha : frame.locals.get? "account" = some (.address addr))
    (hu : frame.locals.get? "userBasic" = none)
    (hx : ∀ borrow, frame.locals.get? (trackingIndexName borrow) = none) :
    internalBlockResult config frame evm updateBaseFinishBlock
      (if evm.executionEnv.perm then
        .ok (storeUserBasic evm addr (basicSetIndex evm basic principal))
        else .staticViolation) := by
  let basic' := basicSetIndex evm basic principal
  let frame' : Frame := { frame with locals := frame.locals.insert "basic" (userBasicValue basic') }
  have hindex := updateBaseIndex_source frame evm basic principal hc hb hp hx
  have heb : evalExpr? config frame' evm (.var "basic") = .ok (userBasicValue basic') := by
    simp only [evalExpr?, frame', Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
      EvalResult.ofOption]
    rfl
  have hea : evalExpr? config frame' evm (.var "account") = .ok (.address addr) := by
    have ha' : frame'.locals.get? "account" = some (.address addr) := by
      simpa only [frame', Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] using ha
    simp only [evalExpr?, ha', EvalResult.ofOption]
  have hu' : frame'.locals.get? "userBasic" = none := by
    simpa only [frame', Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] using hu
  have hw := assignUserBasic frame' evm addr (.var "account") basic' hc hu' hea
  cases hperm : evm.executionEnv.perm
  · simp only [Bool.false_eq_true, if_false, internalBlockResult]
    exact ExecBlock.consNormal hindex (ExecBlock.consStatic (ExecStmt.assignStatic heb hw hperm))
  · simp only [if_true, internalBlockResult]
    exact ⟨frame', ExecBlock.consNormal hindex
      (ExecBlock.consNormal (ExecStmt.assign heb hw) ExecBlock.nil)⟩

end Benchmarks.CompoundIII.Comet
