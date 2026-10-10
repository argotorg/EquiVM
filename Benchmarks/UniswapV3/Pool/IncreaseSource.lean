import Benchmarks.UniswapV3.Pool.CardinalityStorage
import Benchmarks.UniswapV3.Pool.OracleGrow
import Benchmarks.UniswapV3.Pool.NoDelegateCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

abbrev increaseTransition := increaseObservationCardinalityNextTransition

def increaseLocals (next : UInt256) : Store :=
  (∅ : Store).insert "observationCardinalityNext" (.int (Int.ofNat next.toNat))

def increaseFrame (v : UniswapV3PoolImmutables) (next : UInt256) : Frame :=
  { contract := contract, locals := increaseLocals next, immutables := immStore v }

theorem evalIncreaseUnlocked (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (next : UInt256) :
    evalExpr? config (increaseFrame v next) evm
      (.storage ⟨"slot0", [.field "unlocked"]⟩) =
      .ok (.bool (!decide (slot0FieldWord 30 1 evm.accountMap evm.executionEnv = ⟨0⟩))) := by
  rw [← wordToElemBool]
  exact evalSlot0Unlocked _ _ _ (by simp [increaseLocals])

theorem increaseRevertsLocked (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (next : UInt256) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlocked : slot0FieldWord 30 1 evm.accountMap evm.executionEnv = ⟨0⟩) :
    ExecTransitionBody config contract evm (increaseLocals next)
      increaseTransition.body .reverted (immStore v) := by
  apply ExecFuncBody.execBlockRevert
  apply (ABlock.start.requireStep (evalCallvalueEq_true hwv)).requireRevert
  simpa only [hlocked, decide_true, Bool.not_true] using evalIncreaseUnlocked v evm next

theorem increaseAssignLock (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (next : UInt256) :
    ExecStmt config (increaseFrame v next) evm
      (.assign .storage ⟨"slot0", [.field "unlocked"]⟩ (.boolLit false))
      (.ok (increaseFrame v next) (storeSlot0Unlocked evm false)) := by
  exact ExecStmt.assign (by simp only [evalExpr?, pure])
    (assignSlot0Unlocked evm _ _ false (by simp [increaseLocals]))

theorem increaseLockPrefix (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (next : UInt256) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : slot0FieldWord 30 1 evm.accountMap evm.executionEnv ≠ ⟨0⟩) :
    ExecBlock config (increaseFrame v next) evm (increaseTransition.body.take 3)
      (.ok (increaseFrame v next) (storeSlot0Unlocked evm false)) := by
  apply (ABlock.start.requireStep (evalCallvalueEq_true hwv)).run
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · simpa only [hunlocked, decide_false, Bool.not_false] using
      evalIncreaseUnlocked v evm next
  · exact ExecBlock.consNormal (increaseAssignLock v evm next) ExecBlock.nil

theorem increaseStatic (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (next : UInt256) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : slot0FieldWord 30 1 evm.accountMap evm.executionEnv ≠ ⟨0⟩)
    (hperm : evm.executionEnv.perm = false) :
    ExecTransitionBody config contract evm (increaseLocals next)
      increaseTransition.body .staticViolation (immStore v) := by
  apply ExecFuncBody.execBlockStatic
  apply (ABlock.start.requireStep (evalCallvalueEq_true hwv)).run
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · simpa only [hunlocked, decide_false, Bool.not_false] using
      evalIncreaseUnlocked v evm next
  · exact ExecBlock.consStatic (execStmt_assign_static
      (increaseAssignLock v evm next) hperm)


def increaseCheckedFrame (v : UniswapV3PoolImmutables) (next : UInt256) : Frame :=
  { (increaseFrame v next) with locals := (increaseLocals next).insert "__c0" .unit }

def increaseReadyFrame (v : UniswapV3PoolImmutables) (next current : UInt256) : Frame :=
  { (increaseCheckedFrame v next) with
    locals := (increaseCheckedFrame v next).locals.insert "observationCardinalityNextOld" (.int (Int.ofNat current.toNat)) }

def increaseGrownFrame (v : UniswapV3PoolImmutables) (next current result : UInt256) : Frame :=
  { (increaseReadyFrame v next current) with
    locals := (increaseReadyFrame v next current).locals.insert "observationCardinalityNextNew" (.int (Int.ofNat result.toNat)) }

theorem increaseDelegateReverts (v : UniswapV3PoolImmutables) (evm : EVM.State) (next : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : slot0FieldWord 30 1 evm.accountMap evm.executionEnv ≠ ⟨0⟩)
    (hdelegate : evm.executionEnv.codeOwner ≠ v.original) :
    ExecTransitionBody config contract evm (increaseLocals next) increaseTransition.body .reverted (immStore v) := by
  apply ExecFuncBody.execBlockRevert
  rw [← List.take_append_drop 3 increaseTransition.body]
  apply execBlock_append_ok (increaseLockPrefix v evm next hwv hunlocked)
  apply ExecBlock.consRevert
  exact internalCallFunctionRevert (argVals := []) (locals := ∅)
    (by simp only [evalExprs?, pure]) noDelegateCallLookup rfl
    (noDelegateCallReverts v _ (by simpa only [storeSlot0Unlocked_executionEnv] using hdelegate))

theorem increaseReadyPrefix (v : UniswapV3PoolImmutables) (evm : EVM.State) (next : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : slot0FieldWord 30 1 evm.accountMap evm.executionEnv ≠ ⟨0⟩)
    (hself : evm.executionEnv.codeOwner = v.original) :
    let locked := storeSlot0Unlocked evm false
    ExecBlock config (increaseFrame v next) evm (increaseTransition.body.take 5)
      (.ok (increaseReadyFrame v next (slot0FieldWord 27 2 locked.accountMap locked.executionEnv)) locked) := by
  change ExecBlock _ _ _ (increaseTransition.body.take 3 ++ (increaseTransition.body.drop 3).take 2) _
  apply execBlock_append_ok (increaseLockPrefix v evm next hwv hunlocked)
  have hcall : ExecStmt config (increaseFrame v next) (storeSlot0Unlocked evm false)
      (.internalCall "checkNotDelegateCall" [] "__c0")
      (.ok (increaseCheckedFrame v next) (storeSlot0Unlocked evm false)) :=
    internalCallFunctionReturn (callee := noDelegateCallFunction) (argVals := []) (locals := ∅)
      (calleeSolm := noDelegateCallFrame v) (value := none)
      (by simp only [evalExprs?, pure]) noDelegateCallLookup rfl
      (noDelegateCallReturns v _ (by simpa only [storeSlot0Unlocked_executionEnv] using hself))
  refine ExecBlock.consNormal hcall ?_
  exact ExecBlock.consNormal (ExecStmt.letDecl
    (evalSlot0ObservationCardinalityNext _ _ _ (by simp [increaseCheckedFrame, increaseLocals]))) ExecBlock.nil

theorem increaseGrowArgs (v : UniswapV3PoolImmutables) (evm : EVM.State) (next current : UInt256) :
    evalExprs? config (increaseReadyFrame v next current) evm
      [.var "observationCardinalityNextOld", .var "observationCardinalityNext"] =
      .ok [.int (Int.ofNat current.toNat), .int (Int.ofNat next.toNat)] := by
  simp [evalExprs?, evalExpr?, increaseReadyFrame, increaseCheckedFrame, increaseLocals,
    Std.HashMap.getElem_insert, EvalResult.ofOption, EvalResult.bind, bind, pure]

theorem increaseGrowCall (v : UniswapV3PoolImmutables) (evm : EVM.State) (next current : UInt256)
    (hpos : 0 < current.toNat) (hnext : next.toNat < 2 ^ 16) :
    ExecStmt config (increaseReadyFrame v next current) evm
      (.internalCall "Oracle_grow" [.var "observationCardinalityNextOld", .var "observationCardinalityNext"]
        "observationCardinalityNextNew")
      (.ok (increaseGrownFrame v next current (oracleGrowResult current next))
        (oracleGrowState evm current.toNat (next.toNat - current.toNat))) := by
  obtain ⟨frame, hbody⟩ := oracleGrowReturns (immStore v) evm current next hpos hnext
  exact internalCallFunctionReturn (callee := oracleGrowFunction) (locals := oracleGrowLocals current next)
    (calleeSolm := frame) (value := some [.int (Int.ofNat (oracleGrowResult current next).toNat)])
    (increaseGrowArgs v evm next current) oracleGrowLookup (oracleGrowBind current next) hbody

theorem increaseGrowZeroReverts (v : UniswapV3PoolImmutables) (evm : EVM.State) (next : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : slot0FieldWord 30 1 evm.accountMap evm.executionEnv ≠ ⟨0⟩)
    (hself : evm.executionEnv.codeOwner = v.original)
    (hcurrent : slot0FieldWord 27 2 (storeSlot0Unlocked evm false).accountMap
      (storeSlot0Unlocked evm false).executionEnv = ⟨0⟩) :
    ExecTransitionBody config contract evm (increaseLocals next) increaseTransition.body .reverted (immStore v) := by
  apply ExecFuncBody.execBlockRevert
  rw [← List.take_append_drop 5 increaseTransition.body]
  have hprefix := increaseReadyPrefix v evm next hwv hunlocked hself
  dsimp only at hprefix
  rw [hcurrent] at hprefix
  apply execBlock_append_ok hprefix
  apply ExecBlock.consRevert
  exact internalCallFunctionRevert (callee := oracleGrowFunction) (locals := oracleGrowLocals ⟨0⟩ next)
    (increaseGrowArgs v _ next ⟨0⟩) oracleGrowLookup (oracleGrowBind ⟨0⟩ next)
    (oracleGrowRevertsZero (immStore v) _ next)

theorem oracleGrowResult_lt (current next : UInt256)
    (hcurrent : current.toNat < 2 ^ 16) (hnext : next.toNat < 2 ^ 16) :
    (oracleGrowResult current next).toNat < 2 ^ 16 := by
  unfold oracleGrowResult
  split <;> assumption

theorem increaseFinish (v : UniswapV3PoolImmutables) (evm : EVM.State) (next current result : UInt256)
    (hfit : result.toNat < 2 ^ 16) :
    ExecBlock config (increaseGrownFrame v next current result) evm (increaseTransition.body.drop 6)
      (.ok (increaseGrownFrame v next current result)
        (storeSlot0Unlocked (storeSlot0CardinalityNext evm result) true)) := by
  have hnew : ∀ evm', evalExpr? config (increaseGrownFrame v next current result) evm'
      (.var "observationCardinalityNextNew") = .ok (.int (Int.ofNat result.toNat)) := by
    intro evm'; exact evalExpr_var_get (by simp [increaseGrownFrame])
  have hold : ∀ evm', evalExpr? config (increaseGrownFrame v next current result) evm'
      (.var "observationCardinalityNextOld") = .ok (.int (Int.ofNat current.toNat)) := by
    intro evm'; exact evalExpr_var_get (by simp [increaseGrownFrame, increaseReadyFrame, Std.HashMap.getElem_insert])
  have hbase : (increaseGrownFrame v next current result).locals.get? "slot0" = none := by
    simp [increaseGrownFrame, increaseReadyFrame, increaseCheckedFrame, increaseLocals]
  refine ExecBlock.consNormal (ExecStmt.assign (hnew evm)
    (assignSlot0CardinalityNext evm _ _ result hbase hfit)) ?_
  have hevent : ExecStmt config (increaseGrownFrame v next current result) (storeSlot0CardinalityNext evm result)
      (.ite (.binary .ne (.var "observationCardinalityNextOld") (.var "observationCardinalityNextNew"))
        [.emit "IncreaseObservationCardinalityNext"
          [.var "observationCardinalityNextOld", .var "observationCardinalityNextNew"]] [])
      (.ok (increaseGrownFrame v next current result) (storeSlot0CardinalityNext evm result)) := by
    by_cases heq : current.toNat = result.toNat
    · apply ExecStmt.iteFalse ?_ ExecBlock.nil
      simp [evalExpr?, hold, hnew, evalBinaryOp?, heq, bind, EvalResult.bind]
    · refine ExecStmt.iteTrue ?_ (ExecBlock.consNormal (ExecStmt.emit
        (vals := [.int (Int.ofNat current.toNat), .int (Int.ofNat result.toNat)]) ?_) ExecBlock.nil)
      · simp [evalExpr?, hold, hnew, evalBinaryOp?, heq, bind, EvalResult.bind]
      · simp only [evalExprs?, hold, hnew, bind, EvalResult.bind, pure]
  exact ExecBlock.consNormal hevent (ExecBlock.consNormal
    (ExecStmt.assign (by simp only [evalExpr?, pure])
      (assignSlot0Unlocked _ _ _ true hbase)) ExecBlock.nil)

theorem increaseReturns (v : UniswapV3PoolImmutables) (evm : EVM.State) (next : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : slot0FieldWord 30 1 evm.accountMap evm.executionEnv ≠ ⟨0⟩)
    (hself : evm.executionEnv.codeOwner = v.original) (hnext : next.toNat < 2 ^ 16)
    (hpos : 0 < (slot0FieldWord 27 2 (storeSlot0Unlocked evm false).accountMap
      (storeSlot0Unlocked evm false).executionEnv).toNat) :
    let locked := storeSlot0Unlocked evm false
    let current := slot0FieldWord 27 2 locked.accountMap locked.executionEnv
    let result := oracleGrowResult current next
    ExecTransitionBody config contract evm (increaseLocals next) increaseTransition.body
      (.returned (increaseGrownFrame v next current result)
        (storeSlot0Unlocked (storeSlot0CardinalityNext
          (oracleGrowState locked current.toNat (next.toNat - current.toNat)) result) true) none) (immStore v) := by
  dsimp only
  apply ExecFuncBody.execBlockOK
  rw [← List.take_append_drop 5 increaseTransition.body]
  apply execBlock_append_ok (increaseReadyPrefix v evm next hwv hunlocked hself)
  exact ExecBlock.consNormal (increaseGrowCall v _ next _ hpos hnext)
    (increaseFinish v _ next _ _ (oracleGrowResult_lt _ _ (slot0CardinalityNext_lt _ _) hnext))

end Benchmarks.UniswapV3.Pool
