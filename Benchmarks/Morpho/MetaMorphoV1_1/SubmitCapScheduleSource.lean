import Benchmarks.Morpho.MetaMorphoV1_1.SubmitCapImmediateSource
import Benchmarks.Morpho.MetaMorphoV1_1.PendingCapStorage

/-! Source scheduling captures the delay before writing the pending-cap record. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1

open SourceMemory

def submitCapDelayFrame (frame : Frame) (delay : UInt256) : Frame :=
  { frame with locals := frame.locals.insert "__pendingTime8" (uint256Value delay) }

def submitCapScheduleFrame (frame : Frame) (evm : State) (cap : UInt256) : Frame :=
  submitCapDelayFrame (submitCapCastFrame frame false cap) (pendingTimelockDelay evm)

def submitCapTimeExpr : Expr :=
  .cast (.inRange (.uint ⟨256, by decide⟩)
    (.binary .add (.env .timestamp) (.var "__pendingTime8")))
    (.elem (.int (.uint ⟨64, by decide⟩)))

theorem SubmitCapReady.delay {frame : Frame} {p : MarketParamsData}
    {id cap last cursor : UInt256} (h : SubmitCapReady frame p id cap last cursor)
    (delay : UInt256) :
    SubmitCapReady (submitCapDelayFrame frame delay) p id cap last cursor := by
  refine ⟨h.contract, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [submitCapDelayFrame, store_get_ne _ _ (by decide)] <;>
    first | exact h.config | exact h.pending | exact h.timelock | exact h.params
          | exact h.id | exact h.cap | exact h.last | exact h.cursor

theorem submitCapSchedulePrefix {frame : Frame} {evm : State} {p : MarketParamsData}
    {id cap last cursor : UInt256} (h : SubmitCapReady frame p id cap last cursor)
    (hfit : cap.toNat < 2 ^ 184) :
    ABlock config evm frame submitCapScheduled (submitCapScheduleFrame frame evm cap)
      (submitCapScheduled.drop 2) := by
  constructor
  intro result htail
  apply ExecBlock.consNormal (submitCapCastCall h false hfit)
  refine ExecBlock.consNormal ?_ htail
  apply ExecStmt.letDecl
  have hr := evalStorage_timelock evm (submitCapCastFrame frame false cap).locals
    frame.immutables (h.cast false).timelock
  simpa only [submitCapCastFrame, h.contract] using hr

theorem submitCapScheduleValueAssign {frame : Frame} {evm : State} {p : MarketParamsData}
    {id cap last cursor : UInt256} (h : SubmitCapReady frame p id cap last cursor) :
    ExecStmt config (submitCapScheduleFrame frame evm cap) evm
      (.assign .storage ⟨"pendingCap", [.mindex (.var "id"), .field "value"]⟩ (.var "__c7"))
      (.ok (submitCapScheduleFrame frame evm cap) (pendingCapValueState evm id cap)) := by
  have h' := (h.cast false).delay (pendingTimelockDelay evm)
  apply ExecStmt.assign (value := uint256Value cap)
  · simp only [evalExpr?, submitCapScheduleFrame, submitCapDelayFrame,
      store_get_ne _ _ (by decide : ("__pendingTime8" == "__c7") = false),
      submitCapCastFrame, Bool.false_eq_true, if_false, store_get_self, EvalResult.ofOption]
  · exact assignPendingCapValue cap h'.contract h'.pending h'.id

theorem submitCapTimeSource {frame : Frame} {evm : State} {id cap : UInt256}
    (htime : frame.locals.get? "__pendingTime8" = some (uint256Value (pendingTimelockDelay evm)))
    (hfit : pendingTimelockScheduleFits evm) :
    evalExpr? config frame (pendingCapValueState evm id cap) submitCapTimeExpr =
      .ok (uint256Value (pendingTimeCastWord (pendingTimelockTime evm))) := by
  apply uint64CastSource
  apply checkedAddSourceOk (a := UInt256.ofNat evm.executionEnv.header.timestamp)
    (b := pendingTimelockDelay evm) ?_ ?_ hfit
  · simp only [evalExpr?, envValue, pendingCapValueState_env, pure]
  · simp only [evalExpr?, htime, EvalResult.ofOption]

theorem submitCapTimeSourceRevert {frame : Frame} {evm : State} {id cap : UInt256}
    (htime : frame.locals.get? "__pendingTime8" = some (uint256Value (pendingTimelockDelay evm)))
    (hover : ¬ pendingTimelockScheduleFits evm) :
    evalExpr? config frame (pendingCapValueState evm id cap) submitCapTimeExpr = .revert := by
  have h := checkedAddSourceOverflow (cfg := config) (solm := frame)
    (evm := pendingCapValueState evm id cap) (lhs := .env .timestamp) (rhs := .var "__pendingTime8")
    (a := UInt256.ofNat evm.executionEnv.header.timestamp) (b := pendingTimelockDelay evm)
    (by simp only [evalExpr?, envValue, pendingCapValueState_env, pure])
    (by simp only [evalExpr?, htime, EvalResult.ofOption]) (Nat.le_of_not_gt hover)
  simp only [submitCapTimeExpr, evalExpr?, h, bind, EvalResult.bind]

theorem submitCapScheduledStatic {frame : Frame} {evm : State} {p : MarketParamsData}
    {id cap last cursor : UInt256} (h : SubmitCapReady frame p id cap last cursor)
    (hfit : cap.toNat < 2 ^ 184) (hperm : evm.executionEnv.perm = false) :
    ExecBlock config frame evm submitCapScheduled .staticViolation := by
  apply (submitCapSchedulePrefix h hfit).run
  exact ExecBlock.consStatic (execStmt_assign_static (submitCapScheduleValueAssign h) hperm)

theorem submitCapScheduledRevert {frame : Frame} {evm : State} {p : MarketParamsData}
    {id cap last cursor : UInt256} (h : SubmitCapReady frame p id cap last cursor)
    (hfit : cap.toNat < 2 ^ 184) (hover : ¬ pendingTimelockScheduleFits evm) :
    ExecBlock config frame evm submitCapScheduled .reverted := by
  apply (submitCapSchedulePrefix h hfit).run
  apply ExecBlock.consNormal (submitCapScheduleValueAssign h)
  exact ExecBlock.consRevert (ExecStmt.assignExprRevert
    (submitCapTimeSourceRevert (store_get_self _ _ _) hover))

theorem submitCapScheduledReturns {frame : Frame} {evm : State} {p : MarketParamsData}
    {id cap last cursor : UInt256} (h : SubmitCapReady frame p id cap last cursor)
    (hcap : cap.toNat < 2 ^ 184) (hfit : pendingTimelockScheduleFits evm) :
    ∃ final, ExecBlock config frame evm submitCapScheduled
      (.ok final (pendingCapScheduledState evm id cap)) := by
  let f := submitCapScheduleFrame frame evm cap
  have h' : SubmitCapReady f p id cap last cursor := (h.cast false).delay _
  refine ⟨resumeAfterInternalCall f "__c9" (some [.address evm.executionEnv.source]), ?_⟩
  apply (submitCapSchedulePrefix h hcap).run
  apply ExecBlock.consNormal (submitCapScheduleValueAssign h)
  apply ExecBlock.consNormal (ExecStmt.assign
    (submitCapTimeSource (store_get_self _ _ _) hfit)
    (assignPendingCapTime (pendingTimelockTime evm) h'.contract h'.pending h'.id))
  apply ExecBlock.consNormal (internalCallReturnExpr (retTy := [.elem .address])
    (expr := .env .caller) (value := .address evm.executionEnv.source)
    (by change lookupCallable? f.contract "_msgSender" = _; rw [h'.contract]; rfl)
    (by simp only [evalExpr?, envValue, pendingCapTimeState_env, pendingCapValueState_env, pure]))
  apply (ABlock.start.emitStep (vals := [.address evm.executionEnv.source,
    wordBytes32Value id, uint256Value cap]) ?_).run ExecBlock.nil
  simp only [evalExprs?, evalExpr?, resumeAfterInternalCall, store_get_self,
    store_get_ne _ _ (by decide : ("__c9" == "id") = false),
    store_get_ne _ _ (by decide : ("__c9" == "newSupplyCap") = false),
    h'.id, h'.cap, EvalResult.ofOption, bind, EvalResult.bind, pure]

end Benchmarks.Morpho.MetaMorphoV1_1
