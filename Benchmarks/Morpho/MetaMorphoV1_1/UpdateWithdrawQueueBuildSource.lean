import Benchmarks.Morpho.MetaMorphoV1_1.UpdateWithdrawQueueReady
import Benchmarks.Morpho.MetaMorphoV1_1.LocalArrayBoolSource

/-! Source reads, duplicate checks, and writes in the queue-construction loop. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1

def updateWithdrawQueuePreviousFrame (frame : Frame) (prev : UInt256) : Frame :=
  { frame with locals := frame.locals.insert "prevIndex" (uint256Value prev) }

def updateWithdrawQueueReadFrame (frame : Frame) (prev id : UInt256) : Frame :=
  let f := updateWithdrawQueuePreviousFrame frame prev
  { f with locals := f.locals.insert "id" (wordBytes32Value id) }

def updateWithdrawQueueStepFrame (frame : Frame) (prev id : UInt256)
    (seen : List Bool) (queue : List UInt256) (i : Nat) : Frame :=
  let f := updateWithdrawQueueReadFrame frame prev id
  { f with
    locals := (f.locals.insert "seen" (.array ((seen.set prev.toNat true).map Value.bool))).insert
      "newWithdrawQueue" (.array ((queue.set i id).map wordBytes32Value)) }

theorem UpdateWithdrawQueueReady.readFrame {frame : Frame} {imms : Store}
    {indexes : List Value} {curr i : Nat} {seen : List Bool} {queue : List UInt256}
    {cursor : UInt256} (h : UpdateWithdrawQueueReady frame imms indexes curr i seen queue cursor)
    (prev id : UInt256) :
    UpdateWithdrawQueueReady (updateWithdrawQueueReadFrame frame prev id)
      imms indexes curr i seen queue cursor := by
  constructor <;> simp only [updateWithdrawQueueReadFrame, updateWithdrawQueuePreviousFrame]
  all_goals repeat first | rw [store_get_ne _ _ (by decide)]
  all_goals first
    | exact h.contract | exact h.immutables | exact h.withdrawQueue | exact h.config
    | exact h.pendingCap | exact h.input | exact h.currLength | exact h.newLength
    | exact h.seen | exact h.queue | exact h.cursor | exact h.index

theorem UpdateWithdrawQueueReady.stepFrame {frame : Frame} {imms : Store}
    {indexes : List Value} {curr i : Nat} {seen : List Bool} {queue : List UInt256}
    {cursor : UInt256} (h : UpdateWithdrawQueueReady frame imms indexes curr i seen queue cursor)
    (prev id : UInt256) :
    UpdateWithdrawQueueReady (updateWithdrawQueueStepFrame frame prev id seen queue i)
      imms indexes curr i (seen.set prev.toNat true) (queue.set i id) cursor := by
  have hr := h.readFrame prev id
  constructor <;> simp only [updateWithdrawQueueStepFrame]
  all_goals repeat first | rw [store_get_self] | rw [store_get_ne _ _ (by decide)]
  all_goals first
    | exact hr.contract | exact hr.immutables | exact hr.withdrawQueue | exact hr.config
    | exact hr.pendingCap | exact hr.input | exact hr.currLength | exact hr.newLength
    | exact hr.cursor | exact hr.index

theorem updateWithdrawQueueBuildRead {frame : Frame} {imms : Store} {evm : State}
    {indexes : List Value} {curr i : Nat} {seen : List Bool} {queue : List UInt256}
    {cursor prev : UInt256}
    (h : UpdateWithdrawQueueReady frame imms indexes curr i seen queue cursor)
    (hprev : indexes[i]? = some (uint256Value prev))
    (hbound : prev.toNat < (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨21⟩).toNat) :
    let id := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
      (uInt256OfByteArray (KEC (UInt256.toByteArray ⟨21⟩)) + prev)
    ABlock config evm frame updateWithdrawQueueBuildBody
      (updateWithdrawQueueReadFrame frame prev id) (updateWithdrawQueueBuildBody.drop 2) := by
  dsimp only
  constructor
  intro result htail
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalLocalArrayIndex h.input h.index hprev rfl)) ?_
  refine ExecBlock.consNormal ?_ htail
  apply ExecStmt.letDecl
  have hc := h.contract
  rcases frame with ⟨c, locals, imms'⟩
  dsimp only at hc
  subst c
  exact evalStorage_withdrawQueue_local evm _ imms' "prevIndex" prev
    (by rw [store_get_ne _ _ (by decide)]; exact h.withdrawQueue)
    (store_get_self _ _ _) hbound

theorem updateWithdrawQueueBuildReadRevert {frame : Frame} {imms : Store} {evm : State}
    {indexes : List Value} {curr i : Nat} {seen : List Bool} {queue : List UInt256}
    {cursor prev : UInt256}
    (h : UpdateWithdrawQueueReady frame imms indexes curr i seen queue cursor)
    (hprev : indexes[i]? = some (uint256Value prev))
    (hbound : ¬ prev.toNat <
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨21⟩).toNat) :
    ExecBlock config frame evm updateWithdrawQueueBuildBody .reverted := by
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalLocalArrayIndex h.input h.index hprev rfl)) ?_
  apply ExecBlock.consRevert
  apply ExecStmt.letDeclRevert
  apply evalStorage_arrayIndex_revert "withdrawQueue" "prevIndex" prev.toNat
    (by rw [store_get_ne _ _ (by decide)]; exact h.withdrawQueue) (store_get_self _ _ _)
  change arrayIndexInBounds? config evm frame.contract.storage _ _ _ = _
  rw [h.contract, withdrawQueueBounds, if_neg hbound]

theorem updateWithdrawQueueDuplicateSource {frame : Frame} {evm : State}
    {seen : List Bool} {prev id : UInt256} {b : Bool}
    (hseen : frame.locals.get? "seen" = some (.array (seen.map Value.bool)))
    (hb : seen[prev.toNat]? = some b) :
    evalExpr? config (updateWithdrawQueueReadFrame frame prev id) evm
      (.unary .not (.index (.var "seen") (.var "prevIndex"))) = .ok (.bool (!b)) := by
  apply evalLocalArrayBoolNot (values := seen) (i := prev.toNat) ?_ ?_ hb
  · simp only [updateWithdrawQueueReadFrame, updateWithdrawQueuePreviousFrame,
      store_get_ne _ _ (by decide : ("id" == "seen") = false),
      store_get_ne _ _ (by decide : ("prevIndex" == "seen") = false), hseen]
  · simp only [updateWithdrawQueueReadFrame, updateWithdrawQueuePreviousFrame,
      store_get_ne _ _ (by decide : ("id" == "prevIndex") = false), store_get_self]

theorem updateWithdrawQueueBuildTailRevert {frame : Frame} {evm : State}
    {seen : List Bool} {prev id : UInt256}
    (hseen : frame.locals.get? "seen" = some (.array (seen.map Value.bool)))
    (hb : seen[prev.toNat]? = some true) :
    ExecBlock config (updateWithdrawQueueReadFrame frame prev id) evm
      (updateWithdrawQueueBuildBody.drop 2) .reverted :=
  ExecBlock.consRevert (ExecStmt.requireFalse (updateWithdrawQueueDuplicateSource hseen hb))

theorem updateWithdrawQueueBuildTailPass {frame : Frame} {imms : Store} {evm : State}
    {indexes : List Value} {curr i : Nat} {seen : List Bool} {queue : List UInt256}
    {cursor prev id : UInt256}
    (h : UpdateWithdrawQueueReady frame imms indexes curr i seen queue cursor)
    (hb : seen[prev.toNat]? = some false) (hi : i < queue.length) :
    ExecBlock config (updateWithdrawQueueReadFrame frame prev id) evm
      (updateWithdrawQueueBuildBody.drop 2)
      (.ok (updateWithdrawQueueStepFrame frame prev id seen queue i) evm) := by
  have hr := h.readFrame prev id
  have hp : (updateWithdrawQueueReadFrame frame prev id).locals.get? "prevIndex" =
      some (uint256Value prev) := by
    simp only [updateWithdrawQueueReadFrame, updateWithdrawQueuePreviousFrame,
      store_get_ne _ _ (by decide : ("id" == "prevIndex") = false), store_get_self]
  have hseen := assignLocalArrayIndex (cfg := config) (evm := evm)
    (value := .bool true) hr.seen hp
    (by rw [List.length_map]; exact (List.getElem?_eq_some_iff.mp hb).1)
  have hqueue := assignLocalArrayIndex (cfg := config) (evm := evm)
    (array := "newWithdrawQueue") (index := "i") (values := queue.map wordBytes32Value)
    (i := i)
    (solm := { updateWithdrawQueueReadFrame frame prev id with
      locals := (updateWithdrawQueueReadFrame frame prev id).locals.insert "seen"
        (.array ((seen.map Value.bool).set prev.toNat (.bool true))) })
    (value := wordBytes32Value id)
    (by rw [store_get_ne _ _ (by decide)]; exact hr.queue)
    (by rw [store_get_ne _ _ (by decide)]; exact hr.index)
    (by rw [List.length_map]; exact hi)
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (updateWithdrawQueueDuplicateSource h.seen hb)) ?_
  refine ExecBlock.consNormal (ExecStmt.assign (by simp only [evalExpr?, pure]) hseen) ?_
  refine ExecBlock.consNormal (ExecStmt.assign ?_ hqueue) ?_
  · simp only [evalExpr?, store_get_ne _ _ (by decide : ("seen" == "id") = false),
      updateWithdrawQueueReadFrame, store_get_self, EvalResult.ofOption]
  · simpa only [updateWithdrawQueueStepFrame, List.map_set] using
      (ExecBlock.nil (cfg := config)
        (solm := updateWithdrawQueueStepFrame frame prev id seen queue i) (evm := evm))

end Benchmarks.Morpho.MetaMorphoV1_1
