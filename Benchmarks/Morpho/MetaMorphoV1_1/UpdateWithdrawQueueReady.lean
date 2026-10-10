import Benchmarks.Morpho.MetaMorphoV1_1.UpdateWithdrawQueueAllocationSource
import Benchmarks.Morpho.MetaMorphoV1_1.ArrayStorage

/-! Source-frame invariants shared by the withdrawal queue's two loops. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1

open SourceMemory

structure UpdateWithdrawQueueReady (frame : Frame) (imms : Store) (indexes : List Value)
    (curr i : Nat) (seen : List Bool) (queue : List UInt256) (cursor : UInt256) : Prop where
  contract : frame.contract = MetaMorphoV1_1.contract
  immutables : frame.immutables = imms
  withdrawQueue : frame.locals.get? "withdrawQueue" = none
  config : frame.locals.get? "config" = none
  pendingCap : frame.locals.get? "pendingCap" = none
  input : frame.locals.get? "indexes" = some (.array indexes)
  currLength : frame.locals.get? "currLength" = some (.int (Int.ofNat curr))
  newLength : frame.locals.get? "newLength" = some (.int (Int.ofNat indexes.length))
  seen : frame.locals.get? "seen" = some (.array (seen.map Value.bool))
  queue : frame.locals.get? "newWithdrawQueue" = some (.array (queue.map wordBytes32Value))
  cursor : frame.locals.get? cursorName = some (uint256Value cursor)
  index : frame.locals.get? "i" = some (.int (Int.ofNat i))

def updateWithdrawQueueIndexFrame (frame : Frame) (i : Nat) : Frame :=
  { frame with locals := frame.locals.insert "i" (.int (Int.ofNat i)) }

theorem UpdateWithdrawQueueReady.indexFrame {frame : Frame} {imms : Store}
    {indexes : List Value} {curr i : Nat} {seen : List Bool} {queue : List UInt256}
    {cursor : UInt256} (h : UpdateWithdrawQueueReady frame imms indexes curr i seen queue cursor)
    (j : Nat) :
    UpdateWithdrawQueueReady (updateWithdrawQueueIndexFrame frame j)
      imms indexes curr j seen queue cursor := by
  constructor
  · exact h.contract
  · exact h.immutables
  · rw [updateWithdrawQueueIndexFrame, store_get_ne _ _ (by decide)]; exact h.withdrawQueue
  · rw [updateWithdrawQueueIndexFrame, store_get_ne _ _ (by decide)]; exact h.config
  · rw [updateWithdrawQueueIndexFrame, store_get_ne _ _ (by decide)]; exact h.pendingCap
  · rw [updateWithdrawQueueIndexFrame, store_get_ne _ _ (by decide)]; exact h.input
  · rw [updateWithdrawQueueIndexFrame, store_get_ne _ _ (by decide)]; exact h.currLength
  · rw [updateWithdrawQueueIndexFrame, store_get_ne _ _ (by decide)]; exact h.newLength
  · rw [updateWithdrawQueueIndexFrame, store_get_ne _ _ (by decide)]; exact h.seen
  · rw [updateWithdrawQueueIndexFrame, store_get_ne _ _ (by decide)]; exact h.queue
  · rw [updateWithdrawQueueIndexFrame, store_get_ne _ _ (by decide)]; exact h.cursor
  · exact store_get_self _ _ _

theorem updateWithdrawQueueBuildConditionSource {frame : Frame} {imms : Store}
    {evm : State} {indexes : List Value} {curr i : Nat} {seen : List Bool}
    {queue : List UInt256} {cursor : UInt256}
    (h : UpdateWithdrawQueueReady frame imms indexes curr i seen queue cursor) :
    evalExpr? config frame evm updateWithdrawQueueBuildCondition =
      .ok (.bool (decide (i < indexes.length))) :=
  evalLocalNatLt h.index h.newLength

theorem updateWithdrawQueueRemoveConditionSource {frame : Frame} {imms : Store}
    {evm : State} {indexes : List Value} {curr i : Nat} {seen : List Bool}
    {queue : List UInt256} {cursor : UInt256}
    (h : UpdateWithdrawQueueReady frame imms indexes curr i seen queue cursor) :
    evalExpr? config frame evm updateWithdrawQueueRemoveCondition =
      .ok (.bool (decide (i < curr))) :=
  evalLocalNatLt h.index h.currLength

theorem updateWithdrawQueuePostSource {frame : Frame} {imms : Store}
    {evm : State} {indexes : List Value} {curr i : Nat} {seen : List Bool}
    {queue : List UInt256} {cursor : UInt256}
    (h : UpdateWithdrawQueueReady frame imms indexes curr i seen queue cursor)
    (hfit : i + 1 < UInt256.size) :
    ExecBlock config frame evm updateWithdrawQueuePost
      (.ok (updateWithdrawQueueIndexFrame frame (i + 1)) evm) :=
  execLocalIncrement h.index hfit

theorem updateWithdrawQueueInitialReady (evm : State) (imms : Store) (indexes : List Value) :
    let curr := (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨21⟩).toNat
    UpdateWithdrawQueueReady (updateWithdrawQueueIndexFrame
      (updateWithdrawQueueAllocatedFrame (updateWithdrawQueuePrefixFrame evm imms indexes)
        curr indexes.length) 0) imms indexes curr 0 (List.replicate curr false)
      (List.replicate indexes.length ⟨0⟩)
      (UInt256.ofNat (192 + 32 * curr + 32 * indexes.length)) := by
  dsimp only
  constructor <;> simp only [updateWithdrawQueueIndexFrame, updateWithdrawQueueAllocatedFrame,
    updateWithdrawQueueSeenFrame, updateWithdrawQueueCursorFrame, updateWithdrawQueuePrefixFrame,
    List.map_replicate]
  all_goals repeat first
    | rw [store_get_self]
    | rw [store_get_ne _ _ (by decide)]
    | rw [store_get_empty]

end Benchmarks.Morpho.MetaMorphoV1_1
