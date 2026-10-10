import Benchmarks.Morpho.MetaMorphoV1_1.UpdateWithdrawQueueReady
import Benchmarks.Morpho.MetaMorphoV1_1.MarketRemovalGuardsSource
import Benchmarks.Morpho.MetaMorphoV1_1.CursorCallSource

/-! Source storage reads and guards before querying an omitted market's supply shares. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1

open SourceMemory

def updateWithdrawQueueIdFrame (frame : Frame) (id : UInt256) : Frame :=
  { frame with locals := frame.locals.insert "id" (wordBytes32Value id) }

theorem UpdateWithdrawQueueReady.idFrame {frame : Frame} {imms : Store}
    {indexes : List Value} {curr i : Nat} {seen : List Bool} {queue : List UInt256}
    {cursor : UInt256} (h : UpdateWithdrawQueueReady frame imms indexes curr i seen queue cursor)
    (id : UInt256) :
    UpdateWithdrawQueueReady (updateWithdrawQueueIdFrame frame id)
      imms indexes curr i seen queue cursor := by
  constructor <;> simp only [updateWithdrawQueueIdFrame]
  all_goals repeat first | rw [store_get_ne _ _ (by decide)]
  all_goals first
    | exact h.contract | exact h.immutables | exact h.withdrawQueue | exact h.config
    | exact h.pendingCap | exact h.input | exact h.currLength | exact h.newLength
    | exact h.seen | exact h.queue | exact h.cursor | exact h.index

theorem UpdateWithdrawQueueReady.readerFrame {frame : Frame} {imms : Store}
    {indexes : List Value} {curr i : Nat} {seen : List Bool} {queue : List UInt256}
    {cursor : UInt256} (h : UpdateWithdrawQueueReady frame imms indexes curr i seen queue cursor)
    (shares cursor' : UInt256) :
    UpdateWithdrawQueueReady (cursorResultFrame frame "__c2" (uint256Value shares) cursor')
      imms indexes curr i seen queue cursor' := by
  refine ⟨h.contract, h.immutables, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    cursorResultFrame_cursor _ _ _ _, ?_⟩
  all_goals rw [cursorResultFrame_preserves _ _ _ _ _ (by decide) (by decide) (by decide)]
  all_goals first
    | exact h.withdrawQueue | exact h.config | exact h.pendingCap | exact h.input
    | exact h.currLength | exact h.newLength | exact h.seen | exact h.queue | exact h.index

theorem updateWithdrawQueueOmittedRead {frame : Frame} {imms : Store} {evm : State}
    {indexes : List Value} {curr i : Nat} {seen : List Bool} {queue : List UInt256}
    {cursor : UInt256}
    (h : UpdateWithdrawQueueReady frame imms indexes curr i seen queue cursor)
    (hfit : i < UInt256.size)
    (hbound : i < (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨21⟩).toNat) :
    let id := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
      (uInt256OfByteArray (KEC (UInt256.toByteArray ⟨21⟩)) + UInt256.ofNat i)
    ABlock config evm frame updateWithdrawQueueRemoval (updateWithdrawQueueIdFrame frame id)
      (updateWithdrawQueueRemoval.drop 1) := by
  dsimp only
  constructor
  intro result htail
  refine ExecBlock.consNormal ?_ htail
  apply ExecStmt.letDecl
  have hc := h.contract
  rcases frame with ⟨c, locals, imms'⟩
  dsimp only at hc
  subst c
  exact evalStorage_withdrawQueue_local evm locals imms' "i" (UInt256.ofNat i)
    h.withdrawQueue (by simpa only [ulit_toNat' _ hfit] using h.index)
    (by rwa [ulit_toNat' _ hfit])

theorem updateWithdrawQueueOmittedReadRevert {frame : Frame} {imms : Store} {evm : State}
    {indexes : List Value} {curr i : Nat} {seen : List Bool} {queue : List UInt256}
    {cursor : UInt256}
    (h : UpdateWithdrawQueueReady frame imms indexes curr i seen queue cursor)
    (hfit : i < UInt256.size)
    (hbound : ¬ i < (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨21⟩).toNat) :
    ExecBlock config frame evm updateWithdrawQueueRemoval .reverted := by
  apply ExecBlock.consRevert
  apply ExecStmt.letDeclRevert
  apply evalStorage_arrayIndex_revert "withdrawQueue" "i" i h.withdrawQueue h.index
  rw [h.contract]
  have hb := withdrawQueueBounds evm (UInt256.ofNat i)
  rw [ulit_toNat' _ hfit, if_neg hbound] at hb
  exact hb

theorem updateWithdrawQueueBeforeCallSource {frame : Frame} {evm : State} {id : UInt256}
    (hc : frame.contract = contract) (hconfig : frame.locals.get? "config" = none)
    (hpending : frame.locals.get? "pendingCap" = none)
    (hid : frame.locals.get? "id" = some (wordBytes32Value id))
    (hcap : marketRemovalCap evm id = ⟨0⟩) (htime : marketRemovalPendingAt evm id = ⟨0⟩) :
    ABlock config evm frame (updateWithdrawQueueRemoval.drop 1) frame
      (updateWithdrawQueueRemoval.drop 3) := by
  obtain ⟨_, hcap', _, htime'⟩ := marketRemovalGuardValues (evm := evm) hc hconfig hpending hid
  constructor
  intro result htail
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · simpa only [hcap, decide_true] using hcap'
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) htail
  simpa only [htime, decide_true] using htime'

theorem updateWithdrawQueueBeforeCallRevert {frame : Frame} {evm : State} {id : UInt256}
    (hc : frame.contract = contract) (hconfig : frame.locals.get? "config" = none)
    (hpending : frame.locals.get? "pendingCap" = none)
    (hid : frame.locals.get? "id" = some (wordBytes32Value id))
    (hbad : ¬ (marketRemovalCap evm id = ⟨0⟩ ∧ marketRemovalPendingAt evm id = ⟨0⟩)) :
    ExecBlock config frame evm (updateWithdrawQueueRemoval.drop 1) .reverted := by
  obtain ⟨_, hcap', _, htime'⟩ := marketRemovalGuardValues (evm := evm) hc hconfig hpending hid
  by_cases hcap : marketRemovalCap evm id = ⟨0⟩
  · refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · simpa only [hcap, decide_true] using hcap'
    exact ExecBlock.consRevert (ExecStmt.requireFalse (by
      simpa only [show ¬ marketRemovalPendingAt evm id = ⟨0⟩ from fun ht ↦ hbad ⟨hcap, ht⟩,
        decide_false] using htime'))
  · exact ExecBlock.consRevert (ExecStmt.requireFalse (by
      simpa only [hcap, decide_false] using hcap'))

end Benchmarks.Morpho.MetaMorphoV1_1
