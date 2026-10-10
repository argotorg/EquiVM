import Benchmarks.Morpho.MetaMorphoV1_1.UpdateWithdrawQueueRemoveSource
import Benchmarks.Morpho.MetaMorphoV1_1.MarketConfigDeletion
import Benchmarks.Morpho.MetaMorphoV1_1.MarketBalancesSource

/-! Conditional timelock guards and configuration deletion for an omitted market. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1

open SourceMemory

abbrev updateWithdrawQueueRemovalAllowed (evm : State) (id shares : UInt256) : Prop :=
  shares = ⟨0⟩ ∨ (marketRemovalRemovableAt evm id ≠ ⟨0⟩ ∧
    (marketRemovalRemovableAt evm id).toNat ≤
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)

theorem updateWithdrawQueueRemovalGuardValues {frame : Frame} {evm : State} {id : UInt256}
    (hc : frame.contract = contract) (hconfig : frame.locals.get? "config" = none)
    (hid : frame.locals.get? "id" = some (wordBytes32Value id)) :
    evalExpr? config frame evm
      (.binary .ne (.storage ⟨"config", [.mindex (.var "id"), .field "removableAt"]⟩)
        (.intLit 0)) = .ok (.bool (decide (marketRemovalRemovableAt evm id ≠ ⟨0⟩))) ∧
    evalExpr? config frame evm
      (.binary .ge (.env .timestamp)
        (.storage ⟨"config", [.mindex (.var "id"), .field "removableAt"]⟩)) =
      .ok (.bool (decide ((marketRemovalRemovableAt evm id).toNat ≤
        (UInt256.ofNat evm.executionEnv.header.timestamp).toNat))) := by
  have ht := marketRemovalTimeRead false (evm := evm) hc hconfig hid
  simp only [Bool.false_eq_true, if_false] at ht
  exact ⟨wordNeSource ht (by simp only [evalExpr?, pure]; rfl),
    naturalGeSource (timestampSource config frame evm) ht⟩

theorem updateWithdrawQueueRemovalGuardsPass {frame : Frame} {evm : State} {id : UInt256}
    (hc : frame.contract = contract) (hconfig : frame.locals.get? "config" = none)
    (hid : frame.locals.get? "id" = some (wordBytes32Value id))
    (hnz : marketRemovalRemovableAt evm id ≠ ⟨0⟩)
    (htime : (marketRemovalRemovableAt evm id).toNat ≤
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat) :
    ExecBlock config frame evm updateWithdrawQueueRemovalGuards (.ok frame evm) := by
  obtain ⟨h0, h1⟩ := updateWithdrawQueueRemovalGuardValues (evm := evm) hc hconfig hid
  exact ExecBlock.consNormal (ExecStmt.requireTrue (by
    simpa only [decide_eq_true hnz] using h0))
    (ExecBlock.consNormal (ExecStmt.requireTrue (by
      simpa only [decide_eq_true htime] using h1)) ExecBlock.nil)

theorem updateWithdrawQueueRemovalGuardsRevert {frame : Frame} {evm : State} {id : UInt256}
    (hc : frame.contract = contract) (hconfig : frame.locals.get? "config" = none)
    (hid : frame.locals.get? "id" = some (wordBytes32Value id))
    (hbad : ¬ (marketRemovalRemovableAt evm id ≠ ⟨0⟩ ∧
      (marketRemovalRemovableAt evm id).toNat ≤
        (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)) :
    ExecBlock config frame evm updateWithdrawQueueRemovalGuards .reverted := by
  obtain ⟨h0, h1⟩ := updateWithdrawQueueRemovalGuardValues (evm := evm) hc hconfig hid
  by_cases hnz : marketRemovalRemovableAt evm id ≠ ⟨0⟩
  · refine ExecBlock.consNormal (ExecStmt.requireTrue (by
      simpa only [decide_eq_true hnz] using h0)) ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse (by
      simpa only [show ¬ (marketRemovalRemovableAt evm id).toNat ≤
          (UInt256.ofNat evm.executionEnv.header.timestamp).toNat from fun ht ↦ hbad ⟨hnz, ht⟩,
        decide_false] using h1))
  · exact ExecBlock.consRevert (ExecStmt.requireFalse (by
      simpa only [hnz, decide_false] using h0))

theorem updateWithdrawQueueRemovalTailPrefix {frame : Frame} {evm : State} {id shares : UInt256}
    (hc : frame.contract = contract) (hconfig : frame.locals.get? "config" = none)
    (hid : frame.locals.get? "id" = some (wordBytes32Value id))
    (hshares : frame.locals.get? "__c2" = some (uint256Value shares))
    (hgood : updateWithdrawQueueRemovalAllowed evm id shares) :
    ABlock config evm frame (updateWithdrawQueueRemoval.drop 6) frame
      [.delete ⟨"config", [.mindex (.var "id")]⟩] := by
  have hcond := wordNeSource (evalLocalValue (evm := evm) hshares)
    (by simp only [evalExpr?, pure]; rfl :
      evalExpr? config frame evm (.intLit 0) = .ok (uint256Value ⟨0⟩))
  constructor
  intro result htail
  by_cases hz : shares = ⟨0⟩
  · exact ExecBlock.consNormal (ExecStmt.iteFalse (by
      simpa only [hz, ne_eq, not_true_eq_false, decide_false] using hcond) ExecBlock.nil) htail
  · have hg := hgood.resolve_left hz
    exact ExecBlock.consNormal (ExecStmt.iteTrue (by
      simpa only [decide_eq_true hz] using hcond)
      (updateWithdrawQueueRemovalGuardsPass hc hconfig hid hg.1 hg.2)) htail

theorem updateWithdrawQueueRemovalTailRevert {frame : Frame} {evm : State} {id shares : UInt256}
    (hc : frame.contract = contract) (hconfig : frame.locals.get? "config" = none)
    (hid : frame.locals.get? "id" = some (wordBytes32Value id))
    (hshares : frame.locals.get? "__c2" = some (uint256Value shares))
    (hbad : ¬ updateWithdrawQueueRemovalAllowed evm id shares) :
    ExecBlock config frame evm (updateWithdrawQueueRemoval.drop 6) .reverted := by
  have hnz : shares ≠ ⟨0⟩ := fun h ↦ hbad (.inl h)
  have hcond := wordNeSource (evalLocalValue (evm := evm) hshares)
    (by simp only [evalExpr?, pure]; rfl :
      evalExpr? config frame evm (.intLit 0) = .ok (uint256Value ⟨0⟩))
  exact ExecBlock.consRevert (ExecStmt.iteTrue (by
    simpa only [decide_eq_true hnz] using hcond)
    (updateWithdrawQueueRemovalGuardsRevert hc hconfig hid (fun h ↦ hbad (.inr h))))

theorem updateWithdrawQueueRemovalTailReturns {frame : Frame} {evm : State} {id shares : UInt256}
    (hc : frame.contract = contract) (hconfig : frame.locals.get? "config" = none)
    (hid : frame.locals.get? "id" = some (wordBytes32Value id))
    (hshares : frame.locals.get? "__c2" = some (uint256Value shares))
    (hgood : updateWithdrawQueueRemovalAllowed evm id shares) :
    ExecBlock config frame evm (updateWithdrawQueueRemoval.drop 6)
      (.ok frame (deletedMarketConfigState evm id)) :=
  (updateWithdrawQueueRemovalTailPrefix hc hconfig hid hshares hgood).run
    (ExecBlock.consNormal (ExecStmt.delete (deleteStorage_config hc hconfig hid)) ExecBlock.nil)

theorem updateWithdrawQueueRemovalTailStatic {frame : Frame} {evm : State} {id shares : UInt256}
    (hc : frame.contract = contract) (hconfig : frame.locals.get? "config" = none)
    (hid : frame.locals.get? "id" = some (wordBytes32Value id))
    (hshares : frame.locals.get? "__c2" = some (uint256Value shares))
    (hgood : updateWithdrawQueueRemovalAllowed evm id shares)
    (hperm : evm.executionEnv.perm = false) :
    ExecBlock config frame evm (updateWithdrawQueueRemoval.drop 6) .staticViolation :=
  (updateWithdrawQueueRemovalTailPrefix hc hconfig hid hshares hgood).run
    (ExecBlock.consStatic
      (ExecStmt.deleteStatic (deleteStorage_config hc hconfig hid) hperm))

end Benchmarks.Morpho.MetaMorphoV1_1
