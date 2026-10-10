import Benchmarks.Morpho.MetaMorphoV1_1.SubmitCapSyntax
import Benchmarks.Morpho.MetaMorphoV1_1.SubmitCapGuards
import Benchmarks.Morpho.MetaMorphoV1_1.MarketRemovalGuardsSource
import Benchmarks.Morpho.MetaMorphoV1_1.MarketBalancesSource

/-! Source guard evaluation and preserved locals at the cap-submission branches. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

open SourceMemory

structure SubmitCapReady (frame : Frame) (p : MarketParamsData)
    (id cap last cursor : UInt256) : Prop where
  contract : frame.contract = Benchmarks.Morpho.MetaMorphoV1_1.contract
  config : frame.locals.get? "config" = none
  pending : frame.locals.get? "pendingCap" = none
  timelock : frame.locals.get? "timelock" = none
  params : frame.locals.get? "marketParams" = some p.value
  id : frame.locals.get? "id" = some (wordBytes32Value id)
  cap : frame.locals.get? "newSupplyCap" = some (uint256Value cap)
  last : frame.locals.get? "__c4" = some (uint256Value last)
  cursor : frame.locals.get? cursorName = some (uint256Value cursor)

def submitCapCapFrame (frame : Frame) (supply : UInt256) : Frame :=
  { frame with locals := frame.locals.insert "supplyCap" (uint256Value supply) }

theorem submitCapResultFrame_ready (v : MetaMorphoV1_1Immutables) (evm : State)
    (out : ByteArray) (cap last cursor : UInt256) :
    SubmitCapReady (submitCapResultFrame v evm out cap last cursor)
      (marketParamsData out) (marketParamsData out).id cap last cursor := by
  constructor <;>
    simp [submitCapResultFrame, submitCapReaderFrame, resumeAfterInternalCall,
      submitCapAssetFrame, submitCapHashFrame, submitCapRoleFrame, submitCapParamsFrame,
      submitCapCalldataFrame, submitCapInitialLocals, slotsAndCursorName, cursorName,
      Std.HashMap.getElem_insert]

theorem SubmitCapReady.supply {frame : Frame} {p : MarketParamsData}
    {id cap last cursor : UInt256} (h : SubmitCapReady frame p id cap last cursor)
    (supply : UInt256) : SubmitCapReady (submitCapCapFrame frame supply) p id cap last cursor := by
  refine ⟨h.contract, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [submitCapCapFrame, store_get_ne _ _ (by decide)] <;>
    first | exact h.config | exact h.pending | exact h.timelock | exact h.params
          | exact h.id | exact h.cap | exact h.last | exact h.cursor

theorem submitCapLastSource {frame : Frame} {evm : State} {last : UInt256}
    (hlast : frame.locals.get? "__c4" = some (uint256Value last)) :
    evalExpr? config frame evm submitCapLastCondition =
      .ok (.bool (decide (last ≠ ⟨0⟩))) := by
  apply wordNeSource
  · simp only [evalExpr?, hlast, EvalResult.ofOption]
  · simp only [evalExpr?, pure]; rfl

theorem submitCapDifferentSource {frame : Frame} {evm : State} {cap supply : UInt256}
    (hcap : frame.locals.get? "newSupplyCap" = some (uint256Value cap))
    (hsupply : frame.locals.get? "supplyCap" = some (uint256Value supply)) :
    evalExpr? config frame evm submitCapDifferentCondition =
      .ok (.bool (decide (cap ≠ supply))) := by
  apply wordNeSource <;> simp only [evalExpr?, hcap, hsupply, EvalResult.ofOption]

theorem submitCapDecreaseSource {frame : Frame} {evm : State} {cap supply : UInt256}
    (hcap : frame.locals.get? "newSupplyCap" = some (uint256Value cap))
    (hsupply : frame.locals.get? "supplyCap" = some (uint256Value supply)) :
    evalExpr? config frame evm submitCapDecreaseCondition =
      .ok (.bool (decide (cap.toNat < supply.toNat))) := by
  apply naturalLtSource <;> simp only [evalExpr?, hcap, hsupply, EvalResult.ofOption]

theorem submitCapGuardsPass {frame : Frame} {evm : State} {p : MarketParamsData}
    {id cap last cursor : UInt256} (tail : List Stmt)
    (h : SubmitCapReady frame p id cap last cursor)
    (hgood : submitCapGuardsAllowed evm id cap last) :
    ABlock config evm frame (submitCapGuards ++ tail)
      (submitCapCapFrame frame (marketRemovalCap evm id)) tail := by
  obtain ⟨hr, _, _, hp⟩ := marketRemovalGuardValues (evm := evm)
    h.contract h.config h.pending h.id
  constructor
  intro result htail
  apply (ABlock.start.requireStep (by
    rw [submitCapLastSource h.last, decide_eq_true hgood.1])).run
  apply (ABlock.start.requireStep (by simpa only [hgood.2.1, decide_true] using hp)).run
  apply (ABlock.start.requireStep (by simpa only [hgood.2.2.1, decide_true] using hr)).run
  apply ExecBlock.consNormal (ExecStmt.letDecl
    (maxDepositCapRead (evm := evm) h.contract h.config h.id))
  apply (ABlock.start.requireStep ?_).run htail
  rw [submitCapDifferentSource (h.supply _).cap (store_get_self _ _ _),
    decide_eq_true hgood.2.2.2]

theorem submitCapGuardsRevert {frame : Frame} {evm : State} {p : MarketParamsData}
    {id cap last cursor : UInt256} (tail : List Stmt)
    (h : SubmitCapReady frame p id cap last cursor)
    (hbad : ¬ submitCapGuardsAllowed evm id cap last) :
    ExecBlock config frame evm (submitCapGuards ++ tail) .reverted := by
  obtain ⟨hr, _, _, hp⟩ := marketRemovalGuardValues (evm := evm)
    h.contract h.config h.pending h.id
  by_cases hn : last ≠ ⟨0⟩
  case neg =>
    exact ABlock.start.requireRevert (by rw [submitCapLastSource h.last, decide_eq_false hn])
  apply (ABlock.start.requireStep (by rw [submitCapLastSource h.last, decide_eq_true hn])).run
  by_cases hpend : marketRemovalPendingAt evm id = ⟨0⟩
  case neg =>
    exact ABlock.start.requireRevert (by simpa only [hpend, decide_false] using hp)
  apply (ABlock.start.requireStep (by simpa only [hpend, decide_true] using hp)).run
  by_cases hrem : marketRemovalRemovableAt evm id = ⟨0⟩
  case neg =>
    exact ABlock.start.requireRevert (by simpa only [hrem, decide_false] using hr)
  apply (ABlock.start.requireStep (by simpa only [hrem, decide_true] using hr)).run
  apply ExecBlock.consNormal (ExecStmt.letDecl
    (maxDepositCapRead (evm := evm) h.contract h.config h.id))
  apply ABlock.start.requireRevert
  change evalExpr? config (submitCapCapFrame frame (marketRemovalCap evm id)) evm
    submitCapDifferentCondition = .ok (.bool false)
  rw [submitCapDifferentSource (h.supply (marketRemovalCap evm id)).cap (store_get_self _ _ _),
    decide_eq_false (fun hc ↦ hbad ⟨hn, hpend, hrem, hc⟩)]

end Benchmarks.Morpho.MetaMorphoV1_1
