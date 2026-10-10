import Benchmarks.Morpho.MetaMorphoV1_1.MarketRemovalSyntax

/-! Source evaluation and short-circuit failure of the four market-removal guards. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1

open SourceMemory

theorem marketRemovalGuardValues {frame : Frame} {evm : State} {id : UInt256}
    (hcontract : frame.contract = contract) (hconfig : frame.locals.get? "config" = none)
    (hpending : frame.locals.get? "pendingCap" = none)
    (hid : frame.locals.get? "id" = some (wordBytes32Value id)) :
    evalExpr? config frame evm (marketRemovalTimeCondition false) =
      .ok (.bool (decide (marketRemovalRemovableAt evm id = ⟨0⟩))) ∧
    evalExpr? config frame evm marketRemovalCapCondition =
      .ok (.bool (decide (marketRemovalCap evm id = ⟨0⟩))) ∧
    evalExpr? config frame evm marketRemovalEnabledExpr =
      .ok (.bool (decide (marketRemovalEnabledWord evm id ≠ ⟨0⟩))) ∧
    evalExpr? config frame evm (marketRemovalTimeCondition true) =
      .ok (.bool (decide (marketRemovalPendingAt evm id = ⟨0⟩))) := by
  have hz : evalExpr? config frame evm (.intLit 0) = .ok (uint256Value ⟨0⟩) := by
    simp only [evalExpr?]; rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hr := marketRemovalTimeRead false (evm := evm) hcontract hconfig hid
    simp only [Bool.false_eq_true, if_false] at hr
    exact evalExpr_wordEq hr hz
  · exact evalExpr_wordEq (maxDepositCapRead (evm := evm) hcontract hconfig hid) hz
  · exact marketRemovalEnabledRead (evm := evm) hcontract hconfig hid
  · have hr := marketRemovalTimeRead true (evm := evm) hcontract hpending hid
    simp only [if_true] at hr
    exact evalExpr_wordEq hr hz

theorem marketRemovalGuardsPass {frame : Frame} {evm : State} {id : UInt256}
    (tail : List Stmt) (hcontract : frame.contract = contract)
    (hconfig : frame.locals.get? "config" = none)
    (hpending : frame.locals.get? "pendingCap" = none)
    (hid : frame.locals.get? "id" = some (wordBytes32Value id))
    (hgood : marketRemovalAllowed evm id) :
    ABlock config evm frame (marketRemovalGuards ++ tail) frame tail := by
  obtain ⟨h0, h1, h2, h3⟩ :=
    marketRemovalGuardValues (evm := evm) hcontract hconfig hpending hid
  constructor
  intro result htail
  apply (ABlock.start.requireStep (by simpa only [hgood.1, decide_true] using h0)).run
  apply (ABlock.start.requireStep (by simpa only [hgood.2.1, decide_true] using h1)).run
  apply (ABlock.start.requireStep (by
    simpa only [decide_eq_true hgood.2.2.1] using h2)).run
  exact (ABlock.start.requireStep (by simpa only [hgood.2.2.2, decide_true] using h3)).run htail

theorem marketRemovalGuardsRevert {frame : Frame} {evm : State} {id : UInt256}
    (tail : List Stmt) (hcontract : frame.contract = contract)
    (hconfig : frame.locals.get? "config" = none)
    (hpending : frame.locals.get? "pendingCap" = none)
    (hid : frame.locals.get? "id" = some (wordBytes32Value id))
    (hbad : ¬ marketRemovalAllowed evm id) :
    ExecBlock config frame evm (marketRemovalGuards ++ tail) .reverted := by
  obtain ⟨h0, h1, h2, h3⟩ :=
    marketRemovalGuardValues (evm := evm) hcontract hconfig hpending hid
  by_cases hc0 : marketRemovalRemovableAt evm id = ⟨0⟩
  case neg =>
    exact ABlock.start.requireRevert (by simpa only [hc0, decide_false] using h0)
  apply (ABlock.start.requireStep (by simpa only [hc0, decide_true] using h0)).run
  by_cases hc1 : marketRemovalCap evm id = ⟨0⟩
  case neg =>
    exact ABlock.start.requireRevert (by simpa only [hc1, decide_false] using h1)
  apply (ABlock.start.requireStep (by simpa only [hc1, decide_true] using h1)).run
  by_cases hc2 : marketRemovalEnabledWord evm id ≠ ⟨0⟩
  case neg =>
    exact ABlock.start.requireRevert (by simpa only [hc2, decide_false] using h2)
  apply (ABlock.start.requireStep (by
    simpa only [decide_eq_true hc2] using h2)).run
  have hc3 : ¬ marketRemovalPendingAt evm id = ⟨0⟩ := fun h ↦ hbad ⟨hc0, hc1, hc2, h⟩
  exact ABlock.start.requireRevert (by simpa only [hc3, decide_false] using h3)

theorem marketRemovalFrameReady (evm : State) (imms : Store) (out : ByteArray) :
    (marketRemovalFrame evm imms out).contract = contract ∧
    (marketRemovalFrame evm imms out).locals.get? "config" = none ∧
    (marketRemovalFrame evm imms out).locals.get? "pendingCap" = none ∧
    (marketRemovalFrame evm imms out).locals.get? "timelock" = none ∧
    (marketRemovalFrame evm imms out).locals.get? "id" =
      some (wordBytes32Value (marketParamsData out).id) := by
  simp [marketRemovalFrame, marketRemovalRoleFrame, marketRemovalParamsFrame,
    marketRemovalCalldataFrame]

end Benchmarks.Morpho.MetaMorphoV1_1
