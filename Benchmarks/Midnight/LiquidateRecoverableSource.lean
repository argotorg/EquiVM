import Benchmarks.Midnight.LiquidateRecoverable
import Benchmarks.Midnight.LiquidateMaxRepaidSource
import Benchmarks.Midnight.LiquidateConversionSource

/-! Source collateral lookup and rounded-down valuation for the recovery-threshold check. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

def liquidateThresholdBody : List Stmt :=
  match liquidateRcfBody[1]! with
  | .ite _ body _ => body
  | _ => []

def liquidateRecoverableFrame (frame : Frame) (collateral price lif : UInt256) : Frame :=
  wordLocal (wordLocal frame "value" (mulDivDown collateral price liquidatePriceScale))
    "repayable" (liquidateRecoverable collateral price lif)

theorem liquidateRecoverableSource {frame : Frame} {evm : State} {id borrower index price lif : UInt256}
    (hc : frame.contract = contract) (hcanon : borrower.toNat < EVM.addressModulus)
    (hp : frame.locals.get? "_position" = some (.storageRef (positionRef id borrower) positionType))
    (hi : frame.locals.get? "collateralIndex" = some (.int index.toNat))
    (hv : frame.locals.get? "liquidatedCollatPrice" = some (.int price.toNat))
    (hl : frame.locals.get? "lif" = some (.int lif.toNat)) :
    let collateral := healthCollateralWord (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner)
      (positionSlot id borrower + ⟨3⟩) index
    (¬ (index.toNat < 128 ∧ LiquidateRecoverableSafe collateral price lif) ∧
      ExecBlock config frame evm (liquidateThresholdBody.take 2) .reverted) ∨
    (index.toNat < 128 ∧ LiquidateRecoverableSafe collateral price lif ∧
      ExecBlock config frame evm (liquidateThresholdBody.take 2)
        (.ok (liquidateRecoverableFrame frame collateral price lif) evm)) := by
  dsimp only
  let collateral := healthCollateralWord (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner)
    (positionSlot id borrower + ⟨3⟩) index
  let value := mulDivDown collateral price liquidatePriceScale
  let f1 := wordLocal frame "value" value
  by_cases hidx : index.toNat < 128
  · have ha0 : evalExprs? config frame evm
        [positionCollateralExpr "collateralIndex", .var "liquidatedCollatPrice",
          .intLit 1000000000000000000000000000000000000] =
        .ok [.int collateral.toNat, .int price.toNat, .int liquidatePriceScale.toNat] := by
      simp only [evalExprs?, evalPositionCollateral "collateralIndex" hc hcanon hp hi hidx,
        evalWordLocal hv, evalLiquidatePriceScale, bind, pure, EvalResult.bind]
      rfl
    by_cases hfirst : collateral.toNat * price.toNat < UInt256.size
    · have hs0 := callMulDivDown (name := "value") hc ha0 hfirst (by decide)
      have hv1 : f1.locals.get? "value" = some (.int value.toNat) := wordLocal_get _ _ _
      have hl1 : f1.locals.get? "lif" = some (.int lif.toNat) := by
        simpa only [f1, wordLocal_get_ne _ _ _ _ (show "value" ≠ "lif" by decide)] using hl
      have ha1 : evalExprs? config f1 evm
          [.var "value", .intLit 1000000000000000000, .var "lif"] =
          .ok [.int value.toNat, .int lifScale.toNat, .int lif.toNat] := by
        simp only [evalExprs?, evalWordLocal hv1, evalLifScale, evalWordLocal hl1,
          bind, pure, EvalResult.bind]
      by_cases hsecond : value.toNat * lifScale.toNat < UInt256.size ∧ lif ≠ ⟨0⟩
      · exact Or.inr ⟨hidx, ⟨hfirst, hsecond⟩, ExecBlock.consNormal hs0
          (ExecBlock.consNormal (callMulDivDown (frame := f1) hc ha1 hsecond.1 hsecond.2)
            ExecBlock.nil)⟩
      · exact Or.inl ⟨fun h ↦ hsecond h.2.2, ExecBlock.consNormal hs0
          (ExecBlock.consRevert (callMulDivDownRevert (frame := f1) hc ha1 hsecond))⟩
    · exact Or.inl ⟨fun h ↦ hfirst h.2.1, ExecBlock.consRevert
        (callMulDivDownRevert hc ha0 (fun h ↦ hfirst h.1))⟩
  · refine Or.inl ⟨fun h ↦ hidx h.1, ExecBlock.consRevert (ExecStmt.internalCallArgsRevert ?_)⟩
    change evalExprs? config frame evm
      [positionCollateralExpr "collateralIndex", .var "liquidatedCollatPrice",
        .intLit 1000000000000000000000000000000000000] = .revert
    simp only [evalExprs?, evalPositionCollateralRevert "collateralIndex" hc hp hi hidx,
      bind, EvalResult.bind]

end Benchmarks.Midnight
