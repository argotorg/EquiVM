import Benchmarks.Midnight.LiquidateConversion
import Benchmarks.Midnight.LiquidateMaxLifSource

variable {fork : Ethereum.Fork}

/-! Source execution of liquidation's seized-amount and repaid-amount branches. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def liquidateSeizeFrame (frame : Frame) (seized price lif : UInt256) : Frame :=
  wordLocal (wordLocal (wordLocal frame "__c19" (mulDivUp seized price liquidatePriceScale))
    "__c20" (liquidateRepaidAmount seized price lif)) "repaidUnits"
    (liquidateRepaidAmount seized price lif)

def liquidateRepayFrame (frame : Frame) (repaid price lif : UInt256) : Frame :=
  wordLocal (wordLocal (wordLocal frame "__c21" (mulDivDown repaid lif lifScale))
    "__c22" (liquidateSeizedAmount repaid price lif)) "seizedAssets"
    (liquidateSeizedAmount repaid price lif)

theorem evalLiquidatePriceScale {cfg : Config} {frame : Frame} {evm : State} :
    evalExpr? cfg frame evm (.intLit 1000000000000000000000000000000000000) =
      .ok (.int liquidatePriceScale.toNat) := by
  simp only [evalExpr?, pure]; rfl

theorem liquidateSeizeSource {frame : Frame} {evm : State} {seized repaid price lif : UInt256}
    (hc : frame.contract = contract)
    (hs : frame.locals.get? "seizedAssets" = some (.int seized.toNat))
    (hr : frame.locals.get? "repaidUnits" = some (.int repaid.toNat))
    (hp : frame.locals.get? "liquidatedCollatPrice" = some (.int price.toNat))
    (hl : frame.locals.get? "lif" = some (.int lif.toNat)) (hpos : 0 < seized.toNat) :
    (¬ LiquidateSeizeSafe seized price lif ∧
      ExecStmt fork config frame evm (liquidateAmountsBody[4]!) .reverted) ∨
    (LiquidateSeizeSafe seized price lif ∧
      ExecStmt fork config frame evm (liquidateAmountsBody[4]!)
        (.ok (liquidateSeizeFrame frame seized price lif) evm)) := by
  let value := mulDivUp seized price liquidatePriceScale
  let amount := liquidateRepaidAmount seized price lif
  let f1 := wordLocal frame "__c19" value
  let f2 := wordLocal f1 "__c20" amount
  have hcond : evalExpr? config frame evm
      (.binary .gt (.var "seizedAssets") (.intLit 0)) = .ok (.bool true) := by
    rw [evalExpr_uint256_var_positive evm "seizedAssets" seized hs, decide_eq_true hpos]
  have ha0 : evalExprs? config frame evm
      [.var "seizedAssets", .var "liquidatedCollatPrice",
        .intLit 1000000000000000000000000000000000000] =
      .ok [.int seized.toNat, .int price.toNat, .int liquidatePriceScale.toNat] := by
    simp only [evalExprs?, evalWordLocal hs, evalWordLocal hp, evalLiquidatePriceScale,
      bind, pure, EvalResult.bind]
  by_cases hfirst : MulDivUpSafe seized price liquidatePriceScale
  · have hs0 := callMulDivUp (fork := fork) (name := "__c19") hc ha0 hfirst
    have hl1 : f1.locals.get? "lif" = some (.int lif.toNat) := by
      simpa only [f1, wordLocal_get_ne _ _ _ _ (show "__c19" ≠ "lif" by decide)] using hl
    have hv1 : f1.locals.get? "__c19" = some (.int value.toNat) := wordLocal_get _ _ _
    have ha1 : evalExprs? config f1 evm
        [.var "__c19", .intLit 1000000000000000000, .var "lif"] =
        .ok [.int value.toNat, .int lifScale.toNat, .int lif.toNat] := by
      simp only [evalExprs?, evalWordLocal hv1,
        evalLifScale, evalWordLocal hl1, bind, pure, EvalResult.bind]
    by_cases hsecond : MulDivUpSafe value lifScale lif
    · have hs1 := callMulDivUp (fork := fork) (frame := f1) (name := "__c20") hc ha1 hsecond
      have hr2 : f2.locals.get? "repaidUnits" = some (.int repaid.toNat) := by
        simpa only [f2, f1,
          wordLocal_get_ne _ _ _ _ (show "__c20" ≠ "repaidUnits" by decide),
          wordLocal_get_ne _ _ _ _ (show "__c19" ≠ "repaidUnits" by decide)] using hr
      exact Or.inr ⟨⟨hfirst, hsecond⟩, ExecStmt.iteTrue hcond
        (ExecBlock.consNormal hs0 (ExecBlock.consNormal hs1 (ExecBlock.consNormal
          (execLocalAssign hr2 (evalWordLocal (wordLocal_get _ "__c20" _))) ExecBlock.nil)))⟩
    · exact Or.inl ⟨fun h ↦ hsecond h.2, ExecStmt.iteTrue hcond
        (ExecBlock.consNormal hs0 (ExecBlock.consRevert
          (callMulDivUpRevert (frame := f1) hc ha1 hsecond)))⟩
  · exact Or.inl ⟨fun h ↦ hfirst h.1, ExecStmt.iteTrue hcond
      (ExecBlock.consRevert (callMulDivUpRevert hc ha0 hfirst))⟩

theorem liquidateRepaySource {frame : Frame} {evm : State} {seized repaid price lif : UInt256}
    (hc : frame.contract = contract)
    (hs : frame.locals.get? "seizedAssets" = some (.int seized.toNat))
    (hr : frame.locals.get? "repaidUnits" = some (.int repaid.toNat))
    (hp : frame.locals.get? "liquidatedCollatPrice" = some (.int price.toNat))
    (hl : frame.locals.get? "lif" = some (.int lif.toNat)) (hz : seized.toNat = 0) :
    (¬ LiquidateRepaySafe repaid price lif ∧
      ExecStmt fork config frame evm (liquidateAmountsBody[4]!) .reverted) ∨
    (LiquidateRepaySafe repaid price lif ∧
      ExecStmt fork config frame evm (liquidateAmountsBody[4]!)
        (.ok (liquidateRepayFrame frame repaid price lif) evm)) := by
  let value := mulDivDown repaid lif lifScale
  let amount := liquidateSeizedAmount repaid price lif
  let f1 := wordLocal frame "__c21" value
  let f2 := wordLocal f1 "__c22" amount
  have hcond : evalExpr? config frame evm
      (.binary .gt (.var "seizedAssets") (.intLit 0)) = .ok (.bool false) := by
    rw [evalExpr_uint256_var_positive evm "seizedAssets" seized hs, decide_eq_false (by omega)]
  have ha0 : evalExprs? config frame evm
      [.var "repaidUnits", .var "lif", .intLit 1000000000000000000] =
      .ok [.int repaid.toNat, .int lif.toNat, .int lifScale.toNat] := by
    simp only [evalExprs?, evalWordLocal hr, evalWordLocal hl, evalLifScale,
      bind, pure, EvalResult.bind]
  by_cases hfirst : repaid.toNat * lif.toNat < UInt256.size
  · have hs0 := callMulDivDown (fork := fork) (name := "__c21") hc ha0 hfirst (by decide)
    have hp1 : f1.locals.get? "liquidatedCollatPrice" = some (.int price.toNat) := by
      simpa only [f1,
        wordLocal_get_ne _ _ _ _ (show "__c21" ≠ "liquidatedCollatPrice" by decide)] using hp
    have hv1 : f1.locals.get? "__c21" = some (.int value.toNat) := wordLocal_get _ _ _
    have ha1 : evalExprs? config f1 evm
        [.var "__c21", .intLit 1000000000000000000000000000000000000,
          .var "liquidatedCollatPrice"] =
        .ok [.int value.toNat, .int liquidatePriceScale.toNat, .int price.toNat] := by
      simp only [evalExprs?, evalWordLocal hv1,
        evalLiquidatePriceScale, evalWordLocal hp1, bind, pure, EvalResult.bind]
    by_cases hsecond : value.toNat * liquidatePriceScale.toNat < UInt256.size ∧ price ≠ ⟨0⟩
    · have hs1 := callMulDivDown (fork := fork) (frame := f1) (name := "__c22") hc ha1 hsecond.1 hsecond.2
      have hs2 : f2.locals.get? "seizedAssets" = some (.int seized.toNat) := by
        simpa only [f2, f1,
          wordLocal_get_ne _ _ _ _ (show "__c22" ≠ "seizedAssets" by decide),
          wordLocal_get_ne _ _ _ _ (show "__c21" ≠ "seizedAssets" by decide)] using hs
      exact Or.inr ⟨⟨hfirst, hsecond⟩, ExecStmt.iteFalse hcond
        (ExecBlock.consNormal hs0 (ExecBlock.consNormal hs1 (ExecBlock.consNormal
          (execLocalAssign hs2 (evalWordLocal (wordLocal_get _ "__c22" _))) ExecBlock.nil)))⟩
    · exact Or.inl ⟨fun h ↦ hsecond h.2, ExecStmt.iteFalse hcond
        (ExecBlock.consNormal hs0 (ExecBlock.consRevert
          (callMulDivDownRevert (frame := f1) hc ha1 hsecond)))⟩
  · exact Or.inl ⟨fun h ↦ hfirst h.1, ExecStmt.iteFalse hcond
      (ExecBlock.consRevert (callMulDivDownRevert hc ha0 (fun h ↦ hfirst h.1)))⟩

end Benchmarks.Midnight
