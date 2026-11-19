import Benchmarks.Midnight.LiquidateLoopSourceEntry
import Benchmarks.Midnight.HealthArithmeticSource
import Benchmarks.Midnight.LiquidateLoopArithmeticTrace

/-! Source execution of collateral valuation and the debt-capacity update. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem evalLiquidateOracle {cfg : Config} {frame : Frame} {evm : State} {c : CollateralData}
    (hc : frame.locals.get? "_collateralParam" = some (Model.collateralValue c.value)) :
    evalExpr? cfg frame evm (.field (.var "_collateralParam") "oracle") =
      .ok (.address c.oracle) := by
  simp only [evalExpr?, hc, EvalResult.ofOption, bind, EvalResult.bind]
  rfl

theorem evalLiquidateLltv {cfg : Config} {frame : Frame} {evm : State} {c : CollateralData}
    (hc : frame.locals.get? "_collateralParam" = some (Model.collateralValue c.value)) :
    evalExpr? cfg frame evm (.field (.var "_collateralParam") "lltv") =
      .ok (.int c.lltv.toNat) := by
  simp only [evalExpr?, hc, EvalResult.ofOption, bind, EvalResult.bind]
  rfl

theorem evalLiquidateCursor {cfg : Config} {frame : Frame} {evm : State} {c : CollateralData}
    (hc : frame.locals.get? "_collateralParam" = some (Model.collateralValue c.value)) :
    evalExpr? cfg frame evm (.field (.var "_collateralParam") "liquidationCursor") =
      .ok (.int c.liquidationCursor.toNat) := by
  simp only [evalExpr?, hc, EvalResult.ofOption, bind, EvalResult.bind]
  rfl

def liquidateValueFrame (frame : Frame) (collateral price lltv maxDebt : UInt256) : Frame :=
  wordLocal (wordLocal (wordLocal (wordLocal frame "_collateral" collateral)
    "__c4" (healthPriceValue collateral price)) "__c5" (healthCollateralCapacity collateral price lltv))
    "maxDebt" (maxDebt + healthCollateralCapacity collateral price lltv)

theorem liquidateCollateralValueSource {frame : Frame} {evm : State}
    {id borrower index price maxDebt : UInt256} {c : CollateralData}
    (hcontract : frame.contract = contract) (hcanon : borrower.toNat < EVM.addressModulus)
    (hpos : frame.locals.get? "_position" = some (.storageRef (positionRef id borrower) positionType))
    (hi : frame.locals.get? "i" = some (.int index.toNat)) (hindex : index.toNat < 128)
    (hc : frame.locals.get? "_collateralParam" = some (Model.collateralValue c.value))
    (hp : frame.locals.get? "price" = some (.int price.toNat))
    (hm : frame.locals.get? "maxDebt" = some (.int maxDebt.toNat)) (rest : List Stmt) :
    let collateral := healthCollateralWord (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner)
      (positionSlot id borrower + ⟨3⟩) index
    (¬ HealthArithmeticSafe collateral price c.lltv maxDebt ∧
      ExecBlock config frame evm ((liquidateLoopBody.drop 4).take 4 ++ rest) .reverted) ∨
    (HealthArithmeticSafe collateral price c.lltv maxDebt ∧
      ABlock config evm frame ((liquidateLoopBody.drop 4).take 4 ++ rest)
        (liquidateValueFrame frame collateral price c.lltv maxDebt) rest) := by
  dsimp only
  let collateral := healthCollateralWord (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner)
    (positionSlot id borrower + ⟨3⟩) index
  let f0 := wordLocal frame "_collateral" collateral
  let f1 := wordLocal f0 "__c4" (healthPriceValue collateral price)
  let f2 := wordLocal f1 "__c5" (healthCollateralCapacity collateral price c.lltv)
  have hs0 : ExecStmt config frame evm (liquidateLoopBody[4]!) (.ok f0 evm) :=
    ExecStmt.letDecl (evalHealthCollateral hcontract hcanon hpos hi hindex)
  have hp0 : f0.locals.get? "price" = some (.int price.toNat) := by
    simpa [f0, wordLocal, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] using hp
  have hcol0 : f0.locals.get? "_collateral" = some (.int collateral.toNat) :=
    wordLocal_get frame "_collateral" collateral
  have ha0 : evalExprs? config f0 evm
      [.var "_collateral", .var "price", .intLit 1000000000000000000000000000000000000] =
      .ok [.int collateral.toNat, .int price.toNat, .int liquidatePriceScale.toNat] := by
    simp only [evalExprs?, evalWordLocal hcol0,
      evalWordLocal hp0, evalExpr?, pure, bind, EvalResult.bind]
    rfl
  by_cases hmul : collateral.toNat * price.toNat < UInt256.size
  · have hs1 : ExecStmt config f0 evm (liquidateLoopBody[5]!) (.ok f1 evm) :=
      callMulDivDown hcontract ha0 hmul (by decide)
    have hc1 : f1.locals.get? "_collateralParam" = some (Model.collateralValue c.value) := by
      simpa [f1, f0, wordLocal, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] using hc
    have hc4 : f1.locals.get? "__c4" = some (.int (healthPriceValue collateral price).toNat) :=
      wordLocal_get f0 "__c4" _
    have ha1 : evalExprs? config f1 evm
        [.var "__c4", .field (.var "_collateralParam") "lltv", .intLit 1000000000000000000] =
        .ok [.int (healthPriceValue collateral price).toNat, .int c.lltv.toNat, .int lifScale.toNat] := by
      simp only [evalExprs?, evalWordLocal hc4, evalLiquidateLltv hc1,
        evalExpr?, pure, bind, EvalResult.bind]
      rfl
    by_cases hmul2 : (healthPriceValue collateral price).toNat * c.lltv.toNat < UInt256.size
    · have hs2 : ExecStmt config f1 evm (liquidateLoopBody[6]!) (.ok f2 evm) :=
        callMulDivDown hcontract ha1 hmul2 (by decide)
      have hm2 : f2.locals.get? "maxDebt" = some (.int maxDebt.toNat) := by
        simpa [f2, f1, f0, wordLocal, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] using hm
      by_cases hadd : maxDebt.toNat + (healthCollateralCapacity collateral price c.lltv).toNat <
          UInt256.size
      · have hs3 : ExecStmt config f2 evm (liquidateLoopBody[7]!)
            (.ok (liquidateValueFrame frame collateral price c.lltv maxDebt) evm) :=
          execLocalAssign hm2 (checkedAddSourceOk (evalWordLocal hm2)
            (evalWordLocal (wordLocal_get f1 "__c5" _)) hadd)
        exact Or.inr ⟨⟨hmul, hmul2, hadd⟩, ⟨fun h ↦ ExecBlock.consNormal hs0
          (ExecBlock.consNormal hs1 (ExecBlock.consNormal hs2 (ExecBlock.consNormal hs3 h)))⟩⟩
      · exact Or.inl ⟨fun h ↦ hadd h.2.2, ExecBlock.consNormal hs0
          (ExecBlock.consNormal hs1 (ExecBlock.consNormal hs2 (ExecBlock.consRevert
            (ExecStmt.assignExprRevert (checkedAddSourceOverflow
              (a := maxDebt) (b := healthCollateralCapacity collateral price c.lltv)
              (evalWordLocal hm2) (evalWordLocal (wordLocal_get f1 "__c5" _)) (by omega))))))⟩
    · exact Or.inl ⟨fun h ↦ hmul2 h.2.1, ExecBlock.consNormal hs0
        (ExecBlock.consNormal hs1 (ExecBlock.consRevert
          (callMulDivDownRevert hcontract ha1 (fun h ↦ hmul2 h.1))))⟩
  · exact Or.inl ⟨fun h ↦ hmul h.1, ExecBlock.consNormal hs0
      (ExecBlock.consRevert (callMulDivDownRevert hcontract ha0 (fun h ↦ hmul h.1)))⟩

end Benchmarks.Midnight
