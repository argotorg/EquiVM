import Benchmarks.Midnight.LiquidateCollateralSource
import Benchmarks.Midnight.MaxLifSource

/-! Source execution of the rounded collateral recovery calculation. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def liquidateRecoveryFrame (frame : Frame) (collateral price lltv cursor : UInt256) : Frame :=
  wordLocal (wordLocal (wordLocal frame "__c6" (liquidateRoundedValue collateral price))
    "__c7" (maxLif lltv cursor)) "__c8" (liquidateRecoveryValue collateral price lltv cursor)

def LiquidateRecoverySafe (collateral price lltv cursor : UInt256) : Prop :=
  MulDivUpSafe collateral price liquidatePriceScale ∧ MaxLifSafe lltv cursor ∧
    MulDivUpSafe (liquidateRoundedValue collateral price) lifScale (maxLif lltv cursor)

theorem liquidateRecoverySource {frame : Frame} {evm : State}
    {collateral price : UInt256} {c : CollateralData}
    (hcontract : frame.contract = contract)
    (hc : frame.locals.get? "_collateralParam" = some (Model.collateralValue c.value))
    (hcol : frame.locals.get? "_collateral" = some (.int collateral.toNat))
    (hp : frame.locals.get? "price" = some (.int price.toNat)) (rest : List Stmt) :
    (¬ LiquidateRecoverySafe collateral price c.lltv c.liquidationCursor ∧
      ExecBlock config frame evm ((liquidateLoopBody.drop 8).take 3 ++ rest) .reverted) ∨
    (LiquidateRecoverySafe collateral price c.lltv c.liquidationCursor ∧
      ABlock config evm frame ((liquidateLoopBody.drop 8).take 3 ++ rest)
        (liquidateRecoveryFrame frame collateral price c.lltv c.liquidationCursor) rest) := by
  let f1 := wordLocal frame "__c6" (liquidateRoundedValue collateral price)
  let f2 := wordLocal f1 "__c7" (maxLif c.lltv c.liquidationCursor)
  have ha0 : evalExprs? config frame evm
      [.var "_collateral", .var "price", .intLit 1000000000000000000000000000000000000] =
      .ok [.int collateral.toNat, .int price.toNat, .int liquidatePriceScale.toNat] := by
    simp only [evalExprs?, evalWordLocal hcol, evalWordLocal hp, evalExpr?,
      pure, bind, EvalResult.bind]
    rfl
  by_cases hs1 : MulDivUpSafe collateral price liquidatePriceScale
  · have hstep1 : ExecStmt config frame evm (liquidateLoopBody[8]!) (.ok f1 evm) :=
      callMulDivUp hcontract ha0 hs1
    have hc1 : f1.locals.get? "_collateralParam" = some (Model.collateralValue c.value) := by
      simpa [f1, wordLocal, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] using hc
    have ha1 : evalExprs? config f1 evm
        [.field (.var "_collateralParam") "lltv",
          .field (.var "_collateralParam") "liquidationCursor"] =
        .ok [.int c.lltv.toNat, .int c.liquidationCursor.toNat] := by
      simp only [evalExprs?, evalLiquidateLltv hc1, evalLiquidateCursor hc1,
        pure, bind, EvalResult.bind]
    by_cases hs2 : MaxLifSafe c.lltv c.liquidationCursor
    · have hstep2 : ExecStmt config f1 evm (liquidateLoopBody[9]!) (.ok f2 evm) :=
        callMaxLif hcontract ha1 hs2
      have hc6 : f2.locals.get? "__c6" =
          some (.int (liquidateRoundedValue collateral price).toNat) := by
        simp only [f2, f1, wordLocal, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
        simp
      have hc7 : f2.locals.get? "__c7" =
          some (.int (maxLif c.lltv c.liquidationCursor).toNat) := wordLocal_get ..
      have ha2 : evalExprs? config f2 evm
          [.var "__c6", .intLit 1000000000000000000, .var "__c7"] =
          .ok [.int (liquidateRoundedValue collateral price).toNat, .int lifScale.toNat,
            .int (maxLif c.lltv c.liquidationCursor).toNat] := by
        simp only [evalExprs?, evalWordLocal hc6, evalLifScale, evalWordLocal hc7,
          pure, bind, EvalResult.bind]
      by_cases hs3 : MulDivUpSafe (liquidateRoundedValue collateral price) lifScale
          (maxLif c.lltv c.liquidationCursor)
      · have hstep3 : ExecStmt config f2 evm (liquidateLoopBody[10]!)
            (.ok (liquidateRecoveryFrame frame collateral price c.lltv c.liquidationCursor) evm) :=
          callMulDivUp hcontract ha2 hs3
        exact Or.inr ⟨⟨hs1, hs2, hs3⟩, ⟨fun h ↦ ExecBlock.consNormal hstep1
          (ExecBlock.consNormal hstep2 (ExecBlock.consNormal hstep3 h))⟩⟩
      · exact Or.inl ⟨fun h ↦ hs3 h.2.2, ExecBlock.consNormal hstep1
          (ExecBlock.consNormal hstep2
            (ExecBlock.consRevert (callMulDivUpRevert hcontract ha2 hs3)))⟩
    · exact Or.inl ⟨fun h ↦ hs2 h.2.1, ExecBlock.consNormal hstep1
        (ExecBlock.consRevert (callMaxLifRevert hcontract ha1 hs2))⟩
  · exact Or.inl ⟨fun h ↦ hs1 h.1, ExecBlock.consRevert
      (callMulDivUpRevert hcontract ha0 hs1)⟩

end Benchmarks.Midnight
