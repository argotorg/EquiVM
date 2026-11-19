import Benchmarks.Midnight.CollateralSourceFrame

/-! Source execution and reverts of one collateral-validation iteration. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def collateralLoopBody : List Stmt :=
  match touchMarketInitBody[6]! with | .for _ _ _ body => body | _ => []

def collateralTokenOrder : Expr :=
  .binary .gt (.var "collateralToken") (.var "previousCollateralToken")

def collateralSetPrevious : Stmt :=
  .assign .localVar { base := "previousCollateralToken" } (.var "collateralToken")

theorem collateralLoopBody_tail : collateralLoopBody.drop 6 =
    collateralLifChecks ++ [collateralSetPrevious] := rfl

theorem evalCollateralTokenOrder {cfg : Config} {frame : Frame} {evm : EVM.State}
    {previous token : AccountAddress}
    (hp : frame.locals.get? "previousCollateralToken" = some (.address previous))
    (ht : frame.locals.get? "collateralToken" = some (.address token)) :
    evalExpr? cfg frame evm collateralTokenOrder = .ok (.bool (decide (previous.val < token.val))) := by
  simp only [collateralTokenOrder, evalExpr?, hp, ht, EvalResult.ofOption, bind,
    EvalResult.bind, evalBinaryOp?]
  rfl

theorem collateralTokenPrefix {frame : Frame} {evm : EVM.State}
    {m : MarketData} {i : Nat} {previous : AccountAddress} {c : CollateralData}
    (h : CollateralSourceFrame frame m i previous) (hi : i < m.collaterals.length)
    (hc : m.collaterals[i] = c) :
    ABlock config evm frame collateralLoopBody (collateralTokenFrame frame c)
      (collateralLoopBody.drop 1) :=
  ABlock.start.letStep (evalCollateralField h hi hc "token" (.address c.token) rfl)

theorem collateralLltvPrefix {frame : Frame} {evm : EVM.State}
    {m : MarketData} {i : Nat} {previous : AccountAddress} {c : CollateralData}
    (h : CollateralSourceFrame frame m i previous) (hi : i < m.collaterals.length)
    (hc : m.collaterals[i] = c) (ho : previous.val < c.token.val) :
    ABlock config evm frame collateralLoopBody (collateralLltvFrame frame c)
      (collateralLoopBody.drop 3) := by
  exact ((collateralTokenPrefix h hi hc).requireStep
    ((evalCollateralTokenOrder (collateralTokenFrame_inv h c).previous (store_get_self _ _ _)).trans
      (by rw [decide_eq_true ho])))
    |>.letStep (evalCollateralField (collateralTokenFrame_inv h c) hi hc "lltv" (.int c.lltv.toNat) rfl)

theorem collateralCursorPrefix {frame : Frame} {evm : EVM.State}
    {m : MarketData} {i : Nat} {previous : AccountAddress} {c : CollateralData}
    (h : CollateralSourceFrame frame m i previous) (hi : i < m.collaterals.length)
    (hc : m.collaterals[i] = c) (ho : previous.val < c.token.val)
    (hl : collateralEnabledWord evm false c.lltv ≠ ⟨0⟩) :
    ABlock config evm frame collateralLoopBody (collateralCursorFrame frame c)
      (collateralLoopBody.drop 5) := by
  have hlf := collateralLltvFrame_inv h c
  exact ((collateralLltvPrefix h hi hc ho).requireStep
    ((evalCollateralEnabled false hlf.contract hlf.lltvAbsent (wordLocal_get _ _ _)).trans
      (by rw [decide_eq_true hl])))
    |>.letStep (evalCollateralField hlf hi hc "liquidationCursor" (.int c.liquidationCursor.toNat) rfl)

theorem collateralChecksPrefix {frame : Frame} {evm : EVM.State}
    {m : MarketData} {i : Nat} {previous : AccountAddress} {c : CollateralData}
    (h : CollateralSourceFrame frame m i previous) (hi : i < m.collaterals.length)
    (hc : m.collaterals[i] = c) (ho : previous.val < c.token.val)
    (hl : collateralEnabledWord evm false c.lltv ≠ ⟨0⟩)
    (hcu : collateralEnabledWord evm true c.liquidationCursor ≠ ⟨0⟩) :
    ABlock config evm frame collateralLoopBody (collateralCursorFrame frame c)
      (collateralLoopBody.drop 6) := by
  have hcf := collateralCursorFrame_inv h c
  exact (collateralCursorPrefix h hi hc ho hl).requireStep
    ((evalCollateralEnabled true hcf.contract hcf.cursorAbsent (wordLocal_get _ _ _)).trans
      (by rw [decide_eq_true hcu]))

theorem collateralCursorFrame_lltv (frame : Frame) (c : CollateralData) :
    (collateralCursorFrame frame c).locals.get? "lltv" = some (.int c.lltv.toNat) := by
  rw [collateralCursorFrame, wordLocal_get_ne _ _ _ _ (by decide)]
  exact wordLocal_get _ _ _

theorem collateralLifFrame_token (frame : Frame) (c : CollateralData) :
    (collateralLifFrame frame c).locals.get? "collateralToken" = some (.address c.token) := by
  simp [collateralLifFrame, collateralCursorFrame, collateralLltvFrame, collateralTokenFrame,
    wordLocal, Std.HashMap.getElem_insert]

theorem collateralValidationSource {frame : Frame} {evm : EVM.State}
    {m : MarketData} {i : Nat} {previous : AccountAddress} {c : CollateralData}
    (h : CollateralSourceFrame frame m i previous) (hi : i < m.collaterals.length)
    (hc : m.collaterals[i] = c) (hs : CollateralValid evm previous c) :
    ExecBlock config frame evm collateralLoopBody (.ok (collateralStepFrame frame c) evm) := by
  apply (collateralChecksPrefix h hi hc hs.1 hs.2.1 hs.2.2.1).run
  rw [collateralLoopBody_tail]
  apply (collateralLifSource (collateralCursorFrame_inv h c).contract
    (collateralCursorFrame_lltv frame c) (wordLocal_get _ _ _) hs.2.2.2 [collateralSetPrevious]).run
  apply ExecBlock.consNormal (execLocalAssign (collateralLifFrame_inv h c).previous ?_) ExecBlock.nil
  simp only [evalExpr?, collateralLifFrame_token, EvalResult.ofOption]

theorem collateralValidationSourceRevert {frame : Frame} {evm : EVM.State}
    {m : MarketData} {i : Nat} {previous : AccountAddress} {c : CollateralData}
    (h : CollateralSourceFrame frame m i previous) (hi : i < m.collaterals.length)
    (hc : m.collaterals[i] = c) (hbad : ¬ CollateralValid evm previous c) :
    ExecBlock config frame evm collateralLoopBody .reverted := by
  by_cases ho : previous.val < c.token.val
  · by_cases hl : collateralEnabledWord evm false c.lltv ≠ ⟨0⟩
    · by_cases hcu : collateralEnabledWord evm true c.liquidationCursor ≠ ⟨0⟩
      · apply (collateralChecksPrefix h hi hc ho hl hcu).run
        rw [collateralLoopBody_tail]
        exact collateralLifSourceRevert (collateralCursorFrame_inv h c).contract
          (collateralCursorFrame_lltv frame c) (wordLocal_get _ _ _)
          (fun hs ↦ hbad ⟨ho, hl, hcu, hs⟩) [collateralSetPrevious]
      · apply (collateralCursorPrefix h hi hc ho hl).run
        apply ExecBlock.consRevert
        exact ExecStmt.requireFalse ((evalCollateralEnabled true
          (collateralCursorFrame_inv h c).contract (collateralCursorFrame_inv h c).cursorAbsent
          (wordLocal_get _ _ _)).trans (by rw [decide_eq_false hcu]))
    · apply (collateralLltvPrefix h hi hc ho).run
      apply ExecBlock.consRevert
      exact ExecStmt.requireFalse ((evalCollateralEnabled false
        (collateralLltvFrame_inv h c).contract (collateralLltvFrame_inv h c).lltvAbsent
        (wordLocal_get _ _ _)).trans (by rw [decide_eq_false hl]))
  · apply (collateralTokenPrefix h hi hc).run
    apply ExecBlock.consRevert
    exact ExecStmt.requireFalse ((evalCollateralTokenOrder
      (collateralTokenFrame_inv h c).previous (store_get_self _ _ _)).trans
      (by rw [decide_eq_false ho]))

end Benchmarks.Midnight
