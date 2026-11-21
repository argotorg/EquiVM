import Benchmarks.Midnight.TouchMarketSourceBase
import Benchmarks.Midnight.PositionViewSourceBase

/-! The chain, address, maturity, and collateral-count checks before market initialization. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def TouchMarketHeaderSafe (I : ExecutionEnv) (m : MarketData) : Prop :=
  m.chainId.toNat = Ethereum.chainId ∧ m.midnight = I.codeOwner ∧
    (UInt256.ofNat I.header.timestamp).toNat + 3153600000 < UInt256.size ∧
    m.maturity.toNat ≤ (UInt256.ofNat I.header.timestamp).toNat + 3153600000 ∧
    0 < m.collaterals.length ∧ m.collaterals.length ≤ 128

def touchMarketMaturityLimit : Expr :=
  .inRange (.uint ⟨256, by decide⟩) (.binary .add (.env .timestamp) (.intLit 3153600000))

def marketCollateralLength : Expr :=
  .arrayLength .localVar { base := "market", steps := [.field "collateralParams"] }

theorem touchMarketHeader_shape : touchMarketInitBody =
    [.require (.binary .eq (.field (.var "market") "chainId") (.env .chainid)),
     .require (.binary .eq (.field (.var "market") "midnight") (.env .this)),
     .require (.binary .le (.field (.var "market") "maturity") touchMarketMaturityLimit),
     .require (.binary .gt marketCollateralLength (.intLit 0)),
     .require (.binary .le marketCollateralLength (.intLit 128))] ++
       touchMarketInitBody.drop 5 := rfl

theorem evalMarketChain {cfg : Config} {frame : Frame} {evm : EVM.State} {m : MarketData}
    (hm : frame.locals.get? "market" = some (Model.marketValue m.value)) :
    evalExpr? cfg frame evm (.field (.var "market") "chainId") = .ok (.int m.chainId.toNat) := by
  simp only [evalExpr?, hm, EvalResult.ofOption, bind, EvalResult.bind]; rfl

theorem evalMarketMidnight {cfg : Config} {frame : Frame} {evm : EVM.State} {m : MarketData}
    (hm : frame.locals.get? "market" = some (Model.marketValue m.value)) :
    evalExpr? cfg frame evm (.field (.var "market") "midnight") = .ok (.address m.midnight) := by
  simp only [evalExpr?, hm, EvalResult.ofOption, bind, EvalResult.bind]; rfl

theorem evalMarketCollateralLength {cfg : Config} {frame : Frame} {evm : EVM.State}
    {m : MarketData} (hm : frame.locals.get? "market" = some (Model.marketValue m.value)) :
    evalExpr? cfg frame evm marketCollateralLength = .ok (.int m.collaterals.length) := by
  simp only [marketCollateralLength, evalExpr?, hm]
  simp [readLocalPath?, Model.marketValue, MarketData.value, lookupField?, lookupAssoc,
    bind, pure, EvalResult.bind, EvalResult.ofOption]

theorem evalTouchMarketChain {cfg : Config} {frame : Frame} {evm : EVM.State} {m : MarketData}
    (hm : frame.locals.get? "market" = some (Model.marketValue m.value)) :
    evalExpr? cfg frame evm (.binary .eq (.field (.var "market") "chainId") (.env .chainid)) =
      .ok (.bool (decide (m.chainId.toNat = Ethereum.chainId))) := by
  rw [evalExpr_binary_nonshort (by decide) (by decide), evalMarketChain hm]
  simp only [evalExpr?, envValue, evalBinaryOp?, bind, pure, EvalResult.bind,
    Reasoning.VyperDispatch.value_int_beq, Int.ofNat_eq_natCast, Nat.cast_inj]

theorem evalTouchMarketAddress {cfg : Config} {frame : Frame} {evm : EVM.State} {m : MarketData}
    (hm : frame.locals.get? "market" = some (Model.marketValue m.value)) :
    evalExpr? cfg frame evm (.binary .eq (.field (.var "market") "midnight") (.env .this)) =
      .ok (.bool (decide (m.midnight = evm.executionEnv.codeOwner))) := by
  rw [evalExpr_binary_nonshort (by decide) (by decide), evalMarketMidnight hm]
  simp only [evalExpr?, envValue, evalBinaryOp?, bind, pure, EvalResult.bind,
    Reasoning.VyperDispatch.value_address_beq]

theorem evalTouchMarketLimit {cfg : Config} {frame : Frame} {evm : EVM.State}
    (hfit : (UInt256.ofNat evm.executionEnv.header.timestamp).toNat + 3153600000 < UInt256.size) :
    evalExpr? cfg frame evm touchMarketMaturityLimit = .ok (.int
      ((UInt256.ofNat evm.executionEnv.header.timestamp) + UInt256.ofNat 3153600000).toNat) := by
  apply checkedAddSourceOk (by simp only [evalExpr?, envValue, pure])
    (b := UInt256.ofNat 3153600000) (by simp only [evalExpr?, pure]; rfl) hfit

theorem evalTouchMarketLimitRevert {cfg : Config} {frame : Frame} {evm : EVM.State}
    (hover : UInt256.size ≤ (UInt256.ofNat evm.executionEnv.header.timestamp).toNat + 3153600000) :
    evalExpr? cfg frame evm touchMarketMaturityLimit = .revert := by
  apply checkedAddSourceOverflow (by simp only [evalExpr?, envValue, pure])
    (b := UInt256.ofNat 3153600000) (by simp only [evalExpr?, pure]; rfl) hover

theorem evalTouchMarketMaturity {cfg : Config} {frame : Frame} {evm : EVM.State} {m : MarketData}
    (hm : frame.locals.get? "market" = some (Model.marketValue m.value))
    (hfit : (UInt256.ofNat evm.executionEnv.header.timestamp).toNat + 3153600000 < UInt256.size) :
    evalExpr? cfg frame evm
      (.binary .le (.field (.var "market") "maturity") touchMarketMaturityLimit) =
      .ok (.bool (decide (m.maturity.toNat ≤
        (UInt256.ofNat evm.executionEnv.header.timestamp).toNat + 3153600000))) := by
  rw [evalExpr_binary_nonshort (by decide) (by decide), evalMarketMaturity hm,
    evalTouchMarketLimit hfit]
  simp only [bind, EvalResult.bind, evalBinaryOp?, Int.ofNat_le]
  rw [uadd_word_ofNat_toNat _ _ hfit]

theorem evalTouchMarketNonempty {cfg : Config} {frame : Frame} {evm : EVM.State} {m : MarketData}
    (hm : frame.locals.get? "market" = some (Model.marketValue m.value)) :
    evalExpr? cfg frame evm (.binary .gt marketCollateralLength (.intLit 0)) =
      .ok (.bool (decide (0 < m.collaterals.length))) := by
  rw [evalExpr_binary_nonshort (by decide) (by decide), evalMarketCollateralLength hm]
  simp only [evalExpr?, bind, pure, EvalResult.bind, evalBinaryOp?, Int.natCast_pos]

theorem evalTouchMarketCount {cfg : Config} {frame : Frame} {evm : EVM.State} {m : MarketData}
    (hm : frame.locals.get? "market" = some (Model.marketValue m.value)) :
    evalExpr? cfg frame evm (.binary .le marketCollateralLength (.intLit 128)) =
      .ok (.bool (decide (m.collaterals.length ≤ 128))) := by
  rw [evalExpr_binary_nonshort (by decide) (by decide), evalMarketCollateralLength hm]
  simp only [evalExpr?, bind, pure, EvalResult.bind, evalBinaryOp?]
  norm_cast

theorem touchMarketHeaderSource {frame : Frame} {evm : EVM.State} {m : MarketData}
    (hm : frame.locals.get? "market" = some (Model.marketValue m.value))
    (hs : TouchMarketHeaderSafe evm.executionEnv m) :
    ABlock config evm frame touchMarketInitBody frame (touchMarketInitBody.drop 5) := by
  rw [touchMarketHeader_shape]
  exact ABlock.start
    |>.requireStep ((evalTouchMarketChain hm).trans (by rw [decide_eq_true hs.1]))
    |>.requireStep ((evalTouchMarketAddress hm).trans (by rw [decide_eq_true hs.2.1]))
    |>.requireStep ((evalTouchMarketMaturity hm hs.2.2.1).trans
      (by rw [decide_eq_true hs.2.2.2.1]))
    |>.requireStep ((evalTouchMarketNonempty hm).trans (by rw [decide_eq_true hs.2.2.2.2.1]))
    |>.requireStep ((evalTouchMarketCount hm).trans (by rw [decide_eq_true hs.2.2.2.2.2]))

theorem touchMarketHeaderRevert {frame : Frame} {evm : EVM.State} {m : MarketData}
    (hm : frame.locals.get? "market" = some (Model.marketValue m.value))
    (hbad : ¬ TouchMarketHeaderSafe evm.executionEnv m) :
    ExecBlock config frame evm touchMarketInitBody .reverted := by
  rw [touchMarketHeader_shape]
  by_cases hc : m.chainId.toNat = Ethereum.chainId
  · apply ExecBlock.consNormal (ExecStmt.requireTrue
      ((evalTouchMarketChain hm).trans (by rw [decide_eq_true hc])))
    by_cases ha : m.midnight = evm.executionEnv.codeOwner
    · apply ExecBlock.consNormal (ExecStmt.requireTrue
        ((evalTouchMarketAddress hm).trans (by rw [decide_eq_true ha])))
      by_cases ht : (UInt256.ofNat evm.executionEnv.header.timestamp).toNat + 3153600000 < UInt256.size
      · by_cases hmat : m.maturity.toNat ≤
          (UInt256.ofNat evm.executionEnv.header.timestamp).toNat + 3153600000
        · apply ExecBlock.consNormal (ExecStmt.requireTrue
            ((evalTouchMarketMaturity hm ht).trans (by rw [decide_eq_true hmat])))
          by_cases hn : 0 < m.collaterals.length
          · apply ExecBlock.consNormal (ExecStmt.requireTrue
              ((evalTouchMarketNonempty hm).trans (by rw [decide_eq_true hn])))
            apply ExecBlock.consRevert
            exact ExecStmt.requireFalse ((evalTouchMarketCount hm).trans
              (by rw [decide_eq_false (fun h ↦ hbad ⟨hc, ha, ht, hmat, hn, h⟩)]))
          · exact ExecBlock.consRevert (ExecStmt.requireFalse
              ((evalTouchMarketNonempty hm).trans (by rw [decide_eq_false hn])))
        · exact ExecBlock.consRevert (ExecStmt.requireFalse
            ((evalTouchMarketMaturity hm ht).trans (by rw [decide_eq_false hmat])))
      · apply ExecBlock.consRevert
        apply ExecStmt.requireRevert
        rw [evalExpr_binary_nonshort (by decide) (by decide), evalMarketMaturity hm]
        simp only [bind, EvalResult.bind, evalTouchMarketLimitRevert (Nat.le_of_not_gt ht)]
    · exact ExecBlock.consRevert (ExecStmt.requireFalse
        ((evalTouchMarketAddress hm).trans (by rw [decide_eq_false ha])))
  · exact ExecBlock.consRevert (ExecStmt.requireFalse
      ((evalTouchMarketChain hm).trans (by rw [decide_eq_false hc])))

end Benchmarks.Midnight
