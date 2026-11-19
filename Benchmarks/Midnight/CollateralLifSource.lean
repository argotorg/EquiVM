import Benchmarks.Midnight.CollateralLifTrace
import Benchmarks.Midnight.MaxLifSource
import Reasoning.VyperDispatch

/-! Source proofs for the final arithmetic checks in one collateral-validation iteration. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def collateralLifCap : Expr := .binary .le (.var "_maxLif")
  (.inRange (.uint ⟨256, by decide⟩) (.binary .mul (.intLit 2) (.intLit 1000000000000000000)))

def collateralLifProduct : Expr :=
  .inRange (.uint ⟨256, by decide⟩) (.binary .mul (.var "lltv") (.var "_maxLif"))

def collateralLifGuard : Expr :=
  .binary .or (.binary .eq (.var "lltv") (.intLit 1000000000000000000))
    (.binary .le collateralLifProduct (.intLit 999000000000000000000000000000000000))

def collateralLifChecks : List Stmt :=
  [.internalCall "maxLif" [.var "lltv", .var "liquidationCursor"] "_maxLif",
    .require collateralLifCap, .require collateralLifGuard]

theorem evalCollateralLifCap {cfg : Config} {frame : Frame} {evm : EVM.State} {w : UInt256}
    (hw : frame.locals.get? "_maxLif" = some (.int w.toNat)) :
    evalExpr? cfg frame evm collateralLifCap =
      .ok (.bool (decide (w.toNat ≤ 2000000000000000000))) := by
  have he : evalExpr? cfg frame evm
      (.inRange (.uint ⟨256, by decide⟩) (.binary .mul (.intLit 2) (.intLit 1000000000000000000))) =
      .ok (.int 2000000000000000000) := by
    simp only [evalExpr?, evalBinaryOp?, pure, bind, EvalResult.bind]
    decide +kernel
  rw [collateralLifCap, evalExpr_binary_nonshort (by decide) (by decide), evalWordLocal hw, he]
  simp only [bind, EvalResult.bind, evalBinaryOp?]
  norm_cast

theorem evalCollateralLifEq {cfg : Config} {frame : Frame} {evm : EVM.State} {lltv : UInt256}
    (hl : frame.locals.get? "lltv" = some (.int lltv.toNat)) :
    evalExpr? cfg frame evm (.binary .eq (.var "lltv") (.intLit 1000000000000000000)) =
      .ok (.bool (decide (lltv = lifScale))) := by
  rw [evalExpr_binary_nonshort (by decide) (by decide), evalWordLocal hl, evalLifScale]
  simp only [bind, EvalResult.bind, evalBinaryOp?, Reasoning.VyperDispatch.value_int_beq,
    Int.ofNat_inj]
  have he : lltv.toNat = lifScale.toNat ↔ lltv = lifScale := ⟨u256_inj, congrArg UInt256.toNat⟩
  simp only [he]

theorem evalCollateralLifGuard {cfg : Config} {frame : Frame} {evm : EVM.State}
    {lltv cursor : UInt256} (hl : frame.locals.get? "lltv" = some (.int lltv.toNat))
    (hf : frame.locals.get? "_maxLif" = some (.int (maxLif lltv cursor).toNat))
    (hs : MaxLifSafe lltv cursor) (hb : (maxLif lltv cursor).toNat ≤ 2000000000000000000) :
    evalExpr? cfg frame evm collateralLifGuard =
      .ok (.bool (decide (lltv = lifScale ∨
        (UInt256.mul lltv (maxLif lltv cursor)).toNat ≤ 999000000000000000000000000000000000))) := by
  have hp := checkedMulSourceOk (evalWordLocal (cfg := cfg) (evm := evm) hl)
    (evalWordLocal hf) (collateralLifProductBound hs hb)
  have hr : evalExpr? cfg frame evm
      (.binary .le collateralLifProduct (.intLit 999000000000000000000000000000000000)) =
      .ok (.bool (decide ((UInt256.mul lltv (maxLif lltv cursor)).toNat ≤
        999000000000000000000000000000000000))) := by
    rw [evalExpr_binary_nonshort (by decide) (by decide)]
    change ((evalExpr? cfg frame evm _ >>= fun a ↦ evalExpr? cfg frame evm _ >>=
      fun b ↦ evalBinaryOp? .le a b)) = _
    rw [show evalExpr? cfg frame evm collateralLifProduct = _ from hp]
    simp only [evalExpr?, pure, bind, EvalResult.bind, evalBinaryOp?, Int.ofNat_eq_natCast]
    norm_cast
  rw [collateralLifGuard, evalExpr?, evalCollateralLifEq hl]
  by_cases he : lltv = lifScale
  · simp only [he, decide_true, bind, EvalResult.bind, pure, true_or]
  · simp only [he, decide_false, bind, EvalResult.bind, hr, pure, false_or]

theorem collateralLifSource {cfg : Config} {frame : Frame} {evm : EVM.State}
    {lltv cursor : UInt256} (hcontract : frame.contract = contract)
    (hl : frame.locals.get? "lltv" = some (.int lltv.toNat))
    (hc : frame.locals.get? "liquidationCursor" = some (.int cursor.toNat))
    (hs : CollateralLifSafe lltv cursor) (rest : List Stmt) :
    ABlock cfg evm frame (collateralLifChecks ++ rest)
      (wordLocal frame "_maxLif" (maxLif lltv cursor)) rest := by
  have hargs : evalExprs? cfg frame evm [.var "lltv", .var "liquidationCursor"] =
      .ok [.int lltv.toNat, .int cursor.toNat] := by
    simp only [evalExprs?, evalWordLocal hl, evalWordLocal hc, bind, pure, EvalResult.bind]
  have hl' : (wordLocal frame "_maxLif" (maxLif lltv cursor)).locals.get? "lltv" =
      some (.int lltv.toNat) := by rw [wordLocal_get_ne _ _ _ _ (by decide)]; exact hl
  exact (sourceNormalStep ABlock.start (callMaxLif hcontract hargs hs.1))
    |>.requireStep ((evalCollateralLifCap (wordLocal_get _ _ _)).trans
      (by rw [decide_eq_true hs.2.1]))
    |>.requireStep ((evalCollateralLifGuard hl' (wordLocal_get _ _ _) hs.1 hs.2.1).trans
      (by rw [decide_eq_true hs.2.2]))

theorem collateralLifSourceRevert {cfg : Config} {frame : Frame} {evm : EVM.State}
    {lltv cursor : UInt256} (hcontract : frame.contract = contract)
    (hl : frame.locals.get? "lltv" = some (.int lltv.toNat))
    (hc : frame.locals.get? "liquidationCursor" = some (.int cursor.toNat))
    (hbad : ¬ CollateralLifSafe lltv cursor) (rest : List Stmt) :
    ExecBlock cfg frame evm (collateralLifChecks ++ rest) .reverted := by
  have hargs : evalExprs? cfg frame evm [.var "lltv", .var "liquidationCursor"] =
      .ok [.int lltv.toNat, .int cursor.toNat] := by
    simp only [evalExprs?, evalWordLocal hl, evalWordLocal hc, bind, pure, EvalResult.bind]
  have hl' : (wordLocal frame "_maxLif" (maxLif lltv cursor)).locals.get? "lltv" =
      some (.int lltv.toNat) := by rw [wordLocal_get_ne _ _ _ _ (by decide)]; exact hl
  by_cases hs : MaxLifSafe lltv cursor
  · apply ExecBlock.consNormal (callMaxLif hcontract hargs hs)
    by_cases hb : (maxLif lltv cursor).toNat ≤ 2000000000000000000
    · apply ExecBlock.consNormal (ExecStmt.requireTrue
        ((evalCollateralLifCap (wordLocal_get _ _ _)).trans (by rw [decide_eq_true hb])))
      apply ExecBlock.consRevert
      exact ExecStmt.requireFalse ((evalCollateralLifGuard hl' (wordLocal_get _ _ _) hs hb).trans
        (by rw [decide_eq_false (fun hp ↦ hbad ⟨hs, hb, hp⟩)]))
    · exact ExecBlock.consRevert (ExecStmt.requireFalse
        ((evalCollateralLifCap (wordLocal_get _ _ _)).trans (by rw [decide_eq_false hb])))
  · exact ExecBlock.consRevert (callMaxLifRevert hcontract hargs hs)

end Benchmarks.Midnight
