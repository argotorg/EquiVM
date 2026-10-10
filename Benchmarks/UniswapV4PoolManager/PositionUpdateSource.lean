import Benchmarks.UniswapV4PoolManager.PositionLiquiditySource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def positionChangeReverts (liquidity : UInt256) (delta : Int) : Prop :=
  if delta = 0 then liquidity = ⟨0⟩ else ¬liquidityAddFits liquidity delta
instance (liquidity : UInt256) (delta : Int) : Decidable (positionChangeReverts liquidity delta) :=
  inferInstanceAs (Decidable (if delta = 0 then liquidity = ⟨0⟩ else ¬liquidityAddFits liquidity delta))

theorem positionChangeResult_normal (f : Frame) (evm : EVM.State) (id key liquidity : UInt256) (delta : Int) :
    positionChangeResult f evm id key liquidity delta =
      if positionChangeReverts liquidity delta then .reverted else
        if delta ≠ 0 ∧ evm.executionEnv.perm = false then .staticViolation else
          .ok (positionChangeFrame f liquidity delta) (positionChangeState evm id key liquidity delta) := by
  by_cases hz : delta = 0
  · simp only [positionChangeResult, positionChangeReverts, positionChangeFrame, positionChangeState,
      ne_eq, hz, not_true_eq_false, false_and, if_false, if_true]
  · simp only [positionChangeResult, positionChangeReverts, ne_eq, hz, not_false_eq_true, true_and, if_false]
    by_cases hf : liquidityAddFits liquidity delta <;> simp only [hf, if_true, if_false, not_true_eq_false,
      not_false_eq_true]

def positionUpdateResult (f : Frame) (evm : EVM.State) (id key : UInt256) (delta : Int) (fee0 fee1 : UInt256) : ExecResult :=
  let liquidity := positionLiquidityWord evm id key
  if positionChangeReverts liquidity delta then .reverted else
    if delta ≠ 0 ∧ evm.executionEnv.perm = false then .staticViolation else
      positionFeesResult f (positionChangeState evm id key liquidity delta) id key liquidity fee0 fee1

def positionUpdatePreludeFrame (f : Frame) (evm : EVM.State) (id key : UInt256) : Frame :=
  wordLocal (wordLocal (wordLocal f "feesOwed0" ⟨0⟩) "feesOwed1" ⟨0⟩)
    "liquidity" (positionLiquidityWord evm id key)

theorem positionUpdatePrelude {f : Frame} {evm : EVM.State} {id key : UInt256}
    (hs : f.locals.get? "self" = some (positionRefValue id key)) :
    ExecBlock config f evm (positionUpdateFunction.body.take 3) (.ok (positionUpdatePreludeFrame f evm id key) evm) := by
  let f1 := wordLocal f "feesOwed0" ⟨0⟩
  let f2 := wordLocal f1 "feesOwed1" ⟨0⟩
  have h0 : ExecStmt config f evm positionUpdateFunction.body[0]! (.ok f1 evm) :=
    ExecStmt.letDecl (by simp only [evalExpr?, pure]; rfl)
  have h1 : ExecStmt config f1 evm positionUpdateFunction.body[1]! (.ok f2 evm) :=
    ExecStmt.letDecl (by simp only [evalExpr?, pure]; rfl)
  have hs2 : f2.locals.get? "self" = some (positionRefValue id key) := by
    simp only [f2, f1, wordLocal_get, beq_iff_eq, String.reduceEq, ↓reduceIte, hs]
  have h2 : ExecStmt config f2 evm positionUpdateFunction.body[2]!
      (.ok (positionUpdatePreludeFrame f evm id key) evm) := ExecStmt.letDecl (positionLiquidity_read hs2)
  exact ExecBlock.consNormal h0 (ExecBlock.consNormal h1 (execBlock_singleton h2))

theorem positionUpdateBody {f : Frame} {evm : EVM.State} {id key fee0 fee1 : UInt256} {delta : Int}
    (hf : f.contract = contract) (hs : f.locals.get? "self" = some (positionRefValue id key))
    (hd : f.locals.get? "liquidityDelta" = some (.int delta))
    (h0 : f.locals.get? "feeGrowthInside0X128" = some (.int (Int.ofNat fee0.toNat)))
    (h1 : f.locals.get? "feeGrowthInside1X128" = some (.int (Int.ofNat fee1.toNat))) :
    ∃ f', ExecFuncBody config f evm positionUpdateFunction.body (positionUpdateResult f' evm id key delta fee0 fee1) := by
  let f3 := positionUpdatePreludeFrame f evm id key
  have hpre := positionUpdatePrelude (evm := evm) hs
  have hs3 : f3.locals.get? "self" = some (positionRefValue id key) := by
    simp only [f3, positionUpdatePreludeFrame, wordLocal_get, beq_iff_eq, String.reduceEq, ↓reduceIte, hs]
  have hd3 : f3.locals.get? "liquidityDelta" = some (.int delta) := by
    simp only [f3, positionUpdatePreludeFrame, wordLocal_get, beq_iff_eq, String.reduceEq, ↓reduceIte, hd]
  have hl3 : f3.locals.get? "liquidity" = some (.int (Int.ofNat (positionLiquidityWord evm id key).toNat)) :=
    store_get_self _ _ _
  have hbranch := positionLiquidityBranch (f := f3) (evm := evm) hf hs3 hl3 hd3
  rw [positionChangeResult_normal] at hbranch
  by_cases hr : positionChangeReverts (positionLiquidityWord evm id key) delta
  · rw [if_pos hr] at hbranch
    exact ⟨f3, by simpa only [positionUpdateResult, if_pos hr] using (execFuncBody_prepend hpre
      (show ExecFuncBody config f3 evm (positionUpdateFunction.body.drop 3) .reverted from
        .execBlockRevert (ExecBlock.consRevert hbranch)))⟩
  · rw [if_neg hr] at hbranch
    by_cases hp : delta ≠ 0 ∧ evm.executionEnv.perm = false
    · rw [if_pos hp] at hbranch
      exact ⟨f3, by simpa only [positionUpdateResult, if_neg hr, if_pos hp] using (execFuncBody_prepend hpre
        (show ExecFuncBody config f3 evm (positionUpdateFunction.body.drop 3) .staticViolation from
          .execBlockStatic (ExecBlock.consStatic hbranch)))⟩
    · rw [if_neg hp] at hbranch
      let f4 := positionChangeFrame f3 (positionLiquidityWord evm id key) delta
      let post := positionChangeState evm id key (positionLiquidityWord evm id key) delta
      have h04 : f4.locals.get? "feeGrowthInside0X128" = some (.int (Int.ofNat fee0.toNat)) := by
        rw [positionChangeFrame_get _ _ _ _ (by decide)]
        simp only [f3, positionUpdatePreludeFrame, wordLocal_get, beq_iff_eq, String.reduceEq, ↓reduceIte, h0]
      have h14 : f4.locals.get? "feeGrowthInside1X128" = some (.int (Int.ofNat fee1.toNat)) := by
        rw [positionChangeFrame_get _ _ _ _ (by decide)]
        simp only [f3, positionUpdatePreludeFrame, wordLocal_get, beq_iff_eq, String.reduceEq, ↓reduceIte, h1]
      have ho04 : f4.locals.get? "feesOwed0" = some (.int 0) := by
        rw [positionChangeFrame_get _ _ _ _ (by decide)]
        simp only [f3, positionUpdatePreludeFrame, wordLocal_get, beq_iff_eq, String.reduceEq, ↓reduceIte]; rfl
      have ho14 : f4.locals.get? "feesOwed1" = some (.int 0) := by
        rw [positionChangeFrame_get _ _ _ _ (by decide)]
        simp only [f3, positionUpdatePreludeFrame, wordLocal_get, beq_iff_eq, String.reduceEq, ↓reduceIte]; rfl
      obtain ⟨f', hfees⟩ := positionFeesBody (f := f4) (evm := post)
        ((positionChangeFrame_contract _ _ _).trans hf)
        ((positionChangeFrame_get _ _ _ _ (by decide)).trans hs3)
        ((positionChangeFrame_get _ _ _ _ (by decide)).trans hl3) h04 h14 ho04 ho14
      exact ⟨f', by simpa only [positionUpdateResult, if_neg hr, if_neg hp] using
        execFuncBody_prepend hpre (execFuncBody_prepend (execBlock_singleton hbranch) hfees)⟩

theorem positionUpdateCall {f : Frame} {evm : EVM.State} {id key fee0 fee1 : UInt256} {delta : Int}
    {es ed e0 e1 : Expr} (hf : f.contract = contract)
    (hs : evalExpr? config f evm es = .ok (positionRefValue id key))
    (hd : evalExpr? config f evm ed = .ok (.int delta))
    (h0 : evalExpr? config f evm e0 = .ok (.int (Int.ofNat fee0.toNat)))
    (h1 : evalExpr? config f evm e1 = .ok (.int (Int.ofNat fee1.toNat))) (ret : Ident) :
    ExecStmt config f evm (.internalCall "Position_update" [es, ed, e0, e1] ret)
      (resumeCallResult f ret (positionUpdateResult f evm id key delta fee0 fee1)) := by
  let fc : Frame := {f with locals := (((((∅ : Store).insert "feeGrowthInside1X128" (.int (Int.ofNat fee1.toNat))).insert
    "feeGrowthInside0X128" (.int (Int.ofNat fee0.toNat))).insert "liquidityDelta" (.int delta)).insert
    "self" (positionRefValue id key))}
  obtain ⟨f', hbody⟩ := positionUpdateBody (f := fc) (evm := evm) hf (store_get_self _ _ _)
    ((store_get_ne _ _ (by decide : ("self" == "liquidityDelta") = false)).trans (store_get_self _ _ _))
    ((store_get_ne2 _ _ _ (by decide : ("liquidityDelta" == "feeGrowthInside0X128") = false)
      (by decide : ("self" == "feeGrowthInside0X128") = false)).trans (store_get_self _ _ _))
    ((store_get_ne3 _ _ _ _ (by decide : ("feeGrowthInside0X128" == "feeGrowthInside1X128") = false)
      (by decide : ("liquidityDelta" == "feeGrowthInside1X128") = false)
      (by decide : ("self" == "feeGrowthInside1X128") = false)).trans (store_get_self _ _ _))
  have hcall := internalCallFunctionExec (caller := f) (name := "Position_update") (retVar := ret)
    (args := [es, ed, e0, e1])
    (argVals := [positionRefValue id key, .int delta, .int (Int.ofNat fee0.toNat), .int (Int.ofNat fee1.toNat)])
    (by simp only [evalExprs?, hs, hd, h0, h1, bind, EvalResult.bind, pure])
    (by rw [hf]; exact positionUpdate_lookup) rfl hbody
  simpa only [positionUpdateResult, positionFeesResult, positionFeesStoreResult, resumeCallResult_ite,
    resumeCallResult_returned, resumeCallResult_reverted, resumeCallResult_static] using hcall

end Benchmarks.UniswapV4PoolManager
