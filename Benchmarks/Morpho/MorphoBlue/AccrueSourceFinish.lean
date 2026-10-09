import Benchmarks.Morpho.MorphoBlue.AccrueSourceFeeWrites

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

-- LIBRARY CANDIDATE: the nonzero test for a canonical word represented as a Solm integer.
theorem evalWordNeZero {cfg : Config} {frame : Frame} {evm : EVM.State} {e : Expr} {w : UInt256}
    (he : evalExpr? cfg frame evm e = .ok (.int (Int.ofNat w.toNat))) :
    evalExpr? cfg frame evm (.binary .ne e (.intLit 0)) = .ok (.bool (decide (w ≠ ⟨0⟩))) := by
  have h := evalWordEqZero he
  simp only [evalExpr?, he, pure, bind, EvalResult.bind, evalBinaryOp?] at h ⊢
  have hb := Value.bool.inj (EvalResult.ok.inj h)
  rw [hb, decide_not]

theorem morphoAccrueFeeCondition (p : MarketParamsWords) (locals imms : Store) (evm : EVM.State)
    (hl : MarketLocals p locals) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.binary .ne (.storage ⟨"market", [.mindex (.var "id"), .field "fee"]⟩) (.intLit 0)) =
      .ok (.bool (decide (marketFieldWord evm.accountMap evm.executionEnv p.id 5 ≠ ⟨0⟩))) :=
  evalWordNeZero (hl.evalField imms evm ⟨5, by decide⟩)

theorem morphoAccrueEmit (p : MarketParamsWords) (locals imms : Store) (evm : EVM.State)
    (rate interest shares : UInt256) (hl : MarketLocals p locals)
    (hr : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.var "borrowRate") = .ok (.int (Int.ofNat rate.toNat)))
    (hi : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.var "interest") = .ok (.int (Int.ofNat interest.toNat)))
    (hs : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.var "feeShares") = .ok (.int (Int.ofNat shares.toNat))) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm accrueIrmBody[11]!
      (.ok { contract := contract, locals := locals, immutables := imms } evm) := by
  apply ExecStmt.emit
  simp only [evalExprs?, hl.evalId imms evm, hr, hi, hs, pure, bind, EvalResult.bind]
  rfl

theorem morphoAccrueSourceFromIrmOk (p : MarketParamsWords) (hc : p.Canonical) (imms : Store)
    (evm evm' : EVM.State) (locals : Store)
    (htime : (marketFieldWord evm.accountMap evm.executionEnv p.id 4).toNat ≤
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hn : accrueElapsed evm.accountMap evm.executionEnv p ≠ ⟨0⟩) (hi : p.irm ≠ ⟨0⟩)
    (hbody : ExecBlock config (accrueAfterElapsed p imms (accrueElapsed evm.accountMap evm.executionEnv p)) evm
      accrueIrmBody (.ok { contract := contract, locals := locals, immutables := imms } evm'))
    (hl : MarketLocals p locals) :
    ExecFuncBody config (accrueStart p imms) evm accrueInterestFunction.body
      (.returned { contract := contract, locals := locals, immutables := imms }
        (storeMarketLastUpdate evm' p.id (halfWord false (UInt256.ofNat evm'.executionEnv.header.timestamp))) none) := by
  apply ExecFuncBody.execBlockOK
  apply (morphoAccrueSourceNonzeroElapsed p evm imms htime hn).run
  apply ExecBlock.consNormal (ExecStmt.iteTrue ?_ hbody)
  · exact ExecBlock.consNormal (morphoAccrueTimestampAssign p locals imms evm' hl) ExecBlock.nil
  · simpa only [decide_eq_true hi] using
      (accrueElapsed_locals p imms _).evalIrmNonzero hc imms evm

theorem morphoAccrueSourceFromIrmRevert (p : MarketParamsWords) (hc : p.Canonical) (imms : Store)
    (evm : EVM.State)
    (htime : (marketFieldWord evm.accountMap evm.executionEnv p.id 4).toNat ≤
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hn : accrueElapsed evm.accountMap evm.executionEnv p ≠ ⟨0⟩) (hi : p.irm ≠ ⟨0⟩)
    (hbody : ExecBlock config (accrueAfterElapsed p imms (accrueElapsed evm.accountMap evm.executionEnv p)) evm
      accrueIrmBody .reverted) :
    ExecFuncBody config (accrueStart p imms) evm accrueInterestFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply (morphoAccrueSourceNonzeroElapsed p evm imms htime hn).run
  apply ExecBlock.consRevert (ExecStmt.iteTrue ?_ hbody)
  simpa only [decide_eq_true hi] using
    (accrueElapsed_locals p imms _).evalIrmNonzero hc imms evm

theorem morphoAccrueSourceFromIrmStatic (p : MarketParamsWords) (hc : p.Canonical) (imms : Store)
    (evm : EVM.State)
    (htime : (marketFieldWord evm.accountMap evm.executionEnv p.id 4).toNat ≤
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hn : accrueElapsed evm.accountMap evm.executionEnv p ≠ ⟨0⟩) (hi : p.irm ≠ ⟨0⟩)
    (hbody : ExecBlock config (accrueAfterElapsed p imms (accrueElapsed evm.accountMap evm.executionEnv p)) evm
      accrueIrmBody .staticViolation) :
    ExecFuncBody config (accrueStart p imms) evm accrueInterestFunction.body .staticViolation := by
  apply ExecFuncBody.execBlockStatic
  apply (morphoAccrueSourceNonzeroElapsed p evm imms htime hn).run
  apply ExecBlock.consStatic (ExecStmt.iteTrue ?_ hbody)
  simpa only [decide_eq_true hi] using
    (accrueElapsed_locals p imms _).evalIrmNonzero hc imms evm

end Benchmarks.Morpho.MorphoBlue
