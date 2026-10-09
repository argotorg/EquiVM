import Benchmarks.CompoundIII.Comet.ApproveThisModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem approveThisAuth_eval (v : CometWithExtendedAssetListImmutables)
    (evm : EVM.State) (locals : Store) :
    evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
      approveThisAuth = .ok (.bool (decide (evm.executionEnv.source = v.governor))) := by
  simp only [approveThisAuth, evalExpr?, evalImmutable_governor, envValue, pure, bind,
    EvalResult.bind, evalBinaryOp?]
  congr 2
  apply Bool.eq_iff_iff.mpr
  simp

theorem approveThis_source {v : CometWithExtendedAssetListImmutables}
    {evm : EVM.State} {manager asset : AccountAddress} {amount : UInt256}
    {result : Option EVM.State} (ht : ApproveThisTrace v manager asset amount evm result)
    (hv : evm.executionEnv.weiValue = ⟨0⟩) (hhi : evm.executionEnv.calldata.size < 2^255 + 4) :
    ApproveThisSourceResult v manager asset amount evm result := by
  let frame := approveThisEntry v evm manager asset amount
  have hauth := approveThisAuth_eval v evm frame.locals
  have ha : evalExpr? config frame evm (.var "asset") = .ok (.address asset) := by
    simp only [evalExpr?, frame, approveThisEntry, approveThisArgs, calldataLocalFrame,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, EvalResult.ofOption]
    rfl
  have hm : evalExpr? config frame evm (.var "manager") = .ok (.address manager) := by
    simp only [evalExpr?, frame, approveThisEntry, approveThisArgs, calldataLocalFrame,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, EvalResult.ofOption]
    rfl
  have hn : evalExpr? config frame evm (.var "amount") = .ok (.int amount.toNat) := by
    simp only [evalExpr?, frame, approveThisEntry, approveThisArgs, calldataLocalFrame,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, EvalResult.ofOption]
    rfl
  have haddr : AccountAddress.ofUInt256 (EVM.word asset.val) = asset :=
    accountAddress_roundtrip asset
  have hx := extCodeSource (target := EVM.word asset.val) (σ := evm.accountMap) rfl
    (by rw [haddr]; exact ha)
  cases ht with
  | unauthorized hbad =>
      rw [decide_eq_false hbad] at hauth
      unfold ApproveThisSourceResult
      rw [approveThisTransition_body]
      exact ExecFuncBody.execBlockRevert ((calldataPrologue_ok hv hhi).run
        (ExecBlock.consRevert (ExecStmt.requireFalse hauth)))
  | codeMissing hgov hcode =>
      rw [decide_eq_true hgov] at hauth
      unfold ApproveThisSourceResult
      rw [approveThisTransition_body]
      apply ExecFuncBody.execBlockRevert
      apply (calldataPrologue_ok hv hhi).run
      apply ExecBlock.consNormal (ExecStmt.requireTrue hauth)
      apply ExecBlock.consRevert (ExecStmt.requireFalse ?_)
      change evalExpr? config frame evm approveThisCode = .ok (.bool false)
      rw [approveThisCode, evalExpr?, hx, hcode] <;> try (intro h; cases h)
      simp [evalExpr?, evalBinaryOp?, bind, EvalResult.bind, pure]
  | @callResult evm' z out hgov hcode hcall =>
      rw [decide_eq_true hgov] at hauth
      have hguard : evalExpr? config frame evm approveThisCode = .ok (.bool true) := by
        rw [approveThisCode, evalExpr?, hx] <;> try (intro h; cases h)
        simp only [bind, EvalResult.bind, evalExpr?, evalBinaryOp?, pure, EvalResult.ok.injEq,
          Value.bool.injEq, decide_eq_true_eq]
        have hnz := intOfNat_toNat_ne_zero_of_u256_ne_zero _ hcode
        simp only [Int.ofNat_eq_natCast] at hnz ⊢
        omega
      have hc := approveCall_source (ret := "__c0") ha hm hn hcall
      cases z with
      | false =>
          unfold ApproveThisSourceResult
          rw [approveThisTransition_body]
          exact ExecFuncBody.execBlockRevert ((calldataPrologue_ok hv hhi).run
            (ExecBlock.consNormal (ExecStmt.requireTrue hauth)
              (ExecBlock.consNormal (ExecStmt.requireTrue hguard) (ExecBlock.consRevert hc))))
      | true =>
          refine ⟨{ frame with locals := frame.locals.insert "__c0" .unit }, ?_⟩
          rw [approveThisTransition_body]
          exact ExecFuncBody.execBlockOK ((calldataPrologue_ok hv hhi).run
            (ExecBlock.consNormal (ExecStmt.requireTrue hauth)
              (ExecBlock.consNormal (ExecStmt.requireTrue hguard)
                (ExecBlock.consNormal hc ExecBlock.nil))))

end Benchmarks.CompoundIII.Comet
