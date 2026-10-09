import Benchmarks.CompoundIII.Comet.WithdrawReservesModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

theorem withdrawReservesValue_eval (v : CometWithExtendedAssetListImmutables)
    (initial evm : EVM.State) (recipient : AccountAddress) (amount reserves : UInt256) :
    evalExpr? config (withdrawReservesFrame v initial recipient amount reserves) evm
      (.var "reserves") = .ok (.int (signedWord reserves)) := by
  simp only [evalExpr?, withdrawReservesFrame, Std.HashMap.get?_eq_getElem?,
    Std.HashMap.getElem?_insert, EvalResult.ofOption]
  rfl

theorem withdrawReservesSign_eval (v : CometWithExtendedAssetListImmutables)
    (initial evm : EVM.State) (recipient : AccountAddress) (amount reserves : UInt256) :
    evalExpr? config (withdrawReservesFrame v initial recipient amount reserves) evm
      (.binary .ge (.var "reserves") (.intLit 0)) =
      .ok (.bool (decide (0 ≤ signedWord reserves))) := by
  simp only [evalExpr?, withdrawReservesValue_eval, pure, bind, EvalResult.bind, evalBinaryOp?]

theorem withdrawReservesAmount_eval (v : CometWithExtendedAssetListImmutables)
    (initial evm : EVM.State) (recipient : AccountAddress) (amount reserves : UInt256) :
    evalExpr? config (withdrawReservesUnsignedFrame v initial recipient amount reserves) evm
      (.binary .le (.var "amount") (.var "__c1")) =
      .ok (.bool (decide (amount.toNat ≤ reserves.toNat))) := by
  simp only [evalExpr?, withdrawReservesUnsignedFrame, withdrawReservesFrame,
    withdrawReservesEntry, withdrawReservesArgs, calldataLocalFrame,
    Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, EvalResult.ofOption]
  change EvalResult.ok (Value.bool (decide ((amount.toNat : Int) ≤ reserves.toNat))) = _
  simp

theorem withdrawReservesReady (v : CometWithExtendedAssetListImmutables)
    (initial evm : EVM.State) (recipient : AccountAddress) (amount reserves : UInt256)
    (hv : WithdrawReservesAllowed reserves amount) :
    ABlock config evm (withdrawReservesFrame v initial recipient amount reserves)
      withdrawReservesTail (withdrawReservesUnsignedFrame v initial recipient amount reserves)
      [.internalCall "doTransferOut" [.immutable "baseToken", .var "to", .var "amount"] "__c2",
        withdrawReservesEmit] := by
  refine ⟨fun h ↦ ?_⟩
  apply ExecBlock.consNormal (ExecStmt.requireTrue ?_)
  · apply ExecBlock.consNormal (unsigned256_call_ok _ evm reserves (.var "reserves") "__c1" rfl ?_)
    · refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) h
      exact (withdrawReservesAmount_eval v initial evm recipient amount reserves).trans
        (by rw [decide_eq_true hv.2])
    · rw [withdrawReservesValue_eval, signedWord_low hv.1]
  · rw [withdrawReservesSign_eval, decide_eq_true ((signedWord_nonneg_iff reserves).2 hv.1)]

theorem withdrawReservesChecks_revert (v : CometWithExtendedAssetListImmutables)
    (initial evm : EVM.State) (recipient : AccountAddress) (amount reserves : UInt256)
    (hv : ¬ WithdrawReservesAllowed reserves amount) :
    ExecBlock config (withdrawReservesFrame v initial recipient amount reserves) evm
      withdrawReservesTail .reverted := by
  by_cases hn : reserves.toNat < 2^255
  · have ha : ¬ amount.toNat ≤ reserves.toNat := fun ha ↦ hv ⟨hn, ha⟩
    apply ExecBlock.consNormal (ExecStmt.requireTrue ?_)
    · apply ExecBlock.consNormal
        (unsigned256_call_ok _ evm reserves (.var "reserves") "__c1" rfl ?_)
      · apply ExecBlock.consRevert (ExecStmt.requireFalse ?_)
        exact (withdrawReservesAmount_eval v initial evm recipient amount reserves).trans
          (by rw [decide_eq_false ha])
      · rw [withdrawReservesValue_eval, signedWord_low hn]
    · rw [withdrawReservesSign_eval, decide_eq_true ((signedWord_nonneg_iff reserves).2 hn)]
  · apply ExecBlock.consRevert (ExecStmt.requireFalse ?_)
    rw [withdrawReservesSign_eval, decide_eq_false (fun hh ↦ hn ((signedWord_nonneg_iff _).1 hh))]

theorem withdrawReservesAfter_source {v : CometWithExtendedAssetListImmutables}
    {evm : EVM.State} {recipient : AccountAddress} {amount reserves : UInt256}
    {result : Option EVM.State} (ht : WithdrawReservesAfter v recipient amount reserves evm result)
    (initial : EVM.State) :
    WithdrawReservesBlockResult (withdrawReservesFrame v initial recipient amount reserves)
      evm withdrawReservesTail result := by
  cases ht with
  | checksFailed hv =>
    exact withdrawReservesChecks_revert v initial evm recipient amount reserves hv
  | @transfer result hv ht =>
    have hc := transferOut_call ht
      (withdrawReservesUnsignedFrame v initial recipient amount reserves)
      (.immutable "baseToken") (.var "to") (.var "amount") "__c2" rfl
      (evalImmutable_baseToken config contract _ evm v) (by
        simp only [evalExpr?, withdrawReservesUnsignedFrame, withdrawReservesFrame,
          withdrawReservesEntry, withdrawReservesArgs, calldataLocalFrame,
          Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, EvalResult.ofOption]
        rfl) (by
        simp only [evalExpr?, withdrawReservesUnsignedFrame, withdrawReservesFrame,
          withdrawReservesEntry, withdrawReservesArgs, calldataLocalFrame,
          Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, EvalResult.ofOption]
        rfl)
    cases result with
    | none =>
      apply (withdrawReservesReady v initial evm recipient amount reserves hv).run
      exact ExecBlock.consRevert hc
    | some evm' =>
      let final := { withdrawReservesUnsignedFrame v initial recipient amount reserves with
        locals := (withdrawReservesUnsignedFrame v initial recipient amount reserves).locals.insert
          "__c2" .unit }
      have hemit : evalExprs? config final evm' [.var "to", .var "amount"] =
          .ok [.address recipient, .int (Int.ofNat amount.toNat)] := by
        simp only [evalExprs?, evalExpr?, final, withdrawReservesUnsignedFrame,
          withdrawReservesFrame,
          withdrawReservesEntry, withdrawReservesArgs, calldataLocalFrame,
          Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, EvalResult.ofOption,
          pure, bind, EvalResult.bind]
        rfl
      simp only [WithdrawReservesBlockResult]
      by_cases hp : evm'.executionEnv.perm = true
      · rw [if_pos hp]
        refine ⟨final, (withdrawReservesReady v initial evm recipient amount reserves hv).run ?_⟩
        exact ExecBlock.consNormal hc (ExecBlock.consNormal (ExecStmt.emit hemit) ExecBlock.nil)
      · rw [if_neg hp]
        apply (withdrawReservesReady v initial evm recipient amount reserves hv).run
        exact ExecBlock.consNormal hc
          (ExecBlock.consStatic (ExecStmt.emitStatic hemit (Bool.eq_false_iff.mpr hp)))

end Benchmarks.CompoundIII.Comet
