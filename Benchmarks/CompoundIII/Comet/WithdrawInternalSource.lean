import Benchmarks.CompoundIII.Comet.WithdrawInternalModel
import Benchmarks.CompoundIII.Comet.WithdrawAssetSource
import Benchmarks.CompoundIII.Comet.WithdrawAuthSource
import Benchmarks.CompoundIII.Comet.ReentrancySource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

theorem withdrawInternalAfter_source {v operator src recipient asset amount evm result}
    (ht : WithdrawInternalAfter v operator src recipient asset amount evm result)
    (frame : Frame) (hf : WithdrawAssetArgs frame v src recipient asset amount)
    (ho : frame.locals.get? "operator" = some (.address operator)) :
    internalBlockResult config frame evm withdrawInternalTail result := by
  have ha := withdrawAuth_source frame evm operator src hf.contract ho hf.src
  let ready := withdrawAuthFrame frame evm operator src
  have hready : WithdrawAssetArgs ready v src recipient asset amount := by
    constructor
    · exact hf.contract
    · exact hf.immutables
    · simpa only [ready, withdrawAuthFrame, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
        using hf.src
    · simpa only [ready, withdrawAuthFrame, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
        using hf.recipient
    · simpa only [ready, withdrawAuthFrame, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
        using hf.asset
    · simpa only [ready, withdrawAuthFrame, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
        using hf.amount
  cases ht with
  | unauthorized hn =>
    rw [if_neg hn] at ha
    exact execBlockAppendReverted ha
  | reverted hv ht =>
    rw [if_pos hv] at ha
    exact execBlock_append ha (ExecBlock.consRevert (withdrawAsset_source ht ready hready))
  | staticViolation hv ht =>
    rw [if_pos hv] at ha
    exact execBlock_append ha (ExecBlock.consStatic (withdrawAsset_source ht ready hready))
  | @done evm' hv ht hp =>
    rw [if_pos hv] at ha
    have hwork := withdrawAsset_source ht ready hready
    let final := { withdrawAssetReady ready v evm src asset amount with
      locals := (withdrawAssetReady ready v evm src asset amount).locals.insert
        (withdrawAssetReturn v asset) .unit }
    have hend := reentrancy_call final evm' false "__c7"
      ((withdrawAssetReady_contract _ _ _ _ _ _).trans hf.contract)
    simp only [reentrancyOutcome, Bool.false_and, Bool.false_eq_true, if_false,
      reentrancyWriteOutcome, hp, if_true, internalStmtResult] at hend
    exact (show internalBlockResult config ready evm
      [withdrawAssetStmt, .internalCall "nonReentrantAfter" [] "__c7"]
        (.ok (reentrancyState evm' false)) from
      ⟨_, ExecBlock.consNormal hwork (execBlock_singleton hend)⟩).prependBlock ha

theorem withdrawInternal_source {v operator src recipient asset amount evm result}
    (ht : WithdrawInternalTrace v operator src recipient asset amount evm result) :
    internalSourceResult config (withdrawInternalEntry (immStore v) operator src recipient asset amount)
      evm withdrawInternalCallable.body result := by
  let frame := withdrawInternalEntry (immStore v) operator src recipient asset amount
  let ready := { frame with locals := frame.locals.insert "__c0" .unit }
  have hb := reentrancy_call frame evm true "__c0" rfl
  apply internalBlockResult.toSource
  cases ht with
  | reverted he =>
    have hb := internalStmtResult.cast hb he
    exact ExecBlock.consRevert hb
  | staticViolation he =>
    have hb := internalStmtResult.cast hb he
    exact ExecBlock.consStatic hb
  | done he ht =>
    have hf : WithdrawAssetArgs ready v src recipient asset amount := by
      constructor <;> simp only [ready, frame, withdrawInternalEntry,
        Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] <;> rfl
    have ho : ready.locals.get? "operator" = some (.address operator) := by
      simp only [ready, frame, withdrawInternalEntry, Std.HashMap.get?_eq_getElem?,
        Std.HashMap.getElem?_insert]; rfl
    exact (withdrawInternalAfter_source ht ready hf ho).prepend (internalStmtResult.cast hb he)

theorem withdrawInternal_call {v operator src recipient asset amount evm result}
    (ht : WithdrawInternalTrace v operator src recipient asset amount evm result) (frame : Frame)
    (operatorExpr srcExpr toExpr assetExpr amountExpr : Expr) (ret : Ident)
    (hc : frame.contract = contract) (hi : frame.immutables = immStore v)
    (ho : evalExpr? config frame evm operatorExpr = .ok (.address operator))
    (hs : evalExpr? config frame evm srcExpr = .ok (.address src))
    (hto : evalExpr? config frame evm toExpr = .ok (.address recipient))
    (ha : evalExpr? config frame evm assetExpr = .ok (.address asset))
    (ham : evalExpr? config frame evm amountExpr = .ok (.int amount.toNat)) :
    ExecStmt config frame evm
      (.internalCall "withdrawInternal" [operatorExpr, srcExpr, toExpr, assetExpr, amountExpr] ret)
      (internalStmtResult frame ret result) := by
  apply internalVoidCall (callee := withdrawInternalCallable)
    (locals := (withdrawInternalEntry (immStore v) operator src recipient asset amount).locals)
    (argVals := [.address operator, .address src, .address recipient, .address asset, .int amount.toNat])
  · simp only [evalExprs?, ho, hs, hto, ha, ham, pure, bind, EvalResult.bind]
  · rw [hc]; exact withdrawInternalCallable_lookup
  · rfl
  · simpa only [hc, hi] using withdrawInternal_source ht

end Benchmarks.CompoundIII.Comet
