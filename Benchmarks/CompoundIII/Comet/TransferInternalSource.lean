import Benchmarks.CompoundIII.Comet.TransferInternalModel
import Benchmarks.CompoundIII.Comet.TransferAssetSource
import Benchmarks.CompoundIII.Comet.AuthorizationSource
import Benchmarks.CompoundIII.Comet.ReentrancySource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

theorem transferInternalAfter_source {v operator src dst asset amount evm result}
    (ht : TransferInternalAfter v operator src dst asset amount evm result)
    (frame : Frame) (hf : TransferAssetArgs frame v src dst asset amount)
    (ho : frame.locals.get? "operator" = some (.address operator)) :
    internalBlockResult config frame evm transferInternalTail result := by
  have ha := authorization_source frame evm ⟨1, by decide⟩ "src" operator src (by decide)
    hf.contract ho hf.src
  let ready := authorizationFrame frame evm ⟨1, by decide⟩ operator src
  have hready : TransferAssetArgs ready v src dst asset amount := by
    constructor
    · exact hf.contract
    · exact hf.immutables
    · simpa only [ready, authorizationFrame, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
        using hf.src
    · simpa only [ready, authorizationFrame, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
        using hf.dst
    · simpa only [ready, authorizationFrame, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
        using hf.asset
    · simpa only [ready, authorizationFrame, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
        using hf.amount
  have hne : evalExpr? config ready evm (.binary .ne (.var "src") (.var "dst")) =
      .ok (.bool (decide (src ≠ dst))) := evalExpr_address_ne
    (by simp only [evalExpr?, hready.src, EvalResult.ofOption])
    (by simp only [evalExpr?, hready.dst, EvalResult.ofOption])
  cases ht with
  | unauthorized hn =>
    rw [if_neg hn] at ha
    exact execBlockAppendReverted ha
  | selfTransfer hv he =>
    rw [if_pos hv] at ha
    exact execBlock_append ha (ExecBlock.consRevert
      (ExecStmt.requireFalse (hne.trans (by rw [decide_eq_false (not_not.mpr he)]))))
  | reverted hv hn ht =>
    rw [if_pos hv] at ha
    exact execBlock_append ha (ExecBlock.consNormal
      (ExecStmt.requireTrue (hne.trans (by rw [decide_eq_true hn])))
      (ExecBlock.consRevert (transferAsset_source ht ready hready)))
  | staticViolation hv hn ht =>
    rw [if_pos hv] at ha
    exact execBlock_append ha (ExecBlock.consNormal
      (ExecStmt.requireTrue (hne.trans (by rw [decide_eq_true hn])))
      (ExecBlock.consStatic (transferAsset_source ht ready hready)))
  | @done evm' hv hn ht hp =>
    rw [if_pos hv] at ha
    have hwork := transferAsset_source ht ready hready
    let final := { transferAssetReady ready v evm src asset amount with
      locals := (transferAssetReady ready v evm src asset amount).locals.insert
        (transferAssetReturn v asset) .unit }
    have hend := reentrancy_call final evm' false "__c7"
      ((transferAssetReady_contract _ _ _ _ _ _).trans hf.contract)
    simp only [reentrancyOutcome, Bool.false_and, Bool.false_eq_true, if_false,
      reentrancyWriteOutcome, hp, if_true, internalStmtResult] at hend
    exact (show internalBlockResult config ready evm
      [.require (.binary .ne (.var "src") (.var "dst")), transferAssetStmt,
        .internalCall "nonReentrantAfter" [] "__c7"]
        (.ok (reentrancyState evm' false)) from
      ⟨_, ExecBlock.consNormal (ExecStmt.requireTrue (hne.trans (by rw [decide_eq_true hn])))
        (ExecBlock.consNormal hwork (execBlock_singleton hend))⟩).prependBlock ha

theorem transferInternal_source {v operator src dst asset amount evm result}
    (ht : TransferInternalTrace v operator src dst asset amount evm result) :
    internalSourceResult config (transferInternalEntry (immStore v) operator src dst asset amount)
      evm transferInternalCallable.body result := by
  let frame := transferInternalEntry (immStore v) operator src dst asset amount
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
    have hf : TransferAssetArgs ready v src dst asset amount := by
      constructor <;> simp only [ready, frame, transferInternalEntry,
        Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] <;> rfl
    have ho : ready.locals.get? "operator" = some (.address operator) := by
      simp only [ready, frame, transferInternalEntry, Std.HashMap.get?_eq_getElem?,
        Std.HashMap.getElem?_insert]; rfl
    exact (transferInternalAfter_source ht ready hf ho).prepend (internalStmtResult.cast hb he)

theorem transferInternal_call {v operator src dst asset amount evm result}
    (ht : TransferInternalTrace v operator src dst asset amount evm result) (frame : Frame)
    (operatorExpr srcExpr toExpr assetExpr amountExpr : Expr) (ret : Ident)
    (hc : frame.contract = contract) (hi : frame.immutables = immStore v)
    (ho : evalExpr? config frame evm operatorExpr = .ok (.address operator))
    (hs : evalExpr? config frame evm srcExpr = .ok (.address src))
    (hto : evalExpr? config frame evm toExpr = .ok (.address dst))
    (ha : evalExpr? config frame evm assetExpr = .ok (.address asset))
    (ham : evalExpr? config frame evm amountExpr = .ok (.int amount.toNat)) :
    ExecStmt config frame evm
      (.internalCall "transferInternal" [operatorExpr, srcExpr, toExpr, assetExpr, amountExpr] ret)
      (internalStmtResult frame ret result) := by
  apply internalVoidCall (callee := transferInternalCallable)
    (locals := (transferInternalEntry (immStore v) operator src dst asset amount).locals)
    (argVals := [.address operator, .address src, .address dst, .address asset, .int amount.toNat])
  · simp only [evalExprs?, ho, hs, hto, ha, ham, pure, bind, EvalResult.bind]
  · rw [hc]; exact transferInternalCallable_lookup
  · rfl
  · simpa only [hc, hi] using transferInternal_source ht

end Benchmarks.CompoundIII.Comet
