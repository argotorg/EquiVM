import Benchmarks.CompoundIII.Comet.SupplyInternalModel
import Benchmarks.CompoundIII.Comet.SupplyAssetSource
import Benchmarks.CompoundIII.Comet.ReentrancySource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

theorem supplyInternalAfter_source {v operator sender dst asset amount evm result}
    (ht : SupplyInternalAfter v operator sender dst asset amount evm result)
    (frame : Frame) (hf : SupplyAssetArgs frame v sender dst asset amount)
    (ho : frame.locals.get? "operator" = some (.address operator)) :
    internalBlockResult config frame evm supplyInternalTail result := by
  have ha := authorization_source frame evm ⟨0, by decide⟩ "from" operator sender (by decide)
    hf.contract ho hf.sender
  let ready := authorizationFrame frame evm ⟨0, by decide⟩ operator sender
  have hready : SupplyAssetArgs ready v sender dst asset amount := by
    constructor
    · exact hf.contract
    · exact hf.immutables
    · simpa only [ready, authorizationFrame, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
        using hf.sender
    · simpa only [ready, authorizationFrame, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
        using hf.dst
    · simpa only [ready, authorizationFrame, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
        using hf.asset
    · simpa only [ready, authorizationFrame, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
        using hf.amount
  cases ht with
  | unauthorized hn =>
    rw [if_neg hn] at ha
    exact execBlockAppendReverted ha
  | reverted hv ht =>
    rw [if_pos hv] at ha
    exact execBlock_append ha (ExecBlock.consRevert (supplyAsset_source ht ready hready))
  | staticViolation hv ht =>
    rw [if_pos hv] at ha
    exact execBlock_append ha (ExecBlock.consStatic (supplyAsset_source ht ready hready))
  | @done evm' hv ht hp =>
    rw [if_pos hv] at ha
    have hwork := supplyAsset_source ht ready hready
    let final := { supplyAssetReady ready v evm dst asset amount with
      locals := (supplyAssetReady ready v evm dst asset amount).locals.insert
        (supplyAssetReturn v asset) .unit }
    have hend := reentrancy_call final evm' false "__c7"
      ((supplyAssetReady_contract _ _ _ _ _ _).trans hf.contract)
    simp only [reentrancyOutcome, Bool.false_and, Bool.false_eq_true, if_false,
      reentrancyWriteOutcome, hp, if_true, internalStmtResult] at hend
    exact (show internalBlockResult config ready evm
      [supplyAssetStmt, .internalCall "nonReentrantAfter" [] "__c7"]
        (.ok (reentrancyState evm' false)) from
      ⟨_, ExecBlock.consNormal hwork (execBlock_singleton hend)⟩).prependBlock ha

theorem supplyInternal_source {v operator sender dst asset amount evm result}
    (ht : SupplyInternalTrace v operator sender dst asset amount evm result) :
    internalSourceResult config (supplyInternalEntry (immStore v) operator sender dst asset amount)
      evm supplyInternalCallable.body result := by
  let frame := supplyInternalEntry (immStore v) operator sender dst asset amount
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
    have hf : SupplyAssetArgs ready v sender dst asset amount := by
      constructor <;> simp only [ready, frame, supplyInternalEntry,
        Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] <;> rfl
    have ho : ready.locals.get? "operator" = some (.address operator) := by
      simp only [ready, frame, supplyInternalEntry, Std.HashMap.get?_eq_getElem?,
        Std.HashMap.getElem?_insert]; rfl
    exact (supplyInternalAfter_source ht ready hf ho).prepend (internalStmtResult.cast hb he)

theorem supplyInternal_call {v operator sender dst asset amount evm result}
    (ht : SupplyInternalTrace v operator sender dst asset amount evm result) (frame : Frame)
    (operatorExpr senderExpr toExpr assetExpr amountExpr : Expr) (ret : Ident)
    (hc : frame.contract = contract) (hi : frame.immutables = immStore v)
    (ho : evalExpr? config frame evm operatorExpr = .ok (.address operator))
    (hs : evalExpr? config frame evm senderExpr = .ok (.address sender))
    (hto : evalExpr? config frame evm toExpr = .ok (.address dst))
    (ha : evalExpr? config frame evm assetExpr = .ok (.address asset))
    (ham : evalExpr? config frame evm amountExpr = .ok (.int amount.toNat)) :
    ExecStmt config frame evm
      (.internalCall "supplyInternal" [operatorExpr, senderExpr, toExpr, assetExpr, amountExpr] ret)
      (internalStmtResult frame ret result) := by
  apply internalVoidCall (callee := supplyInternalCallable)
    (locals := (supplyInternalEntry (immStore v) operator sender dst asset amount).locals)
    (argVals := [.address operator, .address sender, .address dst, .address asset, .int amount.toNat])
  · simp only [evalExprs?, ho, hs, hto, ha, ham, pure, bind, EvalResult.bind]
  · rw [hc]; exact supplyInternalCallable_lookup
  · rfl
  · simpa only [hc, hi] using supplyInternal_source ht

end Benchmarks.CompoundIII.Comet
