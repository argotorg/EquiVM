import Benchmarks.CompoundIII.Comet.SupplyBaseAfterSource
import Benchmarks.CompoundIII.Comet.TransferInSource
import Benchmarks.CompoundIII.Comet.AccrueInternalSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

theorem supplyBaseAfterTransfer_source {v sender dst amount evm result} (requested : UInt256)
    (ht : SupplyBaseAfterTransfer v sender dst amount evm result) :
    internalBlockResult config (supplyBaseReceivedFrame v sender dst requested amount) evm
      (.internalCall "accrueInternal" [] "__c1" :: supplyBaseAfterAccrueBlock) result := by
  have ha := accrue_call v (supplyBaseReceivedFrame v sender dst requested amount) evm
    "__c1" rfl rfl
  cases ht with
  | reverted he =>
    have ha := internalStmtResult.cast ha he
    exact ExecBlock.consRevert ha
  | staticViolation he =>
    have ha := internalStmtResult.cast ha he
    exact ExecBlock.consStatic ha
  | done he tail =>
    have ha := internalStmtResult.cast ha he
    exact (supplyBaseAfterAccrue_source requested tail).prepend ha

theorem supplyBase_source {v sender dst amount evm result}
    (ht : SupplyBaseTrace v sender dst amount evm result) :
    internalSourceResult config (supplyBaseEntry (immStore v) sender dst amount)
      evm supplyBaseCallable.body result := by
  let frame := supplyBaseEntry (immStore v) sender dst amount
  have ha : evalExpr? config frame evm (.immutable "baseToken") = .ok (.address v.baseToken) := by
    simp only [evalExpr?, frame, supplyBaseEntry, immStore_get_baseToken, EvalResult.ofOption]
  have hs : evalExpr? config frame evm (.var "from") = .ok (.address sender) := by
    simp only [evalExpr?, frame, supplyBaseEntry, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]; rfl
  have ham : evalExpr? config frame evm (.var "amount") = .ok (.int amount.toNat) := by
    simp only [evalExpr?, frame, supplyBaseEntry, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]; rfl
  apply internalBlockResult.toSource
  change internalBlockResult config frame evm
    (.internalCall "doTransferIn" [.immutable "baseToken", .var "from", .var "amount"] "__c0" ::
      .assign .localVar ⟨"amount", []⟩ (.var "__c0") ::
      .internalCall "accrueInternal" [] "__c1" :: supplyBaseAfterAccrueBlock) result
  cases ht with
  | transferFailed ht =>
    exact ExecBlock.consRevert (transferIn_call ht frame _ _ _ "__c0" rfl ha hs ham)
  | @transferOk evm' received result ht tail =>
    let read := { frame with locals := frame.locals.insert "__c0" (.int received.toNat) }
    have hcall := transferIn_call ht frame _ _ _ "__c0" rfl ha hs ham
    have he : evalExpr? config read evm' (.var "__c0") = .ok (.int received.toNat) := by
      simp only [evalExpr?, read, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
        EvalResult.ofOption]; rfl
    have hassign : ExecStmt config read evm'
        (.assign .localVar ⟨"amount", []⟩ (.var "__c0"))
        (.ok (supplyBaseReceivedFrame v sender dst amount received) evm') :=
      ExecStmt.assign he (assignLocalFrame (by
        simp only [read, frame, supplyBaseEntry, Std.HashMap.get?_eq_getElem?,
          Std.HashMap.getElem?_insert]; rfl))
    exact ((supplyBaseAfterTransfer_source amount tail).prepend hassign).prepend hcall

theorem supplyBase_call {v sender dst amount evm result}
    (ht : SupplyBaseTrace v sender dst amount evm result) (frame : Frame)
    (fromExpr dstExpr amountExpr : Expr) (ret : Ident)
    (hc : frame.contract = contract) (hi : frame.immutables = immStore v)
    (hs : evalExpr? config frame evm fromExpr = .ok (.address sender))
    (hd : evalExpr? config frame evm dstExpr = .ok (.address dst))
    (ham : evalExpr? config frame evm amountExpr = .ok (.int amount.toNat)) :
    ExecStmt config frame evm (.internalCall "supplyBase" [fromExpr, dstExpr, amountExpr] ret)
      (internalStmtResult frame ret result) := by
  apply internalVoidCall (callee := supplyBaseCallable)
    (locals := (supplyBaseEntry (immStore v) sender dst amount).locals)
    (argVals := [.address sender, .address dst, .int amount.toNat])
  · simp only [evalExprs?, hs, hd, ham, pure, bind, EvalResult.bind]
  · rw [hc]; exact supplyBaseCallable_lookup
  · rfl
  · simpa only [hc, hi] using supplyBase_source ht

end Benchmarks.CompoundIII.Comet
