import Benchmarks.Midnight.MarketFeeCreditSource
import Benchmarks.Midnight.ToUint128Source
import Benchmarks.Midnight.PositionUpdateSourceFrames

/-! Source fee-credit accumulation, event emission, and returned position values. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

attribute [local simp] wordLocal_get wordLocal_get_ne

theorem positionUpdateFeeSource {frame : Frame} {evm : EVM.State}
    {id user credit pending fee creditDecrease pendingDecrease : UInt256}
    (hc : frame.contract = contract) (hbase : frame.locals.get? "marketState" = none)
    (hid : frame.locals.get? "id" = some (wordBytes32Value id))
    (huser : frame.locals.get? "user" = some (.address (AccountAddress.ofNat user.toNat)))
    (hcredit : frame.locals.get? "newCredit" = some (.int credit.toNat))
    (hpending : frame.locals.get? "newPendingFee" = some (.int pending.toNat))
    (hfee : frame.locals.get? "accruedFee" = some (.int fee.toNat))
    (hcd : frame.locals.get? "creditDecrease" = some (.int creditDecrease.toNat))
    (hpd : frame.locals.get? "pendingFeeDecrease" = some (.int pendingDecrease.toNat))
    (hfee128 : fee.toNat < 2^128) (hsum : (marketFeeCreditWord evm id).toNat + fee.toNat < 2^128)
    (hperm : evm.executionEnv.perm = true) :
    ExecBlock config frame evm (positionUpdateFunction.body.drop 11)
      (.returned (wordLocal frame "__c1" fee) (positionUpdateFeeState evm id fee)
        (some [.int credit.toNat, .int pending.toNat, .int fee.toNat])) := by
  have he : evalExprs? config frame evm [.var "accruedFee"] = .ok [.int fee.toNat] := by
    simp only [evalExprs?, evalWordLocal hfee, EvalResult.bind, bind, pure]
  refine ExecBlock.consNormal (callToUint128 hc he hfee128) ?_
  let frame' := wordLocal frame "__c1" fee
  have hc' : frame'.contract = contract := hc
  have hb' : frame'.locals.get? "marketState" = none := by
    simp [frame', -Std.HashMap.get?_eq_getElem?, hbase]
  have hi' : frame'.locals.get? "id" = some (wordBytes32Value id) := by
    simp [frame', -Std.HashMap.get?_eq_getElem?, hid]
  have hfee' : frame'.locals.get? "__c1" = some (.int fee.toNat) := wordLocal_get _ _ _
  refine ExecBlock.consNormal (ExecStmt.assign (Or.inr hperm)
    (evalCheckedAdd128 (evalMarketFeeCredit (evm := evm) hc' hb' hi') (evalWordLocal hfee') hsum)
    (assignMarketFeeCredit hc' hb' hi')) ?_
  refine ExecBlock.consNormal (ExecStmt.emit (vals := [wordBytes32Value id,
    .address (AccountAddress.ofNat user.toNat), .int creditDecrease.toNat,
    .int pendingDecrease.toNat, .int fee.toNat]) ?_ ?_) ?_
  · simpa only [positionUpdateFeeState, storeHigh128_env] using hperm
  · change evalExprs? config frame' _ _ = _
    simp [-Std.HashMap.get?_eq_getElem?, evalExprs?, evalExpr?, frame',
      hid, huser, hcd, hpd, hfee, EvalResult.ofOption, EvalResult.bind, bind, pure]
  · apply ExecBlock.consReturn
    apply ExecStmt.return
    change evalExprs? config frame' _ _ = _
    simp [-Std.HashMap.get?_eq_getElem?, evalExprs?, evalExpr?, frame',
      hcredit, hpending, hfee, EvalResult.ofOption, EvalResult.bind, bind, pure]

theorem positionUpdateFeeSourceRevert {frame : Frame} {evm : EVM.State} {id fee : UInt256}
    (hc : frame.contract = contract) (hbase : frame.locals.get? "marketState" = none)
    (hid : frame.locals.get? "id" = some (wordBytes32Value id))
    (hfee : frame.locals.get? "accruedFee" = some (.int fee.toNat))
    (hfee128 : fee.toNat < 2^128) (hsum : 2^128 ≤ (marketFeeCreditWord evm id).toNat + fee.toNat) :
    ExecBlock config frame evm (positionUpdateFunction.body.drop 11) .reverted := by
  have he : evalExprs? config frame evm [.var "accruedFee"] = .ok [.int fee.toNat] := by
    simp only [evalExprs?, evalWordLocal hfee, EvalResult.bind, bind, pure]
  refine ExecBlock.consNormal (callToUint128 hc he hfee128) ?_
  let frame' := wordLocal frame "__c1" fee
  have hc' : frame'.contract = contract := hc
  have hb' : frame'.locals.get? "marketState" = none := by
    simp [frame', -Std.HashMap.get?_eq_getElem?, hbase]
  have hi' : frame'.locals.get? "id" = some (wordBytes32Value id) := by
    simp [frame', -Std.HashMap.get?_eq_getElem?, hid]
  have hfee' : frame'.locals.get? "__c1" = some (.int fee.toNat) := wordLocal_get _ _ _
  apply ExecBlock.consRevert (ExecStmt.assignExprRevert _)
  exact evalCheckedAdd128Overflow (evalMarketFeeCredit (evm := evm) hc' hb' hi') (evalWordLocal hfee') hsum

end Benchmarks.Midnight
