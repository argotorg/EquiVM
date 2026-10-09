import Benchmarks.CompoundIII.Comet.BuyCollateralTailSource
import Benchmarks.CompoundIII.Comet.QuoteSource
import Benchmarks.CompoundIII.Comet.TransferInSource
import Benchmarks.CompoundIII.Comet.InternalBlockComposition

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

theorem buyCollateralAfterIn_source {v asset recipient minimum received evm result}
    (ht : BuyCollateralAfterIn v asset recipient minimum received evm result)
    (frame : Frame) (hf : BuyCollateralArgs frame v asset recipient minimum received) :
    internalBlockResult config frame evm buyCollateralAfterInBody result := by
  cases ht with
  | failed ht =>
    exact ExecBlock.consRevert (quote_call ht frame (.var "asset") (.var "baseAmount")
      "collateralAmount" hf.contract hf.immutables (hf.evalAsset evm) (hf.evalBase evm))
  | quote ht hn =>
    have hc := quote_call ht frame (.var "asset") (.var "baseAmount") "collateralAmount"
      hf.contract hf.immutables (hf.evalAsset evm) (hf.evalBase evm)
    exact (buyCollateralAfterQuote_source hn _
      (hf.insert "collateralAmount" _ (by decide)) (by
        simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]; rfl)).prepend hc

theorem buyCollateralAfterReserves_source {v asset recipient minimum base reserves evm result}
    (ht : BuyCollateralAfterReserves v asset recipient minimum base reserves evm result)
    (frame : Frame) (hf : BuyCollateralArgs frame v asset recipient minimum base)
    (hr : frame.locals.get? "reserves" = some (.int (signedWord reserves))) :
    internalBlockResult config frame evm buyCollateralAfterReservesBody result := by
  have hg := buyCollateralForSale_eval hf.immutables hr (evm := evm)
  have hb : evalExpr? config frame evm (.immutable "baseToken") = .ok (.address v.baseToken) := by
    simp only [evalExpr?, hf.immutables, immStore_get_baseToken, EvalResult.ofOption]
  cases ht with
  | notForSale hn =>
    exact ExecBlock.consRevert (ExecStmt.requireFalse (hg.trans (by rw [decide_eq_false hn])))
  | failed hv ht =>
    have hc := transferIn_call ht frame (.immutable "baseToken") (.env .caller) (.var "baseAmount")
      "__c3" hf.contract hb (by simp only [evalExpr?, envValue, pure]) (hf.evalBase evm)
    exact ExecBlock.consNormal (ExecStmt.requireTrue (hg.trans (by rw [decide_eq_true hv])))
      (ExecBlock.consRevert hc)
  | @received evm' amount result hv ht hn =>
    have hc := transferIn_call ht frame (.immutable "baseToken") (.env .caller) (.var "baseAmount")
      "__c3" hf.contract hb (by simp only [evalExpr?, envValue, pure]) (hf.evalBase evm)
    let read : Frame := { frame with locals := frame.locals.insert "__c3" (.int amount.toNat) }
    let ready : Frame := { read with locals := read.locals.insert "baseAmount" (.int amount.toNat) }
    have hread : BuyCollateralArgs read v asset recipient minimum base :=
      hf.insert "__c3" _ (by decide)
    have ha : evalExpr? config read evm' (.var "__c3") = .ok (.int amount.toNat) := by
      simp only [evalExpr?, read, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
        EvalResult.ofOption]; rfl
    have hassign : ExecStmt config read evm'
        (.assign .localVar ⟨"baseAmount", []⟩ (.var "__c3")) (.ok ready evm') :=
      ExecStmt.assign ha (assignLocalFrame hread.base)
    exact ((buyCollateralAfterIn_source hn ready (hread.setBase amount)).prepend hassign).prepend
      hc |>.prepend (ExecStmt.requireTrue (hg.trans (by rw [decide_eq_true hv])))

theorem buyCollateralAfterLock_source {v asset recipient minimum base evm result}
    (ht : BuyCollateralAfterLock v asset recipient minimum base evm result)
    (frame : Frame) (hf : BuyCollateralArgs frame v asset recipient minimum base) :
    internalBlockResult config frame evm buyCollateralAfterLockBody result := by
  let ready : Frame := { frame with
    locals := frame.locals.insert "__c1"
      (.bool (decide ((pauseBitWord evm ⟨4, by decide⟩).toNat ≠ 0))) }
  have hready : BuyCollateralArgs ready v asset recipient minimum base :=
    hf.insert "__c1" _ (by decide)
  have hp := pause_call frame evm ⟨4, by decide⟩ "__c1" hf.contract
  have hg : evalExpr? config ready evm (.unary .not (.var "__c1")) =
      .ok (.bool (decide ((pauseBitWord evm ⟨4, by decide⟩).toNat = 0))) := by
    simp only [evalExpr?, ready, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
      EvalResult.ofOption]
    simp [bind, EvalResult.bind, evalUnaryOp?]
  cases ht with
  | paused hn =>
    exact ExecBlock.consNormal hp (ExecBlock.consRevert
      (ExecStmt.requireFalse (hg.trans (by rw [decide_eq_false hn]))))
  | failed hz ht =>
    have hc := reservesTrace_call ht ready "reserves" hready.contract hready.immutables
    exact ExecBlock.consNormal hp (ExecBlock.consNormal
      (ExecStmt.requireTrue (hg.trans (by rw [decide_eq_true hz]))) (ExecBlock.consRevert hc))
  | reserves hz ht hn =>
    have hc := reservesTrace_call ht ready "reserves" hready.contract hready.immutables
    exact ((buyCollateralAfterReserves_source hn _ (hready.insert "reserves" _ (by decide)) (by
      simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]; rfl)).prepend hc).prepend
      (ExecStmt.requireTrue (hg.trans (by rw [decide_eq_true hz]))) |>.prepend hp

theorem buyCollateral_source {v asset recipient minimum base evm result}
    (ht : BuyCollateralTrace v asset recipient minimum base evm result)
    (frame : Frame) (hf : BuyCollateralArgs frame v asset recipient minimum base) :
    internalBlockResult config frame evm buyCollateralBody result := by
  have hc := reentrancy_call frame evm true "__c0" hf.contract
  cases ht with
  | reverted he => exact ExecBlock.consRevert (internalStmtResult.cast hc he)
  | staticViolation he => exact ExecBlock.consStatic (internalStmtResult.cast hc he)
  | done he ht =>
    exact (buyCollateralAfterLock_source ht _ (hf.insert "__c0" _ (by decide))).prepend
      (internalStmtResult.cast hc he)

def buyCollateralArgs (asset recipient : AccountAddress) (minimum base : UInt256) : Store :=
  ((((∅ : Store).insert "asset" (.address asset)).insert "minAmount" (.int minimum.toNat)).insert
    "baseAmount" (.int base.toNat)).insert "recipient" (.address recipient)

theorem buyCollateralPublic_source {v asset recipient minimum base evm result}
    (ht : BuyCollateralTrace v asset recipient minimum base evm result)
    (hv : evm.executionEnv.weiValue = ⟨0⟩) (hhi : evm.executionEnv.calldata.size < 2^255 + 4) :
    internalSourceResult config
      { contract := contract, locals := buyCollateralArgs asset recipient minimum base,
        immutables := immStore v } evm buyCollateralTransition.body result := by
  rw [buyCollateralTransition_body]
  let frame := calldataLocalFrame
    { contract := contract, locals := buyCollateralArgs asset recipient minimum base,
      immutables := immStore v } evm
  have hf : BuyCollateralArgs frame v asset recipient minimum base := by
    constructor <;> simp only [frame, calldataLocalFrame, buyCollateralArgs,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] <;> rfl
  have hb := buyCollateral_source ht frame hf
  cases result with
  | ok evm' =>
    obtain ⟨final, hb⟩ := hb
    exact ⟨final, ExecFuncBody.execBlockOK ((calldataPrologue_ok hv hhi).run hb)⟩
  | reverted => exact ExecFuncBody.execBlockRevert ((calldataPrologue_ok hv hhi).run hb)
  | staticViolation => exact ExecFuncBody.execBlockStatic ((calldataPrologue_ok hv hhi).run hb)

end Benchmarks.CompoundIII.Comet
