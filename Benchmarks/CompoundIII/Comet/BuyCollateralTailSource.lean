import Benchmarks.CompoundIII.Comet.BuyCollateralFrames
import Benchmarks.CompoundIII.Comet.SafeUintSource
import Benchmarks.CompoundIII.Comet.ReentrancySource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

theorem buyCollateralTransfer_source {asset recipient amount evm result}
    (ht : BuyCollateralTransfer asset recipient amount evm result)
    {v minimum base} (frame : Frame) (hf : BuyCollateralArgs frame v asset recipient minimum base)
    (hh : frame.locals.get? "collateralAmount" = some (.int amount.toNat)) :
    internalBlockResult config frame evm buyCollateralTransferBody result := by
  have ha : evalExpr? config frame evm (.var "collateralAmount") = .ok (.int amount.toNat) := by
    simp only [evalExpr?, hh, EvalResult.ofOption]
  have hc := safeUint_call ⟨128, by decide⟩ "safe128" safe128Callable_lookup frame evm amount
    (.var "collateralAmount") "__c6" hf.contract ha
  let ready : Frame := { frame with locals := frame.locals.insert "__c6" (.int amount.toNat) }
  have hready : BuyCollateralArgs ready v asset recipient minimum base :=
    hf.insert "__c6" _ (by decide)
  have ham : evalExpr? config ready evm (.var "__c6") = .ok (.int amount.toNat) := by
    simp only [evalExpr?, ready, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
      EvalResult.ofOption]; rfl
  cases ht with
  | tooLarge hw =>
    simp only [if_neg hw] at hc
    exact ExecBlock.consRevert hc
  | failed hw ht =>
    simp only [if_pos hw] at hc
    have ho := transferOut_call ht ready (.var "asset") (.var "recipient") (.var "__c6")
      "__c7" hready.contract (hready.evalAsset evm) (hready.evalRecipient evm) ham
    exact ExecBlock.consNormal hc (ExecBlock.consRevert ho)
  | @done evm' hw ht hp =>
    simp only [if_pos hw] at hc
    have ho := transferOut_call ht ready (.var "asset") (.var "recipient") (.var "__c6")
      "__c7" hready.contract (hready.evalAsset evm) (hready.evalRecipient evm) ham
    let final : Frame := { ready with locals := ready.locals.insert "__c7" .unit }
    have hfinal : BuyCollateralArgs final v asset recipient minimum base :=
      hready.insert "__c7" _ (by decide)
    have hh' : final.locals.get? "collateralAmount" = some (.int amount.toNat) := by
      simpa only [final, ready, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] using hh
    have hemit : evalExprs? config final evm'
        [.env .caller, .var "asset", .var "baseAmount", .var "collateralAmount"] =
        .ok [.address evm'.executionEnv.source, .address asset, .int base.toNat,
          .int amount.toNat] := by
      simp only [evalExprs?, evalExpr?, envValue, hfinal.asset, hfinal.base, hh',
        EvalResult.ofOption, pure, bind, EvalResult.bind]
    have hend := reentrancy_call final evm' false "__c8" hfinal.contract
    simp only [reentrancyOutcome, Bool.false_and, Bool.false_eq_true, if_false,
      reentrancyWriteOutcome, hp, if_true, internalStmtResult] at hend
    exact ⟨_, ExecBlock.consNormal hc (ExecBlock.consNormal ho
      (ExecBlock.consNormal (ExecStmt.emit hemit) (execBlock_singleton hend)))⟩

theorem buyCollateralAfterQuote_source {asset recipient minimum amount evm result}
    (ht : BuyCollateralAfterQuote asset recipient minimum amount evm result)
    {v base} (frame : Frame) (hf : BuyCollateralArgs frame v asset recipient minimum base)
    (hh : frame.locals.get? "collateralAmount" = some (.int amount.toNat)) :
    internalBlockResult config frame evm buyCollateralAfterQuoteBody result := by
  have hm : evalExpr? config frame evm
      (.binary .ge (.var "collateralAmount") (.var "minAmount")) =
      .ok (.bool (decide (minimum.toNat ≤ amount.toNat))) := by
    simp only [evalExpr?, hh, hf.minimum, EvalResult.ofOption, bind,
      EvalResult.bind, evalBinaryOp?]
    simp
  have hcheck (evm' : EVM.State) (reserves : UInt256) :
      evalExpr? config { frame with locals := frame.locals.insert "__c5" (.int reserves.toNat) }
        evm' (.binary .le (.var "collateralAmount") (.var "__c5")) =
        .ok (.bool (decide (amount.toNat ≤ reserves.toNat))) := by
    have hh' := hh
    simp only [Std.HashMap.get?_eq_getElem?] at hh'
    simp only [evalExpr?, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, hh',
      EvalResult.ofOption, bind, EvalResult.bind, evalBinaryOp?]
    simp
  cases ht with
  | minimumFailed hn =>
    exact ExecBlock.consRevert (ExecStmt.requireFalse (hm.trans (by rw [decide_eq_false hn])))
  | reservesFailed hmin ht =>
    have hc := collateralReservesTrace_call ht frame (.var "asset") "__c5"
      hf.contract (hf.evalAsset evm)
    exact ExecBlock.consNormal (ExecStmt.requireTrue (hm.trans (by rw [decide_eq_true hmin])))
      (ExecBlock.consRevert hc)
  | @insufficient evm' reserves hmin ht hs =>
    have hc := collateralReservesTrace_call ht frame (.var "asset") "__c5"
      hf.contract (hf.evalAsset evm)
    exact ExecBlock.consNormal (ExecStmt.requireTrue (hm.trans (by rw [decide_eq_true hmin])))
      (ExecBlock.consNormal hc (ExecBlock.consRevert
        (ExecStmt.requireFalse ((hcheck evm' reserves).trans (by rw [decide_eq_false hs])))))
  | @transfer evm' reserves result hmin ht hs hn =>
    have hc := collateralReservesTrace_call ht frame (.var "asset") "__c5"
      hf.contract (hf.evalAsset evm)
    have hf' := hf.insert "__c5" (.int reserves.toNat) (by decide)
    have hh' : (frame.locals.insert "__c5" (.int reserves.toNat)).get? "collateralAmount" =
        some (.int amount.toNat) := by
      simpa only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] using hh
    exact ((buyCollateralTransfer_source hn _ hf' hh').prepend
      (ExecStmt.requireTrue ((hcheck evm' reserves).trans (by rw [decide_eq_true hs])))).prepend
      hc |>.prepend (ExecStmt.requireTrue (hm.trans (by rw [decide_eq_true hmin])))

end Benchmarks.CompoundIII.Comet
