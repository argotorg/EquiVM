import Benchmarks.CompoundIII.Comet.TransferCollateralTrace
import Benchmarks.CompoundIII.Comet.TransferCollateralLocals

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

def transferCollateralCheckTail : List Stmt :=
  [.internalCall "isBorrowCollateralized_body" [.var "src"] "__c3", .require (.var "__c3"),
    .emit "TransferCollateral" [.var "src", .var "dst", .var "asset", .var "amount"]]

def transferCollateralDstTail : List Stmt :=
  .internalCall "updateAssetsIn"
    [.var "dst", .var "assetInfo", .var "dstCollateral", .var "dstCollateralNew"] "__c2" ::
    transferCollateralCheckTail

def transferCollateralSrcTail : List Stmt :=
  .internalCall "updateAssetsIn"
    [.var "src", .var "assetInfo", .var "srcCollateral", .var "srcCollateralNew"] "__c1" ::
    transferCollateralDstTail

theorem transferCollateralCheck_source {v src dst asset amount evm result}
    (ht : TransferCollateralCheck v src evm result) (frame : Frame)
    (hf : TransferCollateralArgs frame v src dst asset amount) :
    internalBlockResult config frame evm transferCollateralCheckTail result := by
  have hcall {r} (hc : CollateralCheckTrace v true src evm r) :=
    collateralCheck_call hc frame (.var "src") "__c3" hf.contract hf.immutables
      (by simp only [evalExpr?, hf.src, EvalResult.ofOption])
  have he (value : Bool) (evm' : EVM.State) : evalExpr? config
      { frame with locals := frame.locals.insert "__c3" (.bool value) } evm' (.var "__c3") =
      .ok (.bool value) := by
    simp only [evalExpr?, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
      EvalResult.ofOption]; rfl
  cases ht with
  | failed ht => exact ExecBlock.consRevert (hcall ht)
  | rejected ht =>
    exact ExecBlock.consNormal (hcall ht) (ExecBlock.consRevert (ExecStmt.requireFalse (he _ _)))
  | @accepted evm' ht =>
    let ready := { frame with locals := frame.locals.insert "__c3" (.bool true) }
    have hf' : TransferCollateralArgs ready v src dst asset amount :=
      hf.insert "__c3" (.bool true) (by decide)
    have hargs : evalExprs? config ready evm'
        [.var "src", .var "dst", .var "asset", .var "amount"] =
        .ok [.address src, .address dst, .address asset, .int amount.toNat] := by
      simp only [evalExprs?, evalExpr?, hf'.src, hf'.dst, hf'.asset, hf'.amount,
        EvalResult.ofOption, pure, bind, EvalResult.bind]
    cases hp : evm'.executionEnv.perm
    · simp only [emitOutcome, hp, Bool.false_eq_true, if_false, internalBlockResult]
      exact ExecBlock.consNormal (hcall ht) (ExecBlock.consNormal (ExecStmt.requireTrue (he _ _))
        (ExecBlock.consStatic (ExecStmt.emitStatic hargs hp)))
    · simp only [emitOutcome, hp, if_true, internalBlockResult]
      exact ⟨ready, ExecBlock.consNormal (hcall ht)
        (ExecBlock.consNormal (ExecStmt.requireTrue (he _ _))
          (ExecBlock.consNormal (ExecStmt.emit hargs) .nil))⟩

theorem transferCollateralDst_source {v src dst asset amount balance next evm out result}
    (ht : TransferCollateralDstMember v src dst balance next evm out result) (frame : Frame)
    (hf : TransferCollateralArgs frame v src dst asset amount) (ho : (calldataWord out 0).toNat < 256)
    (ha : frame.locals.get? "assetInfo" = some (assetValue out))
    (hb : frame.locals.get? "dstCollateral" = some (.int balance.toNat))
    (hn : frame.locals.get? "dstCollateralNew" = some (.int next.toNat)) :
    internalBlockResult config frame evm transferCollateralDstTail result := by
  have hc := assetMembership_call frame evm dst out balance next (.var "dst")
    (.var "assetInfo") (.var "dstCollateral") (.var "dstCollateralNew") "__c2" hf.contract ho
    (by simp only [evalExpr?, hf.dst, EvalResult.ofOption])
    (by simp only [evalExpr?, ha, EvalResult.ofOption])
    (by simp only [evalExpr?, hb, EvalResult.ofOption])
    (by simp only [evalExpr?, hn, EvalResult.ofOption])
  cases ht with
  | reverted hm => rw [hm] at hc; exact ExecBlock.consRevert hc
  | staticViolation hm => rw [hm] at hc; exact ExecBlock.consStatic hc
  | done hm tail =>
    rw [hm] at hc
    exact (transferCollateralCheck_source tail _
      (hf.insert "__c2" .unit (by decide))).prepend hc

theorem transferCollateralSrc_source
    {v src dst asset amount srcBalance srcNext dstBalance dstNext evm out result}
    (ht : TransferCollateralSrcMember v src dst srcBalance srcNext dstBalance dstNext evm out result)
    (frame : Frame) (hf : TransferCollateralArgs frame v src dst asset amount)
    (hb : TransferCollateralBalances frame srcBalance srcNext dstBalance dstNext)
    (ho : (calldataWord out 0).toNat < 256)
    (ha : frame.locals.get? "assetInfo" = some (assetValue out)) :
    internalBlockResult config frame evm transferCollateralSrcTail result := by
  have hc := assetMembership_call frame evm src out srcBalance srcNext (.var "src")
    (.var "assetInfo") (.var "srcCollateral") (.var "srcCollateralNew") "__c1" hf.contract ho
    (by simp only [evalExpr?, hf.src, EvalResult.ofOption])
    (by simp only [evalExpr?, ha, EvalResult.ofOption])
    (by simp only [evalExpr?, hb.src, EvalResult.ofOption])
    (by simp only [evalExpr?, hb.srcNext, EvalResult.ofOption])
  cases ht with
  | reverted hm => rw [hm] at hc; exact ExecBlock.consRevert hc
  | staticViolation hm => rw [hm] at hc; exact ExecBlock.consStatic hc
  | done hm tail =>
    rw [hm] at hc
    have hb' := hb.insert "__c1" .unit (by decide)
    apply (transferCollateralDst_source tail _ (hf.insert "__c1" .unit (by decide)) ho
      ?_ hb'.dst hb'.dstNext).prepend hc
    simpa only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] using ha

theorem transferCollateralTail_source
    {v src dst asset amount srcBalance srcNext dstBalance dstNext evm result}
    (ht : TransferCollateralTailTrace v src dst asset srcBalance srcNext dstBalance dstNext evm result)
    (frame : Frame) (hf : TransferCollateralArgs frame v src dst asset amount)
    (hb : TransferCollateralBalances frame srcBalance srcNext dstBalance dstNext) :
    internalBlockResult config frame evm transferCollateralTail result := by
  have hcall {r} (hc : AssetSearch v asset 0 evm r) :=
    assetSearch_call hc frame (.var "asset") "assetInfo" hf.contract hf.immutables
      (by simp only [evalExpr?, hf.asset, EvalResult.ofOption])
  cases ht with
  | failed ht => exact ExecBlock.consRevert (hcall ht)
  | found ht hv tail =>
    apply (transferCollateralSrc_source tail _ (hf.insert "assetInfo" _ (by decide))
      (hb.insert "assetInfo" _ (by decide)) hv.2.1 ?_).prepend (hcall ht)
    simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]; rfl

end Benchmarks.CompoundIII.Comet
