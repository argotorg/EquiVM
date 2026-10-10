import Benchmarks.CompoundIII.Comet.SupplyCollateralPrefixSource
import Benchmarks.CompoundIII.Comet.InternalBlockComposition

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem supplyCollateralTail_source {sender dst asset amount out}
    (frame : Frame) (evm : EVM.State) (balance next : UInt256)
    (hf : SupplyCollateralArgs frame sender dst asset amount out) (hv : AssetValid out)
    (hb : frame.locals.get? "dstCollateral" = some (.int balance.toNat))
    (hn : frame.locals.get? "dstCollateralNew" = some (.int next.toNat)) :
    internalBlockResult config frame evm supplyCollateralTail
      (assetMembershipResult evm dst (calldataWord out 0) balance next) := by
  have hc := assetMembership_call frame evm dst out balance next
    (.var "dst") (.var "assetInfo") (.var "dstCollateral") (.var "dstCollateralNew") "__c3"
    hf.contract hv.2.1
    (by simp only [evalExpr?, hf.dst, EvalResult.ofOption])
    (by simp only [evalExpr?, hf.info, EvalResult.ofOption])
    (by simp only [evalExpr?, hb, EvalResult.ofOption])
    (by simp only [evalExpr?, hn, EvalResult.ofOption])
  cases he : assetMembershipResult evm dst (calldataWord out 0) balance next with
  | reverted =>
    have hc := internalStmtResult.cast hc he
    exact ExecBlock.consRevert hc
  | staticViolation =>
    have hc := internalStmtResult.cast hc he
    exact ExecBlock.consStatic hc
  | ok evm' =>
    have hc := internalStmtResult.cast hc he
    let final := { frame with locals := frame.locals.insert "__c3" .unit }
    have hargs : SupplyCollateralArgs final sender dst asset amount out :=
      hf.insert "__c3" .unit (by decide)
    refine ⟨final, ExecBlock.consNormal hc (ExecBlock.consNormal (ExecStmt.emit
      (vals := [.address sender, .address dst, .address asset, .int amount.toNat]) ?_) .nil)⟩
    change evalExprs? config final evm' _ = _
    simp only [evalExprs?, evalExpr?, hargs.sender, hargs.dst, hargs.asset, hargs.amount,
      EvalResult.ofOption, pure, bind, EvalResult.bind]

theorem supplyCollateralPrefix_result {frame evm dst asset amount out result}
    (hb : ExecBlock config frame evm supplyCollateralPrefix
      (supplyCollateralPrefixResult frame evm dst asset amount out))
    (he : supplyCollateralPrefixOutcome evm dst asset amount out = result) :
    ExecBlock config frame evm supplyCollateralPrefix
      (match result with
       | .ok evm' => .ok (supplyCollateralReadyFrame frame evm dst asset amount) evm'
       | .reverted => .reverted
       | .staticViolation => .staticViolation) := by
  cases result <;> simpa only [supplyCollateralPrefixResult, he] using hb

theorem supplyCollateralAfterAsset_source {sender dst asset amount out}
    (frame : Frame) (evm : EVM.State)
    (hf : SupplyCollateralArgs frame sender dst asset amount out) (hv : AssetValid out) :
    internalBlockResult config frame evm (supplyCollateralPrefix ++ supplyCollateralTail)
      (supplyCollateralOutcome evm dst asset amount out) := by
  have hp := supplyCollateralPrefix_source frame evm hf
  cases he : supplyCollateralPrefixOutcome evm dst asset amount out with
  | reverted =>
    have hp := supplyCollateralPrefix_result hp he
    simp only [supplyCollateralOutcome, he]
    exact execBlock_append_term hp (by intro _ _ h; cases h)
  | staticViolation =>
    have hp := supplyCollateralPrefix_result hp he
    simp only [supplyCollateralOutcome, he]
    exact execBlock_append_term hp (by intro _ _ h; cases h)
  | ok evm' =>
    have hp := supplyCollateralPrefix_result hp he
    simp only [supplyCollateralOutcome, he]
    apply internalBlockResult.prependBlock (hp := hp)
    apply supplyCollateralTail_source _ evm' _ _ (hf.ready evm) hv
    · simp only [supplyCollateralReadyFrame, Std.HashMap.get?_eq_getElem?,
        Std.HashMap.getElem?_insert]; rfl
    · simp only [supplyCollateralReadyFrame, Std.HashMap.get?_eq_getElem?,
        Std.HashMap.getElem?_insert]; rfl

end Benchmarks.CompoundIII.Comet
