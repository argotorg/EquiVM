import Benchmarks.CompoundIII.Comet.CollateralValueModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem collateralBalance_eval (frame : Frame) (evm : EVM.State) (out : ByteArray)
    (account : AccountAddress) (hc : frame.contract = contract)
    (hu : frame.locals.get? "userCollateral" = none)
    (ha : frame.locals.get? "account" = some (.address account)) :
    evalExpr? config (collateralAssetFrame frame out) evm collateralBalanceExpr =
      .ok (.int (collateralBalanceWord evm account out).toNat) := by
  apply evalUserCollateral (collateralAssetFrame frame out) evm account _ _ _ false hc
  · simpa only [collateralAssetFrame, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, beq_iff_eq, reduceCtorEq, if_false] using hu
  · simp only [Std.HashMap.get?_eq_getElem?] at ha
    simp only [evalExpr?, collateralAssetFrame, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, ha, EvalResult.ofOption]
    rfl
  · simp only [evalExpr?, collateralAssetFrame, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption, bind, EvalResult.bind]
    rfl

theorem collateralPriceFeed_eval (frame : Frame) (evm : EVM.State) (out : ByteArray)
    (amount : UInt256) :
    evalExpr? config (collateralBalanceFrame frame out amount) evm
      (.field (.var "asset") "priceFeed") =
      .ok (.address (AccountAddress.ofNat (calldataWord out 64).toNat)) := by
  simp only [evalExpr?, collateralBalanceFrame, collateralAssetFrame,
    Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, EvalResult.ofOption,
    bind, EvalResult.bind]
  rfl

def CollateralAfterAssetSourceResult (frame : Frame) (evm : EVM.State) (borrow : Bool)
    (out : ByteArray) (result : Option (EVM.State × CollateralValueData)) : Prop :=
  match result with
  | none => ExecBlock config (collateralAssetFrame frame out) evm
      (collateralAfterAssetBlock borrow) .reverted
  | some (evm', d) => ExecBlock config (collateralAssetFrame frame out) evm
      (collateralAfterAssetBlock borrow) (.ok (collateralValueFrame frame borrow d) evm')

theorem collateralAfterAsset_source {borrow : Bool} {out : ByteArray}
    {account : AccountAddress} {evm : EVM.State}
    {result : Option (EVM.State × CollateralValueData)}
    (ht : CollateralAfterAsset borrow out (collateralBalanceWord evm account out) evm result)
    (frame : Frame) (hc : frame.contract = contract)
    (hu : frame.locals.get? "userCollateral" = none)
    (ha : frame.locals.get? "account" = some (.address account)) :
    CollateralAfterAssetSourceResult frame evm borrow out result := by
  classical
  have hb := collateralBalance_eval frame evm out account hc hu ha
  let amount := collateralBalanceWord evm account out
  have hf := collateralPriceFeed_eval frame evm out amount
  cases ht with
  | @priceFailed evm' z priceOut hcall hh hv =>
      exact ExecBlock.consNormal (ExecStmt.letDecl hb) (ExecBlock.consRevert
        (price_call_revert (collateralBalanceFrame frame out amount) evm evm' _ _ "__c5"
          priceOut z hc hf hcall hh hv))
  | @result evm' priceOut hcall hh hv =>
      have hp := price_call_ok (collateralBalanceFrame frame out amount) evm evm' _ _ "__c5"
        priceOut hc hf hcall hh hv
      have hm := collateralMath_source
        (collateralPriceFrame frame out amount (calldataWord priceOut 32)) evm' borrow
        amount (calldataWord priceOut 32) out hc
        (by simp only [collateralPriceFrame, collateralBalanceFrame, collateralAssetFrame,
          Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]; rfl)
        (by simp only [evalExpr?, collateralPriceFrame, collateralBalanceFrame,
          Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, EvalResult.ofOption]; rfl)
        (by simp only [evalExpr?, collateralPriceFrame, Std.HashMap.get?_eq_getElem?,
          Std.HashMap.getElem?_insert, EvalResult.ofOption]; rfl)
      apply Classical.byCases (p :=
        CollateralMathValid borrow amount (calldataWord priceOut 32) out)
      · intro hvalid
        rw [if_pos hvalid]
        rw [if_pos hvalid] at hm
        exact ExecBlock.consNormal (ExecStmt.letDecl hb) (ExecBlock.consNormal hp hm)
      · intro hvalid
        rw [if_neg hvalid]
        rw [if_neg hvalid] at hm
        exact ExecBlock.consNormal (ExecStmt.letDecl hb) (ExecBlock.consNormal hp hm)

theorem collateralValue_source {v : CometWithExtendedAssetListImmutables}
    {borrow : Bool} {account : AccountAddress} {i : UInt256} {evm : EVM.State}
    {result : Option (EVM.State × CollateralValueData)}
    (ht : CollateralValueTrace v borrow account i evm result) (frame : Frame)
    (hc : frame.contract = contract) (hi : frame.immutables = immStore v)
    (hu : frame.locals.get? "userCollateral" = none)
    (ha : frame.locals.get? "account" = some (.address account))
    (he : evalExpr? config frame evm (.var "i") = .ok (.int i.toNat)) :
    CollateralValueSourceResult frame evm borrow (collateralValueBlock borrow) result := by
  have him : frame.immutables.get? "assetList" = some (.address v.assetList) := by
    rw [hi]; exact immStore_get_assetList v
  cases ht with
  | @assetFailed evm' z out hcall hh hv =>
      exact ExecBlock.consRevert (asset_call_revert frame evm evm' i v.assetList _ "asset"
        out z hc him he hcall hh hv)
  | @assetOk evm' out result hcall hh hv htail =>
      have hasset := asset_call_ok frame evm evm' i v.assetList _ "asset"
        out hc him he hcall hh hv
      have hb := collateralAfterAsset_source htail frame hc hu ha
      cases result with
      | none => exact ExecBlock.consNormal hasset hb
      | some r =>
          obtain ⟨evm'', d⟩ := r
          exact ExecBlock.consNormal hasset hb

end Benchmarks.CompoundIII.Comet
