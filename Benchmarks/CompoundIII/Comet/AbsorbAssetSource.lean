import Benchmarks.CompoundIII.Comet.AbsorbAssetModel
import Benchmarks.CompoundIII.Comet.AbsorbAfterAssetSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

theorem absorbAsset_source {v : CometWithExtendedAssetListImmutables} {account : AccountAddress}
    {i delta : UInt256} {evm : State} {result : InternalValueOutcome AbsorbAssetData}
    (ht : AbsorbAssetTrace v account i delta evm result) (frame : Frame)
    (absorber : AccountAddress) (hc : frame.contract = contract)
    (hi : frame.immutables = immStore v)
    (hd : frame.locals.get? "deltaValue" = some (.int delta.toNat))
    (ha : frame.locals.get? "absorber" = some (.address absorber))
    (hb : frame.locals.get? "account" = some (.address account))
    (hU : frame.locals.get? "userCollateral" = none)
    (hT : frame.locals.get? "totalsCollateral" = none)
    (he : evalExpr? config frame evm (.var "i") = .ok (.int i.toNat)) :
    ExecBlock config frame evm absorbAssetBlock
      (internalValueFrameResult (absorbAssetFrame frame delta) result) := by
  have him : frame.immutables.get? "assetList" = some (.address v.assetList) := by
    rw [hi]; exact immStore_get_assetList v
  cases ht with
  | @assetFailed evm' z out hcall hh hv =>
      exact ExecBlock.consRevert (asset_call_revert frame evm evm' i v.assetList _ "assetInfo"
        out z hc him he hcall hh hv)
  | @assetOk evm' out result hcall hh hv htail =>
      have hasset := asset_call_ok frame evm evm' i v.assetList _ "assetInfo"
        out hc him he hcall hh hv
      let ready := absorbAssetInfoFrame frame out
      have hget (key : String) (hk : "assetInfo" ≠ key) :
          ready.locals.get? key = frame.locals.get? key := by
        simp only [ready, absorbAssetInfoFrame, Std.HashMap.get?_eq_getElem?,
          Std.HashMap.getElem?_insert, beq_iff_eq, if_neg hk]
      have hb := absorbAfterAsset_source htail ready absorber hc
        (by simp only [ready, absorbAssetInfoFrame, Std.HashMap.get?_eq_getElem?,
          Std.HashMap.getElem?_insert]; rfl)
        ((hget _ (by decide)).trans hd) ((hget _ (by decide)).trans ha)
        ((hget _ (by decide)).trans hb) ((hget _ (by decide)).trans hU)
        ((hget _ (by decide)).trans hT)
      cases result with
      | reverted => exact ExecBlock.consNormal hasset hb
      | staticViolation => exact ExecBlock.consNormal hasset hb
      | ok evm'' price => exact ExecBlock.consNormal hasset hb

end Benchmarks.CompoundIII.Comet
