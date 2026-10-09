import Benchmarks.CompoundIII.Comet.SupplyBaseModel
import Benchmarks.CompoundIII.Comet.UserBasicRead
import Benchmarks.CompoundIII.Comet.UserBasicLocal

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000
attribute [local irreducible] signed104

theorem supplyBaseRead_source (frame : Frame) (evm : EVM.State) (dst : AccountAddress)
    (hc : frame.contract = contract) (hs : frame.locals.get? "dst" = some (.address dst))
    (hu : frame.locals.get? "userBasic" = none) :
    ExecBlock config frame evm supplyBaseReadBlock
      (.ok (supplyBaseReadFrame frame evm dst) evm) := by
  have hr := evalUserBasic frame evm dst (.var "dst") hc hu
    (by simp only [evalExpr?, hs, EvalResult.ofOption])
  apply ExecBlock.consNormal (ExecStmt.letDecl hr)
  apply ExecBlock.consNormal (ExecStmt.letDecl (evalBasicPrincipal ?_)) .nil
  simp only [evalExpr?, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
    EvalResult.ofOption]
  rfl

theorem supplyBaseReady_args (v : CometWithExtendedAssetListImmutables)
    (sender dst : AccountAddress) (requested amount : UInt256) (evm : EVM.State) :
    SupplyBaseArgs (supplyBaseReadyFrame v sender dst requested amount evm)
      sender dst amount (supplyBaseSupplied evm dst amount) := by
  constructor <;>
    simp only [supplyBaseReadyFrame, supplyBaseMathFrame, supplyBaseReadFrame,
      supplyBaseAccruedFrame, supplyBaseReceivedFrame, supplyBaseEntry, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, Std.HashMap.getElem?_empty] <;> rfl

theorem supplyBaseReady_basic (v : CometWithExtendedAssetListImmutables)
    (sender dst : AccountAddress) (requested amount : UInt256) (evm : EVM.State) :
    (supplyBaseReadyFrame v sender dst requested amount evm).locals.get? "dstUser" =
      some (userBasicValue (withdrawBaseBasic evm dst)) := by
  simp only [supplyBaseReadyFrame, supplyBaseMathFrame, supplyBaseReadFrame,
    Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
  rfl

theorem supplyBaseReady_principal {v sender dst requested amount evm}
    (hf : SupplyBaseMathFits evm (withdrawBaseBasic evm dst).principal amount) :
    (supplyBaseReadyFrame v sender dst requested amount evm).locals.get? "dstPrincipalNew" =
      some (.int (signed104 (supplyBaseNext evm dst amount))) := by
  simp only [supplyBaseReadyFrame, supplyBaseMathFrame, Std.HashMap.get?_eq_getElem?,
    Std.HashMap.getElem?_insert]
  change some (Value.int (principalValueInt evm _)) =
    some (Value.int (signed104 (principalValueWord evm _)))
  rw [principalValueWord_signed104 hf.2.1]

end Benchmarks.CompoundIII.Comet
