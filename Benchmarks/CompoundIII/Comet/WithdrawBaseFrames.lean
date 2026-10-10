import Benchmarks.CompoundIII.Comet.WithdrawBaseModel
import Benchmarks.CompoundIII.Comet.UserBasicRead
import Benchmarks.CompoundIII.Comet.UserBasicLocal

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000
attribute [local irreducible] signed104

theorem withdrawBaseRead_source (frame : Frame) (evm : EVM.State) (src : AccountAddress)
    (hc : frame.contract = contract) (hs : frame.locals.get? "src" = some (.address src))
    (hu : frame.locals.get? "userBasic" = none) :
    ExecBlock config frame evm withdrawBaseReadBlock
      (.ok (withdrawBaseReadFrame frame evm src) evm) := by
  have hr := evalUserBasic frame evm src (.var "src") hc hu
    (by simp only [evalExpr?, hs, EvalResult.ofOption])
  apply ExecBlock.consNormal (ExecStmt.letDecl hr)
  apply ExecBlock.consNormal (ExecStmt.letDecl (evalBasicPrincipal ?_)) .nil
  simp only [evalExpr?, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
    EvalResult.ofOption]
  rfl

theorem withdrawBaseReady_args (v : CometWithExtendedAssetListImmutables)
    (src recipient : AccountAddress) (amount : UInt256) (evm : EVM.State) :
    WithdrawBaseArgs (withdrawBaseReadyFrame v src recipient amount evm)
      v src recipient amount (withdrawBaseSupplied evm src amount) := by
  constructor <;>
    simp only [withdrawBaseReadyFrame, withdrawBaseMathFrame, withdrawBaseReadFrame,
      withdrawBaseAccruedFrame, withdrawBaseEntry, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, Std.HashMap.getElem?_empty] <;> rfl

theorem withdrawBaseReady_basic (v : CometWithExtendedAssetListImmutables)
    (src recipient : AccountAddress) (amount : UInt256) (evm : EVM.State) :
    (withdrawBaseReadyFrame v src recipient amount evm).locals.get? "srcUser" =
      some (userBasicValue (withdrawBaseBasic evm src)) := by
  simp only [withdrawBaseReadyFrame, withdrawBaseMathFrame, withdrawBaseReadFrame,
    Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
  rfl

theorem withdrawBaseReady_principal {v src recipient amount evm}
    (hf : WithdrawBaseMathFits evm (withdrawBaseBasic evm src).principal amount) :
    (withdrawBaseReadyFrame v src recipient amount evm).locals.get? "srcPrincipalNew" =
      some (.int (signed104 (withdrawBaseNext evm src amount))) := by
  simp only [withdrawBaseReadyFrame, withdrawBaseMathFrame, Std.HashMap.get?_eq_getElem?,
    Std.HashMap.getElem?_insert]
  change some (Value.int (principalValueInt evm _)) =
    some (Value.int (signed104 (principalValueWord evm _)))
  rw [principalValueWord_signed104 hf.2.1]

theorem withdrawBaseReady_balance {v src recipient amount evm}
    (hf : WithdrawBaseMathFits evm (withdrawBaseBasic evm src).principal amount) :
    (withdrawBaseReadyFrame v src recipient amount evm).locals.get? "srcBalance" =
      some (.int (signedWord (withdrawBaseBalance evm (withdrawBaseBasic evm src).principal amount))) := by
  simp only [withdrawBaseReadyFrame, withdrawBaseMathFrame, Std.HashMap.get?_eq_getElem?,
    Std.HashMap.getElem?_insert]
  rw [withdrawBaseBalance_int hf.1]
  rfl

end Benchmarks.CompoundIII.Comet
