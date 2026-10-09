import Benchmarks.CompoundIII.Comet.TransferBaseModel
import Benchmarks.CompoundIII.Comet.UserBasicRead
import Benchmarks.CompoundIII.Comet.UserBasicLocal

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000
attribute [local irreducible] signed104

theorem transferBaseRead_source (frame : Frame) (evm : EVM.State) (src dst : AccountAddress)
    (hc : frame.contract = contract) (hs : frame.locals.get? "src" = some (.address src))
    (hd : frame.locals.get? "dst" = some (.address dst)) (hu : frame.locals.get? "userBasic" = none) :
    ExecBlock config frame evm transferBaseReadBlock (.ok (transferBaseReadFrame frame evm src dst)
      evm) := by
  have hsrc := evalUserBasic frame evm src (.var "src") hc hu
    (by simp only [evalExpr?, hs, EvalResult.ofOption])
  let f1 : Frame := { frame with
    locals := frame.locals.insert "srcUser" (userBasicValue (withdrawBaseBasic evm src)) }
  have hdu : f1.locals.get? "userBasic" = none := by
    simpa only [f1, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] using hu
  have hde : evalExpr? config f1 evm (.var "dst") = .ok (.address dst) := by
    simp only [evalExpr?, f1, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
    change EvalResult.ofOption .unboundVariable (frame.locals.get? "dst") = _
    rw [hd]; rfl
  have hdst := evalUserBasic f1 evm dst (.var "dst") hc hdu hde
  let f2 : Frame := { f1 with
    locals := f1.locals.insert "dstUser" (userBasicValue (withdrawBaseBasic evm dst)) }
  have hse : evalExpr? config f2 evm (.var "srcUser") =
      .ok (userBasicValue (withdrawBaseBasic evm src)) := by
    simp only [evalExpr?, f2, f1, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
      EvalResult.ofOption]; rfl
  let f3 : Frame := { f2 with
    locals := f2.locals.insert "srcPrincipal" (.int (signed104 (withdrawBaseBasic evm src).principal)) }
  have hde' : evalExpr? config f3 evm (.var "dstUser") =
      .ok (userBasicValue (withdrawBaseBasic evm dst)) := by
    simp only [evalExpr?, f3, f2, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
      EvalResult.ofOption]; rfl
  exact ExecBlock.consNormal (ExecStmt.letDecl hsrc)
    (ExecBlock.consNormal (ExecStmt.letDecl hdst)
      (ExecBlock.consNormal (ExecStmt.letDecl (evalBasicPrincipal hse))
        (ExecBlock.consNormal (ExecStmt.letDecl (evalBasicPrincipal hde')) .nil)))

theorem transferBaseReady_args {v src dst amount evm}
    (hf : TransferBaseMathFits evm (withdrawBaseBasic evm src).principal
      (withdrawBaseBasic evm dst).principal amount) :
    TransferBaseTailArgs (transferBaseReadyFrame v src dst amount evm) v src dst
      (withdrawBaseBalance evm (withdrawBaseBasic evm src).principal amount)
      (withdrawBaseSupplied evm src amount) (supplyBaseSupplied evm dst amount) := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | rw [withdrawBaseBalance_int hf.1.1]
    | skip
  all_goals
    simp only [transferBaseReadyFrame, transferBaseMathFrame, transferBaseAmountsFrame,
      transferBasePrincipalFrame, transferBaseBalanceFrame, transferBaseSrcBalanceFrame,
      transferBaseReadFrame, transferBaseAccruedFrame, transferBaseEntry,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, Std.HashMap.getElem?_empty]
    rfl

theorem transferBaseReady_srcBasic (v : CometWithExtendedAssetListImmutables)
    (src dst : AccountAddress) (amount : UInt256) (evm : EVM.State) :
    (transferBaseReadyFrame v src dst amount evm).locals.get? "srcUser" =
      some (userBasicValue (withdrawBaseBasic evm src)) := by
  simp only [transferBaseReadyFrame, transferBaseMathFrame, transferBaseAmountsFrame,
    transferBasePrincipalFrame, transferBaseBalanceFrame, transferBaseSrcBalanceFrame,
    transferBaseReadFrame, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
  rfl

theorem transferBaseReady_dstBasic (v : CometWithExtendedAssetListImmutables)
    (src dst : AccountAddress) (amount : UInt256) (evm : EVM.State) :
    (transferBaseReadyFrame v src dst amount evm).locals.get? "dstUser" =
      some (userBasicValue (withdrawBaseBasic evm dst)) := by
  simp only [transferBaseReadyFrame, transferBaseMathFrame, transferBaseAmountsFrame,
    transferBasePrincipalFrame, transferBaseBalanceFrame, transferBaseSrcBalanceFrame,
    transferBaseReadFrame, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
  rfl

theorem transferBaseReady_srcNext {v src dst amount evm}
    (hf : TransferBaseMathFits evm (withdrawBaseBasic evm src).principal
      (withdrawBaseBasic evm dst).principal amount) :
    (transferBaseReadyFrame v src dst amount evm).locals.get? "srcPrincipalNew" =
      some (.int (signed104 (withdrawBaseNext evm src amount))) := by
  rw [withdrawBaseNext, withdrawBasePrincipal, principalValueWord_signed104 hf.1.2.1]
  simp only [transferBaseReadyFrame, transferBaseMathFrame, transferBaseAmountsFrame,
    transferBasePrincipalFrame, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
  rfl

theorem transferBaseReady_dstNext {v src dst amount evm}
    (hf : TransferBaseMathFits evm (withdrawBaseBasic evm src).principal
      (withdrawBaseBasic evm dst).principal amount) :
    (transferBaseReadyFrame v src dst amount evm).locals.get? "dstPrincipalNew" =
      some (.int (signed104 (supplyBaseNext evm dst amount))) := by
  rw [supplyBaseNext, supplyBasePrincipal, principalValueWord_signed104 hf.2.2.1]
  simp only [transferBaseReadyFrame, transferBaseMathFrame, transferBaseAmountsFrame,
    transferBasePrincipalFrame, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
  rfl

end Benchmarks.CompoundIII.Comet
