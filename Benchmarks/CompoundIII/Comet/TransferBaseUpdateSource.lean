import Benchmarks.CompoundIII.Comet.TransferBaseUpdateModel
import Benchmarks.CompoundIII.Comet.UpdateBaseSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000
attribute [local irreducible] signed104

theorem transferBaseUpdate_source (v : CometWithExtendedAssetListImmutables)
    (frame : Frame) (evm : EVM.State) (src dst : AccountAddress)
    (srcBasic dstBasic : UserBasicData) (srcNext dstNext : UInt256)
    (hc : frame.contract = contract) (hi : frame.immutables = immStore v)
    (hsrc : frame.locals.get? "src" = some (.address src))
    (hdst : frame.locals.get? "dst" = some (.address dst))
    (hsb : frame.locals.get? "srcUser" = some (userBasicValue srcBasic))
    (hdb : frame.locals.get? "dstUser" = some (userBasicValue dstBasic))
    (hsn : frame.locals.get? "srcPrincipalNew" = some (.int (signed104 srcNext)))
    (hdn : frame.locals.get? "dstPrincipalNew" = some (.int (signed104 dstNext))) :
    ExecBlock config frame evm transferBaseUpdateBlock
      (transferBaseUpdateResult frame v evm src dst srcBasic dstBasic srcNext dstNext) := by
  have hsa : evalExpr? config frame evm (.var "src") = .ok (.address src) := by
    simp only [evalExpr?, hsrc, EvalResult.ofOption]
  have hsbe : evalExpr? config frame evm (.var "srcUser") = .ok (userBasicValue srcBasic) := by
    simp only [evalExpr?, hsb, EvalResult.ofOption]
  have hsne : evalExpr? config frame evm (.var "srcPrincipalNew") =
      .ok (.int (signed104 srcNext)) := by simp only [evalExpr?, hsn, EvalResult.ofOption]
  have hs := updateBase_call v frame evm src srcBasic srcNext _ _ _ "__c9" hc hi hsa hsbe hsne
  cases ho : updateBaseOutcome v evm src srcBasic srcNext with
  | reverted =>
      simp only [ho, internalStmtResult] at hs
      simp only [transferBaseUpdateResult, transferBaseUpdateOutcome, ho]
      exact ExecBlock.consRevert hs
  | staticViolation =>
      simp only [ho, internalStmtResult] at hs
      simp only [transferBaseUpdateResult, transferBaseUpdateOutcome, ho]
      exact ExecBlock.consStatic hs
  | ok evm' =>
      simp only [ho, internalStmtResult] at hs
      let f : Frame := { frame with locals := frame.locals.insert "__c9" .unit }
      have hda : evalExpr? config f evm' (.var "dst") = .ok (.address dst) := by
        simp only [evalExpr?, f, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
        change EvalResult.ofOption .unboundVariable (frame.locals.get? "dst") = _
        rw [hdst]; rfl
      have hdbe : evalExpr? config f evm' (.var "dstUser") = .ok (userBasicValue dstBasic) := by
        simp only [evalExpr?, f, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
        change EvalResult.ofOption .unboundVariable (frame.locals.get? "dstUser") = _
        rw [hdb]; rfl
      have hdne : evalExpr? config f evm' (.var "dstPrincipalNew") =
          .ok (.int (signed104 dstNext)) := by
        simp only [evalExpr?, f, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
        change EvalResult.ofOption .unboundVariable (frame.locals.get? "dstPrincipalNew") = _
        rw [hdn]; rfl
      have hd := updateBase_call v f evm' dst dstBasic dstNext _ _ _ "__c10" hc hi hda hdbe hdne
      cases ho' : updateBaseOutcome v evm' dst dstBasic dstNext with
      | reverted =>
          simp only [ho', internalStmtResult] at hd
          simp only [transferBaseUpdateResult, transferBaseUpdateOutcome, ho, ho']
          exact ExecBlock.consNormal hs (ExecBlock.consRevert hd)
      | staticViolation =>
          simp only [ho', internalStmtResult] at hd
          simp only [transferBaseUpdateResult, transferBaseUpdateOutcome, ho, ho']
          exact ExecBlock.consNormal hs (ExecBlock.consStatic hd)
      | ok evm'' =>
          simp only [ho', internalStmtResult] at hd
          simp only [transferBaseUpdateResult, transferBaseUpdateOutcome, ho, ho']
          exact ExecBlock.consNormal hs (ExecBlock.consNormal hd ExecBlock.nil)

end Benchmarks.CompoundIII.Comet
