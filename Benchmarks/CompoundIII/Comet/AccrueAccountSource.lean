import Benchmarks.CompoundIII.Comet.AccrueAccountModel
import Benchmarks.CompoundIII.Comet.AccrueInternalSource
import Benchmarks.CompoundIII.Comet.UpdateBaseSource
import Benchmarks.CompoundIII.Comet.UserBasicRead

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem accrueAccountTail_source (v : CometWithExtendedAssetListImmutables)
    (frame : Frame) (evm : EVM.State) (addr : AccountAddress)
    (hc : frame.contract = contract) (hi : frame.immutables = immStore v)
    (ha : frame.locals.get? "account" = some (.address addr))
    (hu : frame.locals.get? "userBasic" = none) :
    internalBlockResult config frame evm accrueAccountTail (accrueAccountUpdate v evm addr) := by
  let basic := accrueAccountBasic evm addr
  let frame' : Frame := { frame with locals := frame.locals.insert "basic" (userBasicValue basic) }
  have hea : evalExpr? config frame evm (.var "account") = .ok (.address addr) := by
    simp only [evalExpr?, ha, EvalResult.ofOption]
  apply internalBlockResult.prepend (ExecStmt.letDecl (evalUserBasic frame evm addr _ hc hu hea))
  have hea' : evalExpr? config frame' evm (.var "account") = .ok (.address addr) := by
    have ha' : frame'.locals.get? "account" = some (.address addr) := by
      simp only [frame', Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
      exact ha
    simp only [evalExpr?, ha', EvalResult.ofOption]
  have heb : evalExpr? config frame' evm (.var "basic") = .ok (userBasicValue basic) := by
    simp only [evalExpr?, frame', Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
      EvalResult.ofOption]
    rfl
  have hep : evalExpr? config frame' evm (.field (.var "basic") "principal") =
      .ok (.int (signed104 (UInt256.signextend (UInt256.ofNat 12) basic.principal))) := by
    rw [signed104_signextend]
    exact evalBasicPrincipal heb
  have hcall := updateBase_call v frame' evm addr basic
    (UInt256.signextend (UInt256.ofNat 12) basic.principal)
    (.var "account") (.var "basic") (.field (.var "basic") "principal") "__c1"
    hc hi hea' heb hep
  change ExecStmt _ _ _ _ (internalStmtResult _ _ (accrueAccountUpdate v evm addr)) at hcall
  cases hr : accrueAccountUpdate v evm addr with
  | ok evm' =>
      exact ⟨_, ExecBlock.consNormal (by simpa only [hr, internalStmtResult] using hcall)
        ExecBlock.nil⟩
  | reverted => exact ExecBlock.consRevert (by simpa only [hr, internalStmtResult] using hcall)
  | staticViolation =>
      exact ExecBlock.consStatic (by simpa only [hr, internalStmtResult] using hcall)

theorem accrueAccount_block (v : CometWithExtendedAssetListImmutables) (evm : EVM.State)
    (addr : AccountAddress) :
    internalBlockResult config (accrueAccountEntry v evm addr) evm
      (.internalCall "accrueInternal" [] "__c0" :: accrueAccountTail)
      (accrueAccountOutcome v evm addr) := by
  let frame := accrueAccountEntry v evm addr
  have hcall := accrue_call v frame evm "__c0" rfl rfl
  cases hr : accrueOutcome v evm with
  | ok evm' =>
      simp only [accrueAccountOutcome, hr]
      apply internalBlockResult.prepend (by simpa only [hr, internalStmtResult] using hcall)
      refine accrueAccountTail_source v
        { frame with locals := frame.locals.insert "__c0" .unit } evm' addr rfl rfl ?_ ?_
      · simp only [frame, accrueAccountEntry, accrueAccountArgs, calldataLocalFrame,
          Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
        rfl
      · simp only [frame, accrueAccountEntry, accrueAccountArgs, calldataLocalFrame,
          Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
        simp
  | reverted =>
      simp only [accrueAccountOutcome, hr, internalBlockResult]
      exact ExecBlock.consRevert (by simpa only [hr, internalStmtResult] using hcall)
  | staticViolation =>
      simp only [accrueAccountOutcome, hr, internalBlockResult]
      exact ExecBlock.consStatic (by simpa only [hr, internalStmtResult] using hcall)

theorem accrueAccount_source (v : CometWithExtendedAssetListImmutables) (evm : EVM.State)
    (addr : AccountAddress) (hv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2^255 + 4) :
    internalSourceResult config
      { contract := contract, immutables := immStore v, locals := accrueAccountArgs addr }
      evm accrueAccountTransition.body (accrueAccountOutcome v evm addr) := by
  have hb := accrueAccount_block v evm addr
  rw [accrueAccountTransition_body]
  cases hr : accrueAccountOutcome v evm addr with
  | ok evm' =>
      rw [hr] at hb
      obtain ⟨frame', hb⟩ := hb
      exact ⟨frame', ExecFuncBody.execBlockOK ((calldataPrologue_ok hv hhi).run hb)⟩
  | reverted =>
      rw [hr] at hb
      exact ExecFuncBody.execBlockRevert ((calldataPrologue_ok hv hhi).run hb)
  | staticViolation =>
      rw [hr] at hb
      exact ExecFuncBody.execBlockStatic ((calldataPrologue_ok hv hhi).run hb)

end Benchmarks.CompoundIII.Comet
