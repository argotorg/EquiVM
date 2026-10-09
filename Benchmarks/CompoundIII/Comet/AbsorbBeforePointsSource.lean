import Benchmarks.CompoundIII.Comet.AbsorbBeforePointsModel
import Benchmarks.CompoundIII.Comet.AbsorbAccountsSource
import Benchmarks.CompoundIII.Comet.AccrueInternalSource
import Benchmarks.CompoundIII.Comet.AuthorizationSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

def absorbBeforePointsBlock : List Stmt :=
  [.internalCall "isAbsorbPaused_body" [] "__c0", .require (.unary .not (.var "__c0")),
    .letGas "startGas", .internalCall "accrueInternal" [] "__c1",
    .letDecl "i" (some (.elem (.int (.uint ⟨256, by decide⟩)))) (.intLit 0)] ++
    absorbAccountsBlock

theorem absorbBeforePoints_source {v : CometWithExtendedAssetListImmutables} {cd : ByteArray}
    {evm : State} {result : InternalOutcome} (ht : AbsorbBeforePointsTrace v cd evm result)
    {accounts : List Value} {endOffset : Nat} (absorber : AccountAddress) (startGas : UInt256)
    (hread : Solc0815.decodeAddressArrayElems? (absorbArrayLength cd) (cd.toList.drop 4)
      (absorbArrayOffset cd + 32) = some (accounts, endOffset))
    (hlen : accounts.length = absorbArrayLength cd) (hn : absorbArrayLength cd < 2^64)
    (frame : Frame) (hc : frame.contract = contract) (him : frame.immutables = immStore v)
    (ha : frame.locals.get? "absorber" = some (.address absorber))
    (hac : frame.locals.get? "accounts" = some (.array accounts))
    (hp : frame.locals.get? "liquidatorPoints" = none) :
    match result with
    | .ok evm' => ∃ final, ExecBlock config frame evm absorbBeforePointsBlock (.ok final evm') ∧
        AbsorbAccountsFrame v absorber accounts startGas (absorbArrayLength cd) final
    | .reverted => ExecBlock config frame evm absorbBeforePointsBlock .reverted
    | .staticViolation => ExecBlock config frame evm absorbBeforePointsBlock .staticViolation := by
  let ready : Frame :=
    { frame with
      locals := frame.locals.insert "__c0"
        (.bool (decide ((pauseBitWord evm ⟨3, by decide⟩).toNat ≠ 0))) }
  let gasFrame : Frame := { ready with locals := ready.locals.insert "startGas" (.int startGas.toNat) }
  let accrued : Frame := { gasFrame with locals := gasFrame.locals.insert "__c1" .unit }
  let loopFrame : Frame := { accrued with locals := accrued.locals.insert "i" (.int 0) }
  have hpause := pause_call frame evm ⟨3, by decide⟩ "__c0" hc
  have hguard : evalExpr? config ready evm (.unary .not (.var "__c0")) =
      .ok (.bool (decide ((pauseBitWord evm ⟨3, by decide⟩).toNat = 0))) := by
    simp only [evalExpr?, ready, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
      EvalResult.ofOption]
    simp [bind, EvalResult.bind, evalUnaryOp?]
  have hgas : ExecStmt config ready evm (.letGas "startGas") (.ok gasFrame evm) :=
    ExecStmt.letGas startGas
  have hcall := accrue_call v gasFrame evm "__c1" hc him
  have hframe : AbsorbAccountsFrame v absorber accounts startGas 0 loopFrame := by
    constructor <;> simp_all only [loopFrame, accrued, gasFrame, ready,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] <;> rfl
  cases ht with
  | paused hz =>
      exact ExecBlock.consNormal hpause (ExecBlock.consRevert
        (ExecStmt.requireFalse (hguard.trans (by rw [decide_eq_false hz]))))
  | accrueReverted hz he =>
      rw [he] at hcall
      exact ExecBlock.consNormal hpause (ExecBlock.consNormal
        (ExecStmt.requireTrue (hguard.trans (by rw [decide_eq_true hz])))
        (ExecBlock.consNormal hgas (ExecBlock.consRevert hcall)))
  | accrueStatic hz he =>
      rw [he] at hcall
      exact ExecBlock.consNormal hpause (ExecBlock.consNormal
        (ExecStmt.requireTrue (hguard.trans (by rw [decide_eq_true hz])))
        (ExecBlock.consNormal hgas (ExecBlock.consStatic hcall)))
  | @accrued evm' result hz he ht =>
      rw [he] at hcall
      have hinit : ExecStmt config accrued evm'
          (.letDecl "i" (some (.elem (.int (.uint ⟨256, by decide⟩)))) (.intLit 0))
          (.ok loopFrame evm') := ExecStmt.letDecl (by simp [evalExpr?, pure])
      have hloop := absorbAccounts_source ht hread hlen hn loopFrame hframe (Nat.zero_le _)
      have prepend {res : ExecResult} (hr : ExecBlock config loopFrame evm' absorbAccountsBlock res) :
          ExecBlock config frame evm absorbBeforePointsBlock res :=
        ExecBlock.consNormal hpause (ExecBlock.consNormal
          (ExecStmt.requireTrue (hguard.trans (by rw [decide_eq_true hz])))
          (ExecBlock.consNormal hgas (ExecBlock.consNormal hcall (ExecBlock.consNormal hinit hr))))
      cases result with
      | ok evm'' =>
          obtain ⟨final, hloop, hfinal⟩ := hloop
          exact ⟨final, prepend hloop, hfinal⟩
      | reverted => exact prepend hloop
      | staticViolation => exact prepend hloop

end Benchmarks.CompoundIII.Comet
