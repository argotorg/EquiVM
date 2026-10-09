import Benchmarks.CompoundIII.Comet.PauseCommon
import Benchmarks.CompoundIII.Comet.PermissionSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

theorem pause_call (frame : Frame) (evm : EVM.State) (bit : Fin 5) (ret : Ident)
    (hc : frame.contract = contract) :
    ExecStmt config frame evm (.internalCall (pauseFunctionName bit) [] ret)
      (.ok { frame with
        locals := frame.locals.insert ret
          (.bool (decide ((pauseBitWord evm bit).toNat ≠ 0))) } evm) := by
  exact ExecStmt.internalCallReturn (callee := pauseCallable bit) (locals := ∅)
    (args := []) (argVals := [])
    rfl (by rw [hc]; exact pauseCallable_lookup bit) rfl
    (by simpa only [hc] using pauseCallable_returns evm frame.immutables bit)

def AuthorizationValid (evm : EVM.State) (bit : Fin 5)
    (operator owner : AccountAddress) : Prop :=
  (pauseBitWord evm bit).toNat = 0 ∧ permissionBool evm owner operator = true

instance (evm : EVM.State) (bit : Fin 5) (operator owner : AccountAddress) :
    Decidable (AuthorizationValid evm bit operator owner) := by
  unfold AuthorizationValid
  infer_instance

def authorizationBlock (bit : Fin 5) (ownerName : Ident) : List Stmt :=
  [.internalCall (pauseFunctionName bit) [] "__c1", .require (.unary .not (.var "__c1")),
    .internalCall "hasPermission_body" [.var ownerName, .var "operator"] "__c2",
    .require (.var "__c2")]

def authorizationFrame (frame : Frame) (evm : EVM.State) (bit : Fin 5)
    (operator owner : AccountAddress) : Frame :=
  { frame with
    locals := (frame.locals.insert "__c1"
      (.bool (decide ((pauseBitWord evm bit).toNat ≠ 0)))).insert "__c2"
      (.bool (permissionBool evm owner operator)) }

theorem authorization_source (frame : Frame) (evm : EVM.State) (bit : Fin 5) (ownerName : Ident)
    (operator src : AccountAddress) (hkey : ownerName ≠ "__c1")
    (hc : frame.contract = contract)
    (ho : frame.locals.get? "operator" = some (.address operator))
    (hs : frame.locals.get? ownerName = some (.address src)) :
    ExecBlock config frame evm (authorizationBlock bit ownerName)
      (if AuthorizationValid evm bit operator src then .ok (authorizationFrame frame evm bit operator src) evm
        else .reverted) := by
  let ready : Frame := { frame with
    locals := frame.locals.insert "__c1"
      (.bool (decide ((pauseBitWord evm bit).toNat ≠ 0))) }
  have howner : ready.locals.get? ownerName = frame.locals.get? ownerName := by
    simp [ready, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, Ne.symm hkey]
  have hp := pause_call frame evm bit "__c1" hc
  have hn : evalExpr? config ready evm (.unary .not (.var "__c1")) =
      .ok (.bool (decide ((pauseBitWord evm bit).toNat = 0))) := by
    simp only [evalExpr?, ready, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
      EvalResult.ofOption]
    simp [bind, EvalResult.bind, evalUnaryOp?]
  by_cases hz : (pauseBitWord evm bit).toNat = 0
  · have ha := hasPermission_call ready evm src operator (.var ownerName) (.var "operator") "__c2" hc
      (by simp only [evalExpr?, howner, hs, EvalResult.ofOption])
      (by simp only [evalExpr?, ready, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
          change EvalResult.ofOption .unboundVariable (frame.locals.get? "operator") = _
          rw [ho]; rfl)
    have hb : evalExpr? config (authorizationFrame frame evm bit operator src) evm (.var "__c2") =
        .ok (.bool (permissionBool evm src operator)) := by
      simp only [evalExpr?, authorizationFrame, Std.HashMap.get?_eq_getElem?,
        Std.HashMap.getElem?_insert, EvalResult.ofOption]; rfl
    cases he : permissionBool evm src operator
    · simp only [AuthorizationValid, hz, he, Bool.false_eq_true, and_false, if_false]
      exact ExecBlock.consNormal hp (ExecBlock.consNormal
        (ExecStmt.requireTrue (hn.trans (by rw [decide_eq_true hz])))
        (ExecBlock.consNormal ha (ExecBlock.consRevert (ExecStmt.requireFalse
          (hb.trans (by rw [he]))))))
    · simp only [AuthorizationValid, hz, he, and_self, if_true]
      exact ExecBlock.consNormal hp (ExecBlock.consNormal
        (ExecStmt.requireTrue (hn.trans (by rw [decide_eq_true hz])))
        (ExecBlock.consNormal ha (ExecBlock.consNormal (ExecStmt.requireTrue
          (hb.trans (by rw [he]))) .nil)))
  · simp only [AuthorizationValid, hz, false_and, if_false]
    exact ExecBlock.consNormal hp (ExecBlock.consRevert
      (ExecStmt.requireFalse (hn.trans (by rw [decide_eq_false hz]))))

end Benchmarks.CompoundIII.Comet
