import Reasoning.ExternalCall
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

-- LIBRARY CANDIDATE: a typed void callback to msg.sender, guarded by its code size.
def callerCallbackFrame (frame : Frame) (caller : AccountAddress) : Frame :=
  { frame with locals := frame.locals.insert "callback" (.address caller) }

def callerCallbackCalledFrame (frame : Frame) (caller : AccountAddress) (retVar : Ident) : Frame :=
  { callerCallbackFrame frame caller with locals := (callerCallbackFrame frame caller).locals.insert retVar .unit }

def callerCallbackBody (name : Ident) (args : List Expr) (retVar : Ident) : List Stmt :=
  [.letDecl "callback" (some (.elem .address)) (.env .caller),
    .require (.binary .gt (.extCodeSize (.var "callback")) (.intLit 0)),
    .externalCall (.var "callback") name (.intLit 0) args retVar]

theorem callerCallback_receiver (cfg : Config) (frame : Frame) (evm : EVM.State) :
    evalExpr? cfg (callerCallbackFrame frame evm.executionEnv.source) evm (.var "callback") =
      .ok (.address evm.executionEnv.source) := by
  simp only [evalExpr?, callerCallbackFrame, store_get_self, EvalResult.ofOption]

theorem callerCallback_guard (cfg : Config) (frame : Frame) (evm : EVM.State) :
    evalExpr? cfg (callerCallbackFrame frame evm.executionEnv.source) evm
      (.binary .gt (.extCodeSize (.var "callback")) (.intLit 0)) =
      .ok (.bool (decide (0 < (extCodeSizeWord evm.accountMap (UInt256.ofNat evm.executionEnv.source.val)).toNat))) :=
  evalExpr_codeGuard_of_accounts_eq rfl (accountAddress_roundtrip _).symm
    (callerCallback_receiver cfg frame evm)

theorem callerCallbackPrelude (cfg : Config) (frame : Frame) (evm : EVM.State)
    (name : Ident) (args : List Expr) (retVar : Ident) (tail : List Stmt) :
    ABlock cfg evm frame (callerCallbackBody name args retVar ++ tail)
      (callerCallbackFrame frame evm.executionEnv.source) ((callerCallbackBody name args retVar).drop 1 ++ tail) := by
  exact ABlock.start.letStep (show evalExpr? cfg frame evm (.env .caller) =
    .ok (.address evm.executionEnv.source) by simp only [evalExpr?, envValue, pure])

theorem callerCallbackSourceNoCode (cfg : Config) (frame : Frame) (evm : EVM.State)
    (name : Ident) (args : List Expr) (retVar : Ident) (tail : List Stmt)
    (hc : extCodeSizeWord evm.accountMap (UInt256.ofNat evm.executionEnv.source.val) = UInt256.ofNat 0) :
    ExecBlock cfg frame evm (callerCallbackBody name args retVar ++ tail) .reverted := by
  apply (callerCallbackPrelude cfg frame evm name args retVar tail).requireRevert
  rw [callerCallback_guard, hc]
  rfl

theorem callerCallbackSourceGuard (cfg : Config) (frame : Frame) (evm : EVM.State)
    (name : Ident) (args : List Expr) (retVar : Ident) (tail : List Stmt)
    (hc : extCodeSizeWord evm.accountMap (UInt256.ofNat evm.executionEnv.source.val) ≠ UInt256.ofNat 0) :
    ABlock cfg evm frame (callerCallbackBody name args retVar ++ tail)
      (callerCallbackFrame frame evm.executionEnv.source) ((callerCallbackBody name args retVar).drop 2 ++ tail) := by
  apply (callerCallbackPrelude cfg frame evm name args retVar tail).requireStep
  rw [callerCallback_guard]
  have hp : 0 < (extCodeSizeWord evm.accountMap (UInt256.ofNat evm.executionEnv.source.val)).toNat :=
    Nat.pos_of_ne_zero (fun hz => hc (uint256_toNat_eq_zero hz))
  rw [decide_eq_true hp]

theorem callerCallbackSourceFailure (cfg : Config) (frame : Frame) (evm evm' : EVM.State)
    (name : Ident) (args : List Expr) (retVar : Ident) (tail : List Stmt) (vals : List Value) (out : ByteArray)
    (hc : extCodeSizeWord evm.accountMap (UInt256.ofNat evm.executionEnv.source.val) ≠ UInt256.ofNat 0)
    (he : evalExprs? cfg (callerCallbackFrame frame evm.executionEnv.source) evm args = .ok vals)
    (hcall : typedCallViaEVM cfg evm evm.executionEnv.source name 0 vals (false, evm', out)) :
    ExecBlock cfg frame evm (callerCallbackBody name args retVar ++ tail) .reverted := by
  apply (callerCallbackSourceGuard cfg frame evm name args retVar tail hc).run
  apply ExecBlock.consRevert
  exact ExecStmt.externalCallFailure (sendVal := 0) (callerCallback_receiver cfg frame evm)
    (by simp only [evalExpr?, pure]) he (by simpa only [address_of_val] using hcall)

theorem callerCallbackSourceSuccess (cfg : Config) (frame : Frame) (evm evm' : EVM.State)
    (name : Ident) (args : List Expr) (retVar : Ident) (tail : List Stmt) (vals : List Value) (out : ByteArray)
    (hc : extCodeSizeWord evm.accountMap (UInt256.ofNat evm.executionEnv.source.val) ≠ UInt256.ofNat 0)
    (he : evalExprs? cfg (callerCallbackFrame frame evm.executionEnv.source) evm args = .ok vals)
    (hcall : typedCallViaEVM cfg evm evm.executionEnv.source name 0 vals (true, evm', out))
    (hd : cfg.externalABI.decode? name out = some []) {result : ExecResult}
    (htail : ExecBlock cfg (callerCallbackCalledFrame frame evm.executionEnv.source retVar) evm' tail result) :
    ExecBlock cfg frame evm (callerCallbackBody name args retVar ++ tail) result := by
  apply (callerCallbackSourceGuard cfg frame evm name args retVar tail hc).run
  apply ExecBlock.consNormal (solm' := callerCallbackCalledFrame frame evm.executionEnv.source retVar) (evm' := evm') ?_ htail
  exact ExecStmt.externalCallSuccess (sendVal := 0) (value := []) (callerCallback_receiver cfg frame evm)
    (by simp only [evalExpr?, pure]) he (by simpa only [address_of_val] using hcall) hd

end Benchmarks.Morpho.MorphoBlue
