import Benchmarks.UniswapV4PoolManager.ProtocolFeesSource
import Benchmarks.UniswapV4PoolManager.WordOperationsSource
import Benchmarks.UniswapV4PoolManager.CallComposition

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

abbrev protocolFeesUpdateFunction : FunctionDecl := contract.functions[77]!

theorem protocolFeesUpdate_lookup : lookupCallable? contract "_updateProtocolFees" =
    some protocolFeesUpdateFunction.toCallable := rfl

def protocolFeesUpdatePost (evm : State) (currency : AccountAddress) (amount : UInt256) : State :=
  protocolFeesPost evm currency (protocolFeesWord evm currency + amount)

def protocolFeesUpdateResult (f : Frame) (evm : State) (currency : AccountAddress)
    (amount : UInt256) : ExecResult :=
  if evm.executionEnv.perm = false then .staticViolation
  else .returned f (protocolFeesUpdatePost evm currency amount) none

theorem protocolFeesUpdateBody {f : Frame} {evm : State} {currency : AccountAddress} {amount : UInt256}
    (hf : f.contract = contract) (hb : f.locals.get? "protocolFeesAccrued" = none)
    (hc : f.locals.get? "currency" = some (.address currency))
    (ha : f.locals.get? "amount" = some (.int (Int.ofNat amount.toNat))) :
    ExecFuncBody config f evm protocolFeesUpdateFunction.body
      (protocolFeesUpdateResult f evm currency amount) := by
  have he := evalWordAdd (protocolFeesRead (evm := evm) hf hb (evalLocalValue hc)) (evalLocalValue ha)
  have hw := protocolFeesWrite (evm := evm) (protocolFeesWord evm currency + amount) hf hb (evalLocalValue hc)
  rw [protocolFeesUpdateResult]
  by_cases hp : evm.executionEnv.perm = false
  · rw [if_pos hp]
    exact .execBlockStatic (ExecBlock.consStatic (ExecStmt.assignStatic he hw hp))
  · rw [if_neg hp]
    exact .execBlockOK (ExecBlock.consNormal (ExecStmt.assign he hw) ExecBlock.nil)

theorem protocolFeesUpdateCall {f : Frame} {evm : State} {ec ea : Expr}
    {currency : AccountAddress} {amount : UInt256} (hf : f.contract = contract)
    (hc : evalExpr? config f evm ec = .ok (.address currency))
    (ha : evalExpr? config f evm ea = .ok (.int (Int.ofNat amount.toNat))) (dest : Ident) :
    ExecStmt config f evm (.internalCall "_updateProtocolFees" [ec, ea] dest)
      (resumeCallResult f dest (protocolFeesUpdateResult f evm currency amount)) := by
  let locals : Store := ((∅ : Store).insert "amount" (.int (Int.ofNat amount.toNat))).insert
    "currency" (.address currency)
  have hb := protocolFeesUpdateBody (f := {f with locals := locals}) (evm := evm) hf
    ((store_get_ne2 _ _ _ (by decide : ("amount" == "protocolFeesAccrued") = false)
      (by decide : ("currency" == "protocolFeesAccrued") = false)).trans (store_get_empty _))
    (store_get_self _ _ _) ((store_get_ne _ _ (by decide : ("currency" == "amount") = false)).trans
      (store_get_self _ _ _))
  have hcall := internalCallFunctionExec (caller := f) (name := "_updateProtocolFees") (retVar := dest)
    (args := [ec, ea]) (argVals := [.address currency, .int (Int.ofNat amount.toNat)])
    (by simp only [evalExprs?, hc, ha, bind, EvalResult.bind, pure])
    (by rw [hf]; exact protocolFeesUpdate_lookup) rfl hb
  simpa only [protocolFeesUpdateResult, resumeCallResult_ite, resumeCallResult_static,
    resumeCallResult_returned] using hcall

end Benchmarks.UniswapV4PoolManager
