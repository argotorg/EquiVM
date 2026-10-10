import Benchmarks.UniswapV4PoolManager.ProtocolFeeSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

abbrev poolGetFunction : FunctionDecl := contract.functions[15]!
abbrev poolSetProtocolFunction : FunctionDecl := contract.functions[53]!
theorem poolGet_lookup : lookupCallable? contract "_getPool" = some poolGetFunction.toCallable := rfl
theorem poolSetProtocol_lookup : lookupCallable? contract "Pool_setProtocolFee" = some poolSetProtocolFunction.toCallable := rfl

def poolGetAlias : Ident := "__solm_storage_ref._@.Benchmarks.UniswapV4PoolManager.SpecSyntax.2010301240._hygCtx._hyg.5"
def poolSetProtocolAlias : Ident := "__solm_storage_ref._@.Benchmarks.UniswapV4PoolManager.SpecSyntax.2010301240._hygCtx._hyg.17"

theorem poolGetBody {f : Frame} {evm : EVM.State} {id : UInt256}
    (hf : f.contract = contract) (hi : f.locals.get? "id" = some (wordBytes32Value id))
    (hb : f.locals.get? "_pools" = none) :
    ExecFuncBody config f evm poolGetFunction.body
      (.returned {f with locals := f.locals.insert poolGetAlias (poolRefValue id)} evm (some [poolRefValue id])) := by
  apply ExecFuncBody.execBlockRet
  exact ExecBlock.consNormal (ExecStmt.letStorage (poolMappingResolve hf hb (evalLocalValue hi)))
    (ABlock.start.returns (evalLocalValue (store_get_self _ _ _)))

theorem poolGetCall {f : Frame} {evm : EVM.State} {e : Expr} {id : UInt256}
    (hf : f.contract = contract) (he : evalExpr? config f evm e = .ok (wordBytes32Value id)) (retVar : Ident) :
    ExecStmt config f evm (.internalCall "_getPool" [e] retVar)
      (.ok {f with locals := f.locals.insert retVar (poolRefValue id)} evm) := by
  apply internalCallFunctionReturn (argVals := [wordBytes32Value id]) (value := some [poolRefValue id])
    (evalExprs?_singleton he) (by rw [hf]; exact poolGet_lookup) rfl
  exact poolGetBody hf (store_get_self _ _ _)
    ((store_get_ne _ _ (by decide : ("id" == "_pools") = false)).trans (store_get_empty _))

def poolSetProtocolFrame (f : Frame) (evm : EVM.State) (id fee : UInt256) : Frame :=
  poolSetSlot0Frame f id (slot0ProtocolFeeWord (poolSlot0Word evm id) fee) poolSetProtocolAlias
def poolSetProtocolPost (evm : EVM.State) (id fee : UInt256) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (poolSlot id) (slot0ProtocolFeeWord (poolSlot0Word evm id) fee)
def poolSetProtocolResult (f : Frame) (evm : EVM.State) (id fee : UInt256) : ExecResult :=
  poolSetSlot0Result f evm id (slot0ProtocolFeeWord (poolSlot0Word evm id) fee)

theorem poolSetProtocolBody {f : Frame} {evm : EVM.State} {id fee : UInt256}
    (hf : f.contract = contract) (hs : f.locals.get? "self" = some (poolRefValue id))
    (he : f.locals.get? "protocolFee" = some (.int (Int.ofNat fee.toNat))) (hc : fee.toNat < 2^24) :
    ExecFuncBody config f evm poolSetProtocolFunction.body
      (poolSetProtocolResult (poolSetProtocolFrame f evm id fee) evm id fee) := by
  exact poolSetSlot0BodyExec poolSetProtocolAlias "protocolFee" "Slot0Library_setProtocolFee"
    (by decide) (by decide) (by decide) hf hs he
    (fun hf hs he => slot0ProtocolFeeCall hf hc (poolSlot0_read hs) (evalLocalValue he) "__c1")

def poolSetProtocolCallResult (f : Frame) (evm : EVM.State) (id fee : UInt256) (retVar : Ident) : ExecResult :=
  resumeCallResult f retVar (poolSetProtocolResult f evm id fee)

theorem poolSetProtocolCall {f : Frame} {evm : EVM.State} {ep ef : Expr} {id fee : UInt256}
    (hf : f.contract = contract) (hc : fee.toNat < 2^24)
    (hp : evalExpr? config f evm ep = .ok (poolRefValue id))
    (he : evalExpr? config f evm ef = .ok (.int (Int.ofNat fee.toNat))) (retVar : Ident) :
    ExecStmt config f evm (.internalCall "Pool_setProtocolFee" [ep, ef] retVar)
      (poolSetProtocolCallResult f evm id fee retVar) := by
  have hb := poolSetProtocolBody (f := {f with locals := ((∅ : Store).insert "protocolFee" (.int (Int.ofNat fee.toNat))).insert "self" (poolRefValue id)})
    (evm := evm) hf (store_get_self _ _ _)
    ((store_get_ne _ _ (by decide : ("self" == "protocolFee") = false)).trans (store_get_self _ _ _)) hc
  have hcall := internalCallFunctionExec (caller := f) (name := "Pool_setProtocolFee") (retVar := retVar)
    (args := [ep, ef]) (argVals := [poolRefValue id, .int (Int.ofNat fee.toNat)])
    (by simp only [evalExprs?, hp, he, bind, EvalResult.bind, pure])
    (by rw [hf]; exact poolSetProtocol_lookup) (by rfl) hb
  simpa only [poolSetProtocolCallResult, poolSetProtocolResult, poolSetSlot0Result, resumeCallResult_ite,
    resumeCallResult_reverted, resumeCallResult_static, resumeCallResult_returned] using hcall

end Benchmarks.UniswapV4PoolManager
