import Benchmarks.UniswapV4PoolManager.PoolSetSlot0Source

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

abbrev poolSetFeeFunction : FunctionDecl := contract.functions[50]!
theorem poolSetFee_lookup : lookupCallable? contract "Pool_setLPFee" = some poolSetFeeFunction.toCallable := rfl

def poolSetFeeAlias : Ident := "__solm_storage_ref._@.Benchmarks.UniswapV4PoolManager.SpecSyntax.2010301240._hygCtx._hyg.16"
def poolSetFeeFrame (f : Frame) (evm : EVM.State) (id fee : UInt256) : Frame :=
  {f with locals := (((f.locals.insert poolSetFeeAlias (poolRefValue id)).insert "__c0" .unit).insert
    "__c1" (wordBytes32Value (slot0LPFeeWord (poolSlot0Word evm id) fee)))}
def poolSetFeePost (evm : EVM.State) (id fee : UInt256) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (poolSlot id) (slot0LPFeeWord (poolSlot0Word evm id) fee)

def poolSetFeeResult (f : Frame) (evm : EVM.State) (id fee : UInt256) : ExecResult :=
  if poolSqrtPriceWord evm id = ⟨0⟩ then .reverted else
  if evm.executionEnv.perm = false then .staticViolation else .returned f (poolSetFeePost evm id fee) none

theorem poolSetFeeBody {f : Frame} {evm : EVM.State} {id fee : UInt256}
    (hf : f.contract = contract) (hs : f.locals.get? "self" = some (poolRefValue id))
    (he : f.locals.get? "lpFee" = some (.int (Int.ofNat fee.toNat))) (hc : fee.toNat < 2^24) :
    ExecFuncBody config f evm poolSetFeeFunction.body
      (poolSetFeeResult (poolSetFeeFrame f evm id fee) evm id fee) := by
  exact poolSetSlot0BodyExec poolSetFeeAlias "lpFee" "Slot0Library_setLpFee"
    (by decide) (by decide) (by decide) hf hs he
    (fun hf hs he => slot0LPFeeCall hf hc (poolSlot0_read hs) (evalLocalValue he) "__c1")

def poolSetFeeCallResult (f : Frame) (evm : EVM.State) (id fee : UInt256) (retVar : Ident) : ExecResult :=
  resumeCallResult f retVar (poolSetFeeResult f evm id fee)

theorem poolSetFeeCall {f : Frame} {evm : EVM.State} {ep ef : Expr} {id fee : UInt256}
    (hf : f.contract = contract) (hc : fee.toNat < 2^24)
    (hp : evalExpr? config f evm ep = .ok (poolRefValue id))
    (he : evalExpr? config f evm ef = .ok (.int (Int.ofNat fee.toNat))) (retVar : Ident) :
    ExecStmt config f evm (.internalCall "Pool_setLPFee" [ep, ef] retVar)
      (poolSetFeeCallResult f evm id fee retVar) := by
  have hb := poolSetFeeBody (f := {f with locals := ((∅ : Store).insert "lpFee" (.int (Int.ofNat fee.toNat))).insert "self" (poolRefValue id)})
    (evm := evm) hf (store_get_self _ _ _)
    ((store_get_ne _ _ (by decide : ("self" == "lpFee") = false)).trans (store_get_self _ _ _)) hc
  have hcall := internalCallFunctionExec (caller := f) (name := "Pool_setLPFee") (retVar := retVar)
    (args := [ep, ef]) (argVals := [poolRefValue id, .int (Int.ofNat fee.toNat)])
    (by simp only [evalExprs?, hp, he, bind, EvalResult.bind, pure])
    (by rw [hf]; exact poolSetFee_lookup) (by rfl) hb
  simpa only [poolSetFeeCallResult, poolSetFeeResult, resumeCallResult_ite,
    resumeCallResult_reverted, resumeCallResult_static, resumeCallResult_returned] using hcall

end Benchmarks.UniswapV4PoolManager
