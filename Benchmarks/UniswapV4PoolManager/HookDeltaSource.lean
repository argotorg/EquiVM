import Benchmarks.UniswapV4PoolManager.HookCallSource
import Benchmarks.UniswapV4PoolManager.SignedBytesDecode

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

abbrev hookDeltaFunction : FunctionDecl := contract.functions[32]!
theorem hookDelta_lookup : lookupCallable? contract "Hooks_callHookWithReturnDelta" =
    some hookDeltaFunction.toCallable := rfl

def hookDeltaWord (out : ByteArray) (parse : Bool) : UInt256 :=
  if parse then calldataWord out 32 else ⟨0⟩
def hookDeltaReplyResult (f : Frame) (evm : State) (out : ByteArray) (parse : Bool) : ExecResult :=
  if parse = true ∧ out.size ≠ 64 then .reverted
  else .returned f evm (some [.int (EVM.signed (hookDeltaWord out parse))])
def hookDeltaResult (f : Frame) (evm : State) (z : Bool) (data out : ByteArray) (parse : Bool) : ExecResult :=
  if z = true ∧ hookReplyValid data out then
    hookDeltaReplyResult {f with locals := f.locals.insert "result" (.bytes out)} evm out parse
  else .reverted

def hookDeltaInvocationResult (f : Frame) (ret : Ident) (evm : State) (z : Bool)
    (data out : ByteArray) (parse : Bool) : ExecResult :=
  if z = true ∧ hookReplyValid data out then
    if parse = true ∧ out.size ≠ 64 then .reverted
    else .ok {f with locals := f.locals.insert ret (.int (EVM.signed (hookDeltaWord out parse)))} evm
  else .reverted

theorem hookDelta_resume (f cf : Frame) (ret : Ident) (evm : State) (z : Bool)
    (data out : ByteArray) (parse : Bool) :
    resumeCallResult f ret (hookDeltaResult cf evm z data out parse) =
      hookDeltaInvocationResult f ret evm z data out parse := by
  simp only [hookDeltaResult, hookDeltaReplyResult, resumeCallResult_ite, resumeCallResult_returned,
    resumeCallResult_reverted, hookDeltaInvocationResult]
  split_ifs <;> rfl

theorem hookDeltaReply {f : Frame} {evm : State} {out : ByteArray} {parse : Bool}
    (hp : f.locals.get? "parseReturn" = some (.bool parse))
    (ho : f.locals.get? "result" = some (.bytes out)) :
    ExecFuncBody config f evm (hookDeltaFunction.body.drop 1) (hookDeltaReplyResult f evm out parse) := by
  have he := evalNotBool (evalLocalValue (cfg := config) (evm := evm) hp)
  cases parse with
  | false =>
    simp only [hookDeltaReplyResult, Bool.false_eq_true, false_and, if_false, hookDeltaWord]
    exact .execBlockRet (ExecBlock.consReturn (ExecStmt.iteTrue he
      (ABlock.start.returns (by simp only [evalExpr?, pure]; rfl))))
  | true =>
    simp only [hookDeltaReplyResult, true_and]
    have hg : ExecStmt config f evm hookDeltaFunction.body[1]! (.ok f evm) :=
      ExecStmt.iteFalse he ExecBlock.nil
    have hlen := evalNatEqLiteral (k := 64) (evalLocalBytesLength (cfg := config) (evm := evm) ho)
    by_cases hl : out.size = 64
    · rw [if_neg (not_not.mpr hl)]
      exact .execBlockRet (ExecBlock.consNormal hg
        (ExecBlock.consNormal (ExecStmt.requireTrue (hlen.trans (by rw [decide_eq_true hl])))
          (ABlock.start.returns (evalDecodeSigned256Slice (start := 32) rfl (evalLocalValue ho) (by omega)))))
    · rw [if_pos hl]
      exact .execBlockRevert (ExecBlock.consNormal hg
        (ExecBlock.consRevert (ExecStmt.requireFalse (hlen.trans (by rw [decide_eq_false hl])))))

theorem hookDeltaBody {f : Frame} {evm post : State} {hook : AccountAddress}
    {z parse : Bool} {data out : ByteArray} (hf : f.contract = contract)
    (hs : f.locals.get? "self" = some (.address hook))
    (hd : f.locals.get? "data" = some (.bytes data))
    (hp : f.locals.get? "parseReturn" = some (.bool parse)) (hlen : 4 ≤ data.size)
    (hcall : callViaEVM evm hook 0 data (z, post, out)) :
    ExecFuncBody config f evm hookDeltaFunction.body (hookDeltaResult f post z data out parse) := by
  have hc := hookCall hf (evalLocalValue hs) (evalLocalValue hd) hlen hcall "result"
  by_cases hv : z = true ∧ hookReplyValid data out
  · rw [if_pos hv] at hc
    rw [hookDeltaResult, if_pos hv]
    exact execFuncBody_prepend (execBlock_singleton hc)
      (hookDeltaReply ((store_get_ne _ _ (by decide)).trans hp) (store_get_self _ _ _))
  · rw [if_neg hv] at hc
    rw [hookDeltaResult, if_neg hv]
    exact .execBlockRevert (ExecBlock.consRevert hc)

theorem hookDeltaCall {f : Frame} {evm post : State} {hook : AccountAddress}
    {z parse : Bool} {data out : ByteArray} {es ed ep : Expr} (hf : f.contract = contract)
    (hs : evalExpr? config f evm es = .ok (.address hook))
    (hd : evalExpr? config f evm ed = .ok (.bytes data))
    (hp : evalExpr? config f evm ep = .ok (.bool parse)) (hlen : 4 ≤ data.size)
    (hcall : callViaEVM evm hook 0 data (z, post, out)) (ret : Ident) :
    ExecStmt config f evm (.internalCall "Hooks_callHookWithReturnDelta" [es, ed, ep] ret)
      (hookDeltaInvocationResult f ret post z data out parse) := by
  rw [← hookDelta_resume f
    {f with locals := (((∅ : Store).insert "parseReturn" (.bool parse)).insert "data" (.bytes data)).insert "self" (.address hook)}]
  apply internalCallFunctionExec (argVals := [.address hook, .bytes data, .bool parse])
    (by simp only [evalExprs?, hs, hd, hp, bind, EvalResult.bind, pure])
    (by rw [hf]; exact hookDelta_lookup) rfl
  exact hookDeltaBody hf (store_get_self _ _ _)
    ((store_get_ne _ _ (by decide)).trans (store_get_self _ _ _))
    ((store_get_ne _ _ (by decide)).trans ((store_get_ne _ _ (by decide)).trans (store_get_self _ _ _))) hlen hcall

end Benchmarks.UniswapV4PoolManager
