import Benchmarks.UniswapV4PoolManager.LocalBytes
import Benchmarks.UniswapV4PoolManager.CallComposition
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

abbrev hookCallFunction : FunctionDecl := contract.functions[31]!
theorem hookCall_lookup : lookupCallable? contract "Hooks_callHook" = some hookCallFunction.toCallable := rfl

def hookReplyValid (data out : ByteArray) : Prop := 32 ≤ out.size ∧ out.extract 0 4 = data.extract 0 4
instance (data out : ByteArray) : Decidable (hookReplyValid data out) := inferInstanceAs (Decidable (_ ∧ _))
def hookCallResult (f : Frame) (evm : EVM.State) (z : Bool) (data out : ByteArray) : ExecResult :=
  if z = true ∧ hookReplyValid data out then .returned f evm (some [.bytes out]) else .reverted

theorem hookReplySource {f : Frame} {evm : EVM.State} {z : Bool} {data out : ByteArray}
    (hs : f.locals.get? "success" = some (.bool z))
    (hr : f.locals.get? "result" = some (.bytes out))
    (hd : f.locals.get? "data" = some (.bytes data)) (hlen : 4 ≤ data.size) :
    ExecFuncBody config f evm (hookCallFunction.body.drop 1) (hookCallResult f evm z data out) := by
  have hsuccess := evalLocalValue (cfg := config) (evm := evm) hs
  have hsize := evalNatGeLiteral (cfg := config) (evm := evm) (k := 32) (evalLocalBytesLength hr)
  cases z with
  | false =>
    simp only [hookCallResult, Bool.false_eq_true, false_and, if_false]
    exact .execBlockRevert (ExecBlock.consRevert (ExecStmt.requireFalse hsuccess))
  | true =>
    simp only [hookCallResult, true_and]
    by_cases hlong : 32 ≤ out.size
    · rw [decide_eq_true hlong] at hsize
      have heq := evalEqBytes (evalBytesPrefix (cfg := config) (evm := evm) (n := 4) (evalLocalValue hr) (by omega))
        (evalBytesPrefix (cfg := config) (evm := evm) (n := 4) (evalLocalValue hd) hlen)
      by_cases hsel : out.extract 0 4 = data.extract 0 4
      · simp only [hookReplyValid, hlong, hsel, true_and, if_true]
        rw [decide_eq_true hsel] at heq
        exact .execBlockRet (ExecBlock.consNormal (ExecStmt.requireTrue hsuccess)
          (ExecBlock.consNormal (ExecStmt.requireTrue hsize)
          (ExecBlock.consNormal (ExecStmt.requireTrue heq) (ABlock.start.returns (evalLocalValue hr)))))
      · simp only [hookReplyValid, hlong, hsel, true_and, if_false]
        rw [decide_eq_false hsel] at heq
        exact .execBlockRevert (ExecBlock.consNormal (ExecStmt.requireTrue hsuccess)
          (ExecBlock.consNormal (ExecStmt.requireTrue hsize) (ExecBlock.consRevert (ExecStmt.requireFalse heq))))
    · simp only [hookReplyValid, hlong, false_and, if_false]
      rw [decide_eq_false hlong] at hsize
      exact .execBlockRevert (ExecBlock.consNormal (ExecStmt.requireTrue hsuccess)
        (ExecBlock.consRevert (ExecStmt.requireFalse hsize)))

theorem hookCallBody {f : Frame} {evm evm' : EVM.State} {hook : AccountAddress} {z : Bool} {data out : ByteArray}
    (hs : f.locals.get? "self" = some (.address hook))
    (hd : f.locals.get? "data" = some (.bytes data)) (hlen : 4 ≤ data.size)
    (hcall : callViaEVM evm hook 0 data (z, evm', out)) :
    ExecFuncBody config f evm hookCallFunction.body
      (hookCallResult {f with locals := (f.locals.insert "success" (.bool z)).insert "result" (.bytes out)} evm' z data out) := by
  let f1 : Frame := {f with locals := (f.locals.insert "success" (.bool z)).insert "result" (.bytes out)}
  have hlow : ExecStmt config f evm hookCallFunction.body[0]! (.ok f1 evm') :=
    lowLevelCallSource (evalLocalValue hs) (by simp only [evalExpr?, pure]) (evalLocalValue hd) hcall
  have hrest := hookReplySource (f := f1) (evm := evm')
    ((store_get_ne _ _ (by decide : ("result" == "success") = false)).trans (store_get_self _ _ _))
    (store_get_self _ _ _)
    ((store_get_ne2 _ _ _ (by decide : ("success" == "data") = false)
      (by decide : ("result" == "data") = false)).trans hd) hlen
  exact execFuncBody_prepend (execBlock_singleton hlow) hrest

theorem hookCall {f : Frame} {evm evm' : EVM.State} {es ed : Expr} {hook : AccountAddress} {z : Bool} {data out : ByteArray}
    (hf : f.contract = contract) (hs : evalExpr? config f evm es = .ok (.address hook))
    (hd : evalExpr? config f evm ed = .ok (.bytes data)) (hlen : 4 ≤ data.size)
    (hcall : callViaEVM evm hook 0 data (z, evm', out)) (retVar : Ident) :
    ExecStmt config f evm (.internalCall "Hooks_callHook" [es, ed] retVar)
      (if z = true ∧ hookReplyValid data out then
        .ok {f with locals := f.locals.insert retVar (.bytes out)} evm' else .reverted) := by
  have hb := hookCallBody (f := {f with locals := ((∅ : Store).insert "data" (.bytes data)).insert "self" (.address hook)})
    (evm := evm) (store_get_self _ _ _)
    ((store_get_ne _ _ (by decide : ("self" == "data") = false)).trans (store_get_self _ _ _)) hlen hcall
  have hl : lookupCallable? f.contract "Hooks_callHook" = some hookCallFunction.toCallable := by
    rw [hf]; exact hookCall_lookup
  have hargs : evalExprs? config f evm [es, ed] = .ok [.address hook, .bytes data] := by
    simp only [evalExprs?, hs, hd, bind, EvalResult.bind, pure]
  by_cases hv : z = true ∧ hookReplyValid data out
  · simp only [hookCallResult, if_pos hv] at hb ⊢
    exact internalCallFunctionReturn hargs hl rfl hb
  · simp only [hookCallResult, if_neg hv] at hb ⊢
    exact internalCallFunctionRevert hargs hl rfl hb

end Benchmarks.UniswapV4PoolManager
