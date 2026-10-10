import Benchmarks.UniswapV4PoolManager.HookCallSource
import Benchmarks.UniswapV4PoolManager.Slot0Source
import Benchmarks.UniswapV4PoolManager.TransientSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

def hookEnabled (sender hook : AccountAddress) (flag : UInt256) : Prop :=
  sender ≠ hook ∧ UInt256.land (accountWord hook) flag ≠ ⟨0⟩
instance (sender hook : AccountAddress) (flag : UInt256) : Decidable (hookEnabled sender hook flag) :=
  inferInstanceAs (Decidable (_ ∧ _))

def hookPermissionExpr (e : Expr) (flag : UInt256) : Expr :=
  .binary .ne (.binary (.bitAnd (.uint ⟨160, by decide⟩))
    (.cast e (.elem (.int (.uint ⟨160, by decide⟩))))
    (.intLit (Int.ofNat flag.toNat))) (.intLit 0)

theorem hookPermission_eval {f : Frame} {evm : EVM.State} {hook : AccountAddress} {e : Expr}
    (he : evalExpr? config f evm e = .ok (.address hook)) (flag : UInt256) (hflag : flag.toNat < 2^160) :
    evalExpr? config f evm (hookPermissionExpr e flag) =
      .ok (.bool (decide (UInt256.land (accountWord hook) flag ≠ ⟨0⟩))) := by
  have hbits := evalUintWordAnd ⟨160, by decide⟩ (accountWord_canonical hook) hflag
    (evalAddressUint160 he)
    (show evalExpr? config f evm (.intLit (Int.ofNat flag.toNat)) = .ok (.int (Int.ofNat flag.toNat)) by
      simp only [evalExpr?, pure])
  exact evalNeWords hbits
    (show evalExpr? config f evm (.intLit 0) = .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) by
      simp only [evalExpr?, pure]; rfl)

def hookEnabledExpr (flag : UInt256) : Expr :=
  .binary .and (.binary .ne (.env .caller) (.var "self")) (hookPermissionExpr (.var "self") flag)

theorem hookEnabled_eval {f : Frame} {evm : EVM.State} {hook : AccountAddress}
    (hs : f.locals.get? "self" = some (.address hook)) (flag : UInt256) (hflag : flag.toNat < 2^160) :
    evalExpr? config f evm (hookEnabledExpr flag) =
      .ok (.bool (decide (hookEnabled evm.executionEnv.source hook flag))) := by
  have hself := evalLocalValue (cfg := config) (evm := evm) hs
  have hcaller : evalExpr? config f evm (.env .caller) = .ok (.address evm.executionEnv.source) := by
    simp only [evalExpr?, envValue, pure]
  have hn := hookPermission_eval hself flag hflag
  simpa only [hookEnabled, Bool.decide_and] using evalAndBool (evalNeAddress hcaller hself) hn

def hookInvocationResult (f : Frame) (evm evm' : EVM.State) (enabled : Prop) [Decidable enabled]
    (z : Bool) (data out : ByteArray) : ExecResult :=
  if enabled then if z = true ∧ hookReplyValid data out then .returned f evm' none else .reverted
  else .returned f evm none

def hookPayloadFrame (f : Frame) (data out : ByteArray) : Frame :=
  {f with locals := (f.locals.insert "payload" (.bytes data)).insert "ignored" (.bytes out)}
def hookPayloadResult (f : Frame) (post : State) (z : Bool) (data out : ByteArray) : ExecResult :=
  if z = true ∧ hookReplyValid data out then .ok (hookPayloadFrame f data out) post else .reverted

theorem hookPayloadBlock {f : Frame} {evm post : State} {hook : AccountAddress}
    {payload : Expr} {data out : ByteArray} {z : Bool}
    (hf : f.contract = contract) (hs : f.locals.get? "self" = some (.address hook))
    (hp : evalExpr? config f evm payload = .ok (.bytes data)) (hlen : 4 ≤ data.size)
    (hcall : callViaEVM evm hook 0 data (z, post, out)) :
    ExecBlock config f evm [.letDecl "payload" (some .bytes) payload,
      .internalCall "Hooks_callHook" [.var "self", .var "payload"] "ignored"]
      (hookPayloadResult f post z data out) := by
  let f1 : Frame := {f with locals := f.locals.insert "payload" (.bytes data)}
  have hhook := hookCall (f := f1) hf
    (evalLocalValue ((store_get_ne _ _ (by decide : ("payload" == "self") = false)).trans hs))
    (evalLocalValue (store_get_self _ _ _)) hlen hcall "ignored"
  by_cases hv : z = true ∧ hookReplyValid data out
  · rw [if_pos hv] at hhook
    rw [hookPayloadResult, if_pos hv]
    exact ExecBlock.consNormal (ExecStmt.letDecl hp) (execBlock_singleton hhook)
  · rw [if_neg hv] at hhook
    rw [hookPayloadResult, if_neg hv]
    exact ExecBlock.consNormal (ExecStmt.letDecl hp) (ExecBlock.consRevert hhook)

-- The common conditional wrapper around a validated hook call.
theorem conditionalHookBody {f : Frame} {evm evm' : EVM.State} {hook : AccountAddress}
    {condition payload : Expr} {enabled : Prop} [Decidable enabled] {data out : ByteArray} {z : Bool}
    (hf : f.contract = contract) (hs : f.locals.get? "self" = some (.address hook))
    (hc : evalExpr? config f evm condition = .ok (.bool (decide enabled)))
    (hp : evalExpr? config f evm payload = .ok (.bytes data)) (hlen : 4 ≤ data.size)
    (hcall : enabled → callViaEVM evm hook 0 data (z, evm', out)) :
    ∃ f', ExecFuncBody config f evm
      [.ite condition [.letDecl "payload" (some .bytes) payload,
        .internalCall "Hooks_callHook" [.var "self", .var "payload"] "ignored"] []]
      (hookInvocationResult f' evm evm' enabled z data out) := by
  by_cases he : enabled
  · rw [decide_eq_true he] at hc
    refine ⟨hookPayloadFrame f data out, ?_⟩
    have hblock := hookPayloadBlock hf hs hp hlen (hcall he)
    by_cases hv : z = true ∧ hookReplyValid data out
    · simp only [hookPayloadResult, if_pos hv] at hblock
      simp only [hookInvocationResult, if_pos he, if_pos hv]
      exact .execBlockOK (execBlock_singleton (ExecStmt.iteTrue hc hblock))
    · simp only [hookPayloadResult, if_neg hv] at hblock
      simp only [hookInvocationResult, if_pos he, if_neg hv]
      exact .execBlockRevert (ExecBlock.consRevert (ExecStmt.iteTrue hc hblock))
  · refine ⟨f, ?_⟩
    simp only [hookInvocationResult, if_neg he]
    rw [decide_eq_false he] at hc
    exact .execBlockOK (execBlock_singleton (ExecStmt.iteFalse hc ExecBlock.nil))

end Benchmarks.UniswapV4PoolManager
