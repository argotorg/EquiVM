import Benchmarks.UniswapV4PoolManager.AfterLiquidityBranchSource
import Benchmarks.UniswapV4PoolManager.BlockContinuation

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def afterLiquidityAdd (p : ModifyLiquidityWords) : Bool := decide (0 < EVM.signed p.delta)
def afterLiquidityActive (hook : AccountAddress) (p : ModifyLiquidityWords) : Prop :=
  UInt256.land (accountWord hook) (afterLiquidityFlag (afterLiquidityAdd p)) ≠ ⟨0⟩
instance (hook : AccountAddress) (p : ModifyLiquidityWords) : Decidable (afterLiquidityActive hook p) :=
  inferInstanceAs (Decidable (_ ≠ _))
def afterLiquiditySelectedStmt : Stmt :=
  .ite (.binary .gt (.field (.var "params") "liquidityDelta") (.intLit 0))
    [.ite (hookPermissionExpr (.var "self") (afterLiquidityFlag true)) (afterLiquidityBranch true) []]
    [.ite (hookPermissionExpr (.var "self") (afterLiquidityFlag false)) (afterLiquidityBranch false) []]
def afterLiquiditySelectedResult (f : Frame) (evm post : State) (hook : AccountAddress) (key : PoolKeyWords)
    (p : ModifyLiquidityWords) (delta fees : UInt256) (data : ByteArray) (z : Bool) (out : ByteArray) : ExecResult :=
  if afterLiquidityActive hook p then
    afterLiquidityBranchResult f post delta z
      (afterLiquidityPayload (afterLiquidityAdd p) evm.executionEnv.source key p delta fees data)
      out (afterLiquidityParse hook (afterLiquidityAdd p))
  else .ok f evm
def afterLiquidityReturnedHook (hook : AccountAddress) (p : ModifyLiquidityWords) (out : ByteArray) : UInt256 :=
  if afterLiquidityActive hook p then hookDeltaWord out (afterLiquidityParse hook (afterLiquidityAdd p)) else ⟨0⟩
def afterLiquidityReturnedCaller (hook : AccountAddress) (p : ModifyLiquidityWords) (delta : UInt256) (out : ByteArray) : UInt256 :=
  if afterLiquidityActive hook p then balanceDeltaCombineWord true delta
    (hookDeltaWord out (afterLiquidityParse hook (afterLiquidityAdd p))) else delta
def afterLiquidityReturnResult (f : Frame) (evm : State) (hook : AccountAddress) (p : ModifyLiquidityWords)
    (delta : UInt256) (out : ByteArray) : ExecResult :=
  .returned f evm (some [.int (EVM.signed (afterLiquidityReturnedCaller hook p delta out)),
    .int (EVM.signed (afterLiquidityReturnedHook hook p out))])

theorem afterLiquiditySelectedBody {f : Frame} {evm post : State} {hook : AccountAddress}
    {key : PoolKeyWords} {p : ModifyLiquidityWords} {delta fees : UInt256} {data out : ByteArray}
    {z : Bool} {old : Value}
    (hf : f.contract = contract) (hs : f.locals.get? "self" = some (.address hook))
    (hk : f.locals.get? "key" = some (poolKeyValue key))
    (hp : f.locals.get? "params" = some (modifyLiquidityParamsValue p))
    (hd : f.locals.get? "delta" = some (.int (EVM.signed delta)))
    (he : f.locals.get? "feesAccrued" = some (.int (EVM.signed fees)))
    (hb : f.locals.get? "hookData" = some (.bytes data))
    (hcaller : f.locals.get? "callerDelta" = some (.int (EVM.signed delta)))
    (hhook : f.locals.get? "hookDelta" = some old)
    (hc : PoolKeyCanonical key) (hl : int24Canonical p.lower) (hu : int24Canonical p.upper)
    (hcall : afterLiquidityActive hook p → callViaEVM evm hook 0
      (afterLiquidityPayload (afterLiquidityAdd p) evm.executionEnv.source key p delta fees data) (z, post, out)) :
    ExecStmt config f evm afterLiquiditySelectedStmt
      (afterLiquiditySelectedResult f evm post hook key p delta fees data z out) := by
  have hdelta := evalStructField (evalLocalValue (cfg := config) (evm := evm) hp) (field := "liquidityDelta") rfl
  have hpos : evalExpr? config f evm
      (.binary .gt (.field (.var "params") "liquidityDelta") (.intLit 0)) = .ok (.bool (afterLiquidityAdd p)) := by
    simp only [evalExpr?, hdelta, evalBinaryOp?, bind, EvalResult.bind, pure]
    rfl
  have hflag := hookPermission_eval (evalLocalValue (cfg := config) (evm := evm) hs)
    (afterLiquidityFlag (afterLiquidityAdd p)) (by cases afterLiquidityAdd p <;> decide)
  change evalExpr? config f evm _ = .ok (.bool (decide (afterLiquidityActive hook p))) at hflag
  have hbranch : ExecStmt config f evm
      (.ite (hookPermissionExpr (.var "self") (afterLiquidityFlag (afterLiquidityAdd p)))
        (afterLiquidityBranch (afterLiquidityAdd p)) [])
      (afterLiquiditySelectedResult f evm post hook key p delta fees data z out) := by
    by_cases ha : afterLiquidityActive hook p
    · rw [afterLiquiditySelectedResult, if_pos ha]
      exact ExecStmt.iteTrue (hflag.trans (by rw [decide_eq_true ha]))
        (afterLiquidityBranchBody (afterLiquidityAdd p) hf hs hk hp hd he hb hcaller hhook hc hl hu (hcall ha))
    · rw [afterLiquiditySelectedResult, if_neg ha]
      exact ExecStmt.iteFalse (hflag.trans (by rw [decide_eq_false ha])) ExecBlock.nil
  cases had : afterLiquidityAdd p with
  | false =>
    rw [had] at hpos hbranch
    exact ExecStmt.iteFalse hpos (execBlock_singleton hbranch)
  | true =>
    rw [had] at hpos hbranch
    exact ExecStmt.iteTrue hpos (execBlock_singleton hbranch)

theorem afterLiquiditySelectedReturn {f f' : Frame} {evm post next : State} {hook : AccountAddress}
    {key : PoolKeyWords} {p : ModifyLiquidityWords} {delta fees : UInt256} {data out : ByteArray} {z : Bool}
    (hd : f.locals.get? "callerDelta" = some (.int (EVM.signed delta)))
    (hh : f.locals.get? "hookDelta" = some (.int 0))
    (hr : afterLiquiditySelectedResult f evm post hook key p delta fees data z out = .ok f' next) :
    ExecBlock config f' next [.return [.var "callerDelta", .var "hookDelta"]]
      (afterLiquidityReturnResult f' next hook p delta out) := by
  by_cases ha : afterLiquidityActive hook p
  · rw [afterLiquiditySelectedResult, if_pos ha, afterLiquidityBranchResult] at hr
    split_ifs at hr with hv hbad
    rw [afterLiquidityFinishResult] at hr
    split_ifs at hr with hfit
    cases hr
    have hc : evalExpr? config (afterLiquidityFinishFrame
        (afterLiquidityReplyFrame f (afterLiquidityPayload (afterLiquidityAdd p) evm.executionEnv.source key p delta fees data)
          out (afterLiquidityParse hook (afterLiquidityAdd p))) delta
        (hookDeltaWord out (afterLiquidityParse hook (afterLiquidityAdd p)))) post (.var "callerDelta") =
        .ok (.int (EVM.signed (afterLiquidityReturnedCaller hook p delta out))) := by
      rw [afterLiquidityReturnedCaller, if_pos ha]
      exact evalLocalValue (store_get_self _ _ _)
    have hh' : evalExpr? config (afterLiquidityFinishFrame
        (afterLiquidityReplyFrame f (afterLiquidityPayload (afterLiquidityAdd p) evm.executionEnv.source key p delta fees data)
          out (afterLiquidityParse hook (afterLiquidityAdd p))) delta
        (hookDeltaWord out (afterLiquidityParse hook (afterLiquidityAdd p)))) post (.var "hookDelta") =
        .ok (.int (EVM.signed (afterLiquidityReturnedHook hook p out))) := by
      rw [afterLiquidityReturnedHook, if_pos ha]
      exact evalLocalValue ((store_get_ne _ _ (by decide : ("callerDelta" == "hookDelta") = false)).trans
        ((store_get_ne _ _ (by decide : ("remaining" == "hookDelta") = false)).trans (store_get_self _ _ _)))
    exact ExecBlock.consReturn (ExecStmt.return (by simp only [evalExprs?, hc, hh', bind, EvalResult.bind, pure]))
  · rw [afterLiquiditySelectedResult, if_neg ha] at hr
    cases hr
    have hc := evalLocalValue (cfg := config) (evm := evm) hd
    have hh' := evalLocalValue (cfg := config) (evm := evm) hh
    simp only [afterLiquidityReturnResult, afterLiquidityReturnedCaller, afterLiquidityReturnedHook, if_neg ha]
    exact ExecBlock.consReturn (ExecStmt.return (by simp only [evalExprs?, hc, hh', bind, EvalResult.bind, pure]; rfl))

end Benchmarks.UniswapV4PoolManager
