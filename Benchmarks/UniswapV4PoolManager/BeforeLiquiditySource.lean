import Benchmarks.UniswapV4PoolManager.LiquidityHookSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

abbrev beforeLiquidityFunction : FunctionDecl := contract.functions[35]!
def beforeLiquidityFlag (add : Bool) : UInt256 := if add then ⟨2048⟩ else ⟨512⟩
def beforeLiquidityEnabled (hook : AccountAddress) (p : ModifyLiquidityWords) (add : Bool) : Prop :=
  (if add then 0 < EVM.signed p.delta else EVM.signed p.delta ≤ 0) ∧
    UInt256.land (accountWord hook) (beforeLiquidityFlag add) ≠ ⟨0⟩
instance (hook : AccountAddress) (p : ModifyLiquidityWords) (add : Bool) :
    Decidable (beforeLiquidityEnabled hook p add) := inferInstanceAs (Decidable (_ ∧ _))
def beforeLiquidityCondition (add : Bool) : Expr :=
  .binary .and (.binary (if add then .gt else .le) (.field (.var "params") "liquidityDelta") (.intLit 0))
    (hookPermissionExpr (.var "self") (beforeLiquidityFlag add))
def beforeLiquidityPayloadExpr (add : Bool) : Expr :=
  liquidityHookPayloadExpr false add (.env .caller) (.var "key") (.var "params") (.intLit 0) (.intLit 0) (.var "hookData")
def beforeLiquidityPayload (add : Bool) (sender : AccountAddress) (key : PoolKeyWords)
    (p : ModifyLiquidityWords) (data : ByteArray) : ByteArray :=
  liquidityHookPayload false add sender key p ⟨0⟩ ⟨0⟩ data
def beforeLiquidityBranch (add : Bool) : List Stmt :=
  [.letDecl "payload" (some .bytes) (beforeLiquidityPayloadExpr add),
   .internalCall "Hooks_callHook" [.var "self", .var "payload"] "ignored"]

theorem beforeLiquidityCondition_eval {f : Frame} {evm : State} {hook : AccountAddress} {p : ModifyLiquidityWords}
    (hs : f.locals.get? "self" = some (.address hook))
    (hp : f.locals.get? "params" = some (modifyLiquidityParamsValue p)) (add : Bool) :
    evalExpr? config f evm (beforeLiquidityCondition add) =
      .ok (.bool (decide (beforeLiquidityEnabled hook p add))) := by
  have hd := evalStructField (evalLocalValue (cfg := config) (evm := evm) hp) (field := "liquidityDelta") rfl
  have he : evalExpr? config f evm
      (.binary (if add then .gt else .le) (.field (.var "params") "liquidityDelta") (.intLit 0)) =
      .ok (.bool (decide (if add then 0 < EVM.signed p.delta else EVM.signed p.delta ≤ 0))) := by
    cases add <;> simp only [Bool.false_eq_true, if_false, if_true, evalExpr?, hd, evalBinaryOp?,
      bind, EvalResult.bind, pure]
  have hb := hookPermission_eval (evalLocalValue (cfg := config) (evm := evm) hs)
    (beforeLiquidityFlag add) (by cases add <;> decide)
  simpa only [beforeLiquidityEnabled, Bool.decide_and] using evalAndBool he hb

def beforeLiquidityTailResult (f : Frame) (evm post : State) (hook : AccountAddress)
    (key : PoolKeyWords) (p : ModifyLiquidityWords) (data : ByteArray) (z : Bool) (out : ByteArray) : ExecResult :=
  if beforeLiquidityEnabled hook p true then
    hookPayloadResult f post z (beforeLiquidityPayload true evm.executionEnv.source key p data) out
  else if beforeLiquidityEnabled hook p false then
    hookPayloadResult f post z (beforeLiquidityPayload false evm.executionEnv.source key p data) out
  else .ok f evm
def beforeLiquidityBlockResult (f : Frame) (evm post : State) (hook : AccountAddress)
    (key : PoolKeyWords) (p : ModifyLiquidityWords) (data : ByteArray) (z : Bool) (out : ByteArray) : ExecResult :=
  if evm.executionEnv.source = hook then .returned f evm (some [])
  else beforeLiquidityTailResult f evm post hook key p data z out
def beforeLiquidityResult (f : Frame) (evm post : State) (hook : AccountAddress)
    (key : PoolKeyWords) (p : ModifyLiquidityWords) (data : ByteArray) (z : Bool) (out : ByteArray) : ExecResult :=
  finishBlockResult (beforeLiquidityBlockResult f evm post hook key p data z out)

theorem beforeLiquidityBody {f : Frame} {evm post : State} {hook : AccountAddress}
    {key : PoolKeyWords} {p : ModifyLiquidityWords} {data out : ByteArray} {z : Bool}
    (hf : f.contract = contract) (hs : f.locals.get? "self" = some (.address hook))
    (hk : f.locals.get? "key" = some (poolKeyValue key))
    (hp : f.locals.get? "params" = some (modifyLiquidityParamsValue p))
    (hd : f.locals.get? "hookData" = some (.bytes data))
    (hc : PoolKeyCanonical key) (hl : int24Canonical p.lower) (hu : int24Canonical p.upper)
    (hcall : ∀ add, evm.executionEnv.source ≠ hook → beforeLiquidityEnabled hook p add →
      callViaEVM evm hook 0 (beforeLiquidityPayload add evm.executionEnv.source key p data) (z, post, out)) :
    ExecFuncBody config f evm beforeLiquidityFunction.body
      (beforeLiquidityResult f evm post hook key p data z out) := by
  have hsender : evalExpr? config f evm (.env .caller) = .ok (.address evm.executionEnv.source) := by
    simp only [evalExpr?, envValue, pure]
  have heq := evalEqAddress hsender (evalLocalValue hs)
  apply execFuncBody_block
  by_cases hself : evm.executionEnv.source = hook
  · rw [beforeLiquidityBlockResult, if_pos hself]
    exact ExecBlock.consReturn (ExecStmt.iteTrue (heq.trans (by rw [decide_eq_true hself]))
      (ExecBlock.consReturn (ExecStmt.return rfl)))
  · rw [beforeLiquidityBlockResult, if_neg hself]
    have hg : ExecStmt config f evm beforeLiquidityFunction.body[0]! (.ok f evm) :=
      ExecStmt.iteFalse (heq.trans (by rw [decide_eq_false hself])) ExecBlock.nil
    have hb (add : Bool) (ha : beforeLiquidityEnabled hook p add) :
        ExecBlock config f evm (beforeLiquidityBranch add)
          (hookPayloadResult f post z (beforeLiquidityPayload add evm.executionEnv.source key p data) out) := by
      apply hookPayloadBlock hf hs (liquidityHookPayload_eval false add hsender
        (evalLocalValue hk) (evalLocalValue hp)
        (show evalExpr? config f evm (.intLit 0) = .ok (.int (EVM.signed (⟨0⟩ : UInt256))) by simp only [evalExpr?, pure]; rfl)
        (show evalExpr? config f evm (.intLit 0) = .ok (.int (EVM.signed (⟨0⟩ : UInt256))) by simp only [evalExpr?, pure]; rfl)
        (evalLocalValue hd) hc hl hu)
      · rw [liquidityHookPayload_size]
        change 4 ≤ 388 + paddedSize data.size
        omega
      · exact hcall add hself ha
    have ha := beforeLiquidityCondition_eval (evm := evm) hs hp true
    have hr := beforeLiquidityCondition_eval (evm := evm) hs hp false
    rw [beforeLiquidityTailResult]
    by_cases hadd : beforeLiquidityEnabled hook p true
    · rw [if_pos hadd]
      exact ExecBlock.consNormal hg (execBlock_singleton
        (ExecStmt.iteTrue (ha.trans (by rw [decide_eq_true hadd])) (hb true hadd)))
    · rw [if_neg hadd]
      by_cases hremove : beforeLiquidityEnabled hook p false
      · rw [if_pos hremove]
        exact ExecBlock.consNormal hg (execBlock_singleton
          (ExecStmt.iteFalse (ha.trans (by rw [decide_eq_false hadd]))
            (execBlock_singleton (ExecStmt.iteTrue (hr.trans (by rw [decide_eq_true hremove])) (hb false hremove)))))
      · rw [if_neg hremove]
        exact ExecBlock.consNormal hg (execBlock_singleton
          (ExecStmt.iteFalse (ha.trans (by rw [decide_eq_false hadd]))
            (execBlock_singleton (ExecStmt.iteFalse (hr.trans (by rw [decide_eq_false hremove])) ExecBlock.nil))))

end Benchmarks.UniswapV4PoolManager
