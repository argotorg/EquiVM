import Benchmarks.UniswapV4PoolManager.AfterSwapBranchSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def afterSwapSelectedUnspecified (hook : AccountAddress) (unspecified : Int) (out : ByteArray) : Int :=
  if afterSwapActive hook then unspecified+EVM.signed (hookDeltaWord out (afterSwapParse hook)) else unspecified
def afterSwapSelectedResult (f : Frame) (evm post : State) (hook : AccountAddress)
    (key : PoolKeyWords) (p : SwapParamsWords) (delta : UInt256) (unspecified : Int)
    (data : ByteArray) (z : Bool) (out : ByteArray) : ExecResult :=
  if afterSwapActive hook then afterSwapBranchResult f post unspecified z
    (afterSwapPayload evm.executionEnv.source key p delta data) out (afterSwapParse hook)
  else .ok f evm

theorem afterSwapSelectedSource {f : Frame} {evm post : State} {hook : AccountAddress}
    {key : PoolKeyWords} {p : SwapParamsWords} {delta : UInt256} {unspecified : Int}
    {data out : ByteArray} {z : Bool}
    (hf : f.contract = contract) (hs : f.locals.get? "self" = some (.address hook))
    (hk : f.locals.get? "key" = some (poolKeyValue key))
    (hp : f.locals.get? "params" = some (swapParamsValue p))
    (hd : f.locals.get? "swapDelta" = some (.int (EVM.signed delta)))
    (hb : f.locals.get? "hookData" = some (.bytes data))
    (hu : f.locals.get? "unspecified" = some (.int unspecified))
    (hc : PoolKeyCanonical key) (hl : p.priceLimit.toNat < 2^160)
    (hcall : afterSwapActive hook →
      callViaEVM evm hook 0 (afterSwapPayload evm.executionEnv.source key p delta data) (z, post, out)) :
    ExecStmt config f evm afterSwapFunction.body[3]!
      (afterSwapSelectedResult f evm post hook key p delta unspecified data z out) := by
  have hflag := hookPermission_eval (evalLocalValue (cfg := config) (evm := evm) hs) ⟨64⟩ (by decide)
  change evalExpr? config f evm _ = .ok (.bool (decide (afterSwapActive hook))) at hflag
  by_cases ha : afterSwapActive hook
  · rw [afterSwapSelectedResult, if_pos ha]
    exact ExecStmt.iteTrue (hflag.trans (by rw [decide_eq_true ha]))
      (afterSwapBranchSource hf hs hk hp hd hb hu hc hl (hcall ha))
  · rw [afterSwapSelectedResult, if_neg ha]
    exact ExecStmt.iteFalse (hflag.trans (by rw [decide_eq_false ha])) ExecBlock.nil

theorem afterSwapSelectedResult_normal {f f' : Frame} {evm post next : State} {hook : AccountAddress}
    {key : PoolKeyWords} {p : SwapParamsWords} {delta : UInt256} {unspecified : Int}
    {data out : ByteArray} {z : Bool}
    (hu : f.locals.get? "unspecified" = some (.int unspecified))
    (huc : signedFits ⟨128, by decide⟩ unspecified)
    (hr : afterSwapSelectedResult f evm post hook key p delta unspecified data z out = .ok f' next) :
    f'.contract = f.contract ∧ f'.locals.get? "params" = f.locals.get? "params" ∧
      f'.locals.get? "specified" = f.locals.get? "specified" ∧
      f'.locals.get? "swapDelta" = f.locals.get? "swapDelta" ∧
      f'.locals.get? "unspecified" = some (.int (afterSwapSelectedUnspecified hook unspecified out)) ∧
      signedFits ⟨128, by decide⟩ (afterSwapSelectedUnspecified hook unspecified out) := by
  by_cases ha : afterSwapActive hook
  · rw [afterSwapSelectedResult, if_pos ha] at hr
    obtain ⟨rfl, rfl, hfit⟩ := afterSwapBranchResult_normal hr
    rw [afterSwapSelectedUnspecified, if_pos ha]
    refine ⟨rfl, ?_, ?_, ?_, ?_, hfit⟩
    all_goals simp only [afterSwapUpdateFrame, afterSwapReplyFrame, valueLocal_get,
      beq_iff_eq, String.reduceEq, if_true, if_false]
  · rw [afterSwapSelectedResult, if_neg ha] at hr
    cases hr
    rw [afterSwapSelectedUnspecified, if_neg ha]
    exact ⟨rfl, rfl, rfl, rfl, hu, huc⟩

end Benchmarks.UniswapV4PoolManager
