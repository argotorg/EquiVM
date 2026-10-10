import Benchmarks.UniswapV4PoolManager.PoolSwapBodyCorrect

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem poolSwap_lookup : lookupCallable? contract "Pool_swap" = some poolSwapFunction.toCallable := rfl

def poolSwapCallFrame (f : Frame) (id : UInt256) (p : PoolSwapParamsWords) : Frame :=
  {f with locals := ((∅ : Store).insert "params" (poolSwapParamsValue p)).insert "self" (poolRefValue id)}

theorem poolSwapCallCorrect {I : ExecutionEnv} {g : Sat256} {s0 evm : State} {f : Frame}
    {mem rdata : ByteArray} {aw id state params ret : UInt256} {p : PoolSwapParamsWords}
    {k C : Nat} {R : List UInt256} {es ep : Expr}
    (v : PoolManagerImmutables) (hstack : R.length+36 ≤ 1024) (hI : evm.executionEnv = I)
    (hσ0 : evm.σ₀ = s0.σ₀)
    (hf : f.contract = contract) (hs : evalExpr? config f evm es = .ok (poolRefValue id))
    (hp : evalExpr? config f evm ep = .ok (poolSwapParamsValue p))
    (hm : WordStructView mem params (poolSwapParamsWordList p))
    (hparams : 128 ≤ params.toNat) (hb : params.toNat+160 ≤ state.toNat)
    (hfit : state.toNat+352 ≤ solcMaxU64) (hfree : memLoad (UInt256.ofNat 64) mem = state)
    (hspacing : int24Canonical p.tickSpacing) (hlimit : p.priceLimit.toNat < 2^160)
    (hoverride : p.lpFeeOverride.toNat < 2^24) (hpaid : Cₘ aw ≤ C)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (dest : Ident)
    (h : RD (deployedRuntime v) I g s0 ⟨18777⟩
      ([poolSlot id, params, ret]++R) mem aw rdata evm.accountMap k C) :
    X (g.toNat+1) (D_J (deployedRuntime v) 0) s0 = .error .OutOfGass ∨
    ∃ result, ExecStmt config f evm (.internalCall "Pool_swap" [es, ep] dest) (resumeCallResult f dest result) ∧
      functionResultTrace (deployedRuntime v) g s0
        (poolSwapBodyReturn v I g s0 evm mem rdata id state params ret p R C) result := by
  rcases poolSwapBodyCorrect (f := poolSwapCallFrame f id p) v hstack hI hσ0 hf
      (store_get_self _ _ _) ((store_get_ne _ _ (by decide : ("self" == "params") = false)).trans (store_get_self _ _ _))
      hm hparams hb hfit hfree hspacing hlimit hoverride hpaid hret h with hog | ⟨result, hb, ht⟩
  · exact .inl hog
  · refine .inr ⟨result, ?_, ht⟩
    exact internalCallFunctionExec (caller := f) (name := "Pool_swap") (retVar := dest)
      (args := [es, ep]) (argVals := [poolRefValue id, poolSwapParamsValue p])
      (by simp only [evalExprs?, hs, hp, bind, EvalResult.bind, pure])
      (by rw [hf]; exact poolSwap_lookup) rfl hb

end Benchmarks.UniswapV4PoolManager
