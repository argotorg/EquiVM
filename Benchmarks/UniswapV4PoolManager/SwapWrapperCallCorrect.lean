import Benchmarks.UniswapV4PoolManager.SwapWrapperBodyCorrect

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem swapWrapper_lookup : lookupCallable? contract "_swap" = some swapWrapperFunction.toCallable := rfl

def swapWrapperCallFrame (f : Frame) (id : UInt256) (p : PoolSwapParamsWords) (currency : AccountAddress) : Frame :=
  {f with locals := ((((∅ : Store).insert "inputCurrency" (.address currency)).insert "params"
    (poolSwapParamsValue p)).insert "id" (wordBytes32Value id)).insert "pool" (poolRefValue id)}

theorem swapWrapperCallCorrect {I : ExecutionEnv} {g : Sat256} {s0 evm : State} {f : Frame}
    {mem rdata : ByteArray} {aw id state params callerParams x8 x9 x10 x11 x12 x13 hookPtr junk : UInt256}
    {p : PoolSwapParamsWords} {currency : AccountAddress} {R : List UInt256} {k C : Nat}
    {es ei ep ec : Expr} (v : PoolManagerImmutables) (hstack : R.length+49 ≤ 1024)
    (hI : evm.executionEnv = I) (hσ0 : evm.σ₀ = s0.σ₀) (hf : f.contract = contract)
    (hs : evalExpr? config f evm es = .ok (poolRefValue id))
    (hi : evalExpr? config f evm ei = .ok (wordBytes32Value id))
    (hp : evalExpr? config f evm ep = .ok (poolSwapParamsValue p))
    (hc : evalExpr? config f evm ec = .ok (.address currency))
    (hm : WordStructView mem params (poolSwapParamsWordList p)) (hparams : 128 ≤ params.toNat)
    (hb : params.toNat+160 ≤ state.toNat) (hfit : state.toNat+352 ≤ solcMaxU64)
    (hfree : memLoad (UInt256.ofNat 64) mem = state) (hspacing : int24Canonical p.tickSpacing)
    (hlimit : p.priceLimit.toNat < 2^160) (hoverride : p.lpFeeOverride.toNat < 2^24)
    (hpaid : Cₘ aw ≤ C) (dest : Ident)
    (h : RD (deployedRuntime v) I g s0 ⟨18777⟩
      ([poolSlot id, params, ⟨1755⟩, id, UInt256.ofNat 16777215, callerParams, accountWord currency,
        x8, x9, x10, x11, x12, x13, hookPtr, UInt256.ofNat 32, junk]++R)
      mem aw rdata evm.accountMap k C) :
    X (g.toNat+1) (D_J (deployedRuntime v) 0) s0 = .error .OutOfGass ∨
    ∃ result, ExecStmt config f evm (.internalCall "_swap" [es, ei, ep, ec] dest) (resumeCallResult f dest result) ∧
      functionResultTrace (deployedRuntime v) g s0
        (swapWrapperReturn v I g s0 mem rdata state callerParams x8 x9 x10 x11 x12 x13 hookPtr junk R) result := by
  rcases swapWrapperBodyCorrect (f := swapWrapperCallFrame f id p currency) v hstack hI hσ0 hf
      (store_get_self _ _ _)
      ((store_get_ne _ _ (by decide : ("pool" == "id") = false)).trans (store_get_self _ _ _))
      ((store_get_ne2 _ _ _ (by decide : ("id" == "params") = false)
        (by decide : ("pool" == "params") = false)).trans (store_get_self _ _ _))
      ((store_get_ne3 _ _ _ _ (by decide : ("params" == "inputCurrency") = false)
        (by decide : ("id" == "inputCurrency") = false)
        (by decide : ("pool" == "inputCurrency") = false)).trans (store_get_self _ _ _))
      hm hparams hb hfit hfree hspacing hlimit hoverride hpaid h with hog | ⟨result, hbody, htrace⟩
  · exact .inl hog
  · refine .inr ⟨result, ?_, htrace⟩
    exact internalCallFunctionExec (caller := f) (name := "_swap") (retVar := dest)
      (args := [es, ei, ep, ec])
      (argVals := [poolRefValue id, wordBytes32Value id, poolSwapParamsValue p, .address currency])
      (by simp only [evalExprs?, hs, hi, hp, hc, bind, EvalResult.bind, pure])
      (by rw [hf]; exact swapWrapper_lookup) rfl hbody

end Benchmarks.UniswapV4PoolManager
