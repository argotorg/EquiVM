import Benchmarks.UniswapV4PoolManager.BeforeSwapBodyCorrect
import Benchmarks.UniswapV4PoolManager.BeforeSwapCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem beforeSwapCallCorrect {I : ExecutionEnv} {g : Sat256} {s0 evm : State} {f : Frame}
    {mem rdata : ByteArray} {aw free keyPtr paramsPtr src len ret : UInt256} {hook : AccountAddress}
    {k C : Nat} {R : List UInt256} {key : PoolKeyWords} {p : SwapParamsWords} {es ek ep ed : Expr}
    (v : PoolManagerImmutables) (hstack : R.length+24 ≤ 1024)
    (hI : evm.executionEnv = I) (hσ0 : evm.σ₀ = s0.σ₀) (hc : f.contract = contract)
    (hs : evalExpr? config f evm es = .ok (.address hook))
    (hk : evalExpr? config f evm ek = .ok (poolKeyValue key))
    (hp : evalExpr? config f evm ep = .ok (swapParamsValue p))
    (hd : evalExpr? config f evm ed = .ok (.bytes (I.calldata.extract src.toNat (src.toNat+len.toNat))))
    (hkey : PoolKeyView mem keyPtr key)
    (hparams : MemorySlice mem paramsPtr.toNat (wordBytes (swapParamsWordList p)))
    (hcanonical : PoolKeyCanonical key) (hlimit : p.priceLimit.toNat < 2^160)
    (hkb : keyPtr.toNat+160 ≤ free.toNat) (hpb : paramsPtr.toNat+96 ≤ free.toNat)
    (hklo : 96 ≤ keyPtr.toNat) (hf : free.toNat+len.toNat+480 < UInt256.size)
    (hroom : free.toNat+4000 ≤ solcMaxU64) (hsrc : src.toNat+len.toNat ≤ I.calldata.size)
    (hgas : g.toNat < 324518553658429321982441292826060) (hpaid : Cₘ aw ≤ C+63)
    (hfree : memLoad (UInt256.ofNat 64) mem = free)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (dest : Ident)
    (h : RD (deployedRuntime v) I g s0 ⟨15172⟩
      (accountWord hook :: keyPtr :: paramsPtr :: src :: len :: ret :: R) mem aw rdata evm.accountMap k C) :
    X (g.toNat+1) (D_J (deployedRuntime v) 0) s0 = .error .OutOfGass ∨
    ∃ result, ExecStmt config f evm (.internalCall "Hooks_beforeSwap" [es, ek, ep, ed] dest)
        (resumeCallResult f dest result) ∧
      functionResultTrace (deployedRuntime v) g s0 (beforeSwapReturn v I g s0 mem free ret R) result := by
  rcases beforeSwapBodyCorrect
      (f := beforeSwapCallFrame f hook key p (I.calldata.extract src.toNat (src.toNat+len.toNat)))
      v hstack hI hσ0 hc (store_get_self _ _ _)
      ((store_get_ne _ _ (by decide : ("self" == "key") = false)).trans (store_get_self _ _ _))
      ((store_get_ne2 _ _ _ (by decide : ("key" == "params") = false)
        (by decide : ("self" == "params") = false)).trans (store_get_self _ _ _))
      ((store_get_ne3 _ _ _ _ (by decide : ("params" == "hookData") = false)
        (by decide : ("key" == "hookData") = false)
        (by decide : ("self" == "hookData") = false)).trans (store_get_self _ _ _))
      hkey hparams hcanonical hlimit hkb hpb hklo hf hroom hsrc hgas hpaid hfree hret h with
    hog | ⟨result, hbody, htrace⟩
  · exact .inl hog
  · refine .inr ⟨result, ?_, htrace⟩
    exact internalCallFunctionExec (caller := f) (name := "Hooks_beforeSwap") (retVar := dest)
      (args := [es, ek, ep, ed])
      (argVals := [.address hook, poolKeyValue key, swapParamsValue p,
        .bytes (I.calldata.extract src.toNat (src.toNat+len.toNat))])
      (by simp only [evalExprs?, hs, hk, hp, hd, bind, EvalResult.bind, pure])
      (by rw [hc]; exact beforeSwap_lookup) rfl hbody

end Benchmarks.UniswapV4PoolManager
