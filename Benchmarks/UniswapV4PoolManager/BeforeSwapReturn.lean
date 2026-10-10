import Benchmarks.UniswapV4PoolManager.BeforeSwapReplyMemory
import Benchmarks.UniswapV4PoolManager.BeforeSwapFeeTrace
import Benchmarks.UniswapV4PoolManager.BeforeSwapSource
import Benchmarks.UniswapV4PoolManager.HookReturnMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager

abbrev BeforeSwapReturnMemory := HookReturnMemory 4000

def beforeSwapReturn (v : PoolManagerImmutables) (I : ExecutionEnv) (g : Sat256) (s0 : State)
    (mem : ByteArray) (start ret : UInt256) (R : List UInt256)
    (post : State) (values : Option (List Value)) : Prop :=
  ∃ amount hookReturn fee rawFee out rdata free aw k C,
    post.executionEnv = I ∧ post.σ₀ = s0.σ₀ ∧
    values = some (beforeSwapReturnValues amount hookReturn fee) ∧ fee.toNat < 2^24 ∧
    UInt256.land rawFee (UInt256.ofNat 16777215) = fee ∧ Cₘ aw ≤ C ∧
    RD (deployedRuntime v) I g s0 ret (rawFee :: hookReturn :: amount :: R) out aw rdata post.accountMap k C ∧
    BeforeSwapReturnMemory mem out start free

theorem beforeSwapReturn_bypass {v : PoolManagerImmutables} {I : ExecutionEnv} {g : Sat256}
    {s0 post : State} {mem rdata : ByteArray} {free ret amount aw : UInt256} {k C : Nat} {R : List UInt256}
    (hI : post.executionEnv = I) (hσ0 : post.σ₀ = s0.σ₀)
    (hfree : memLoad (UInt256.ofNat 64) mem = free) (hf : free.toNat+4000 ≤ solcMaxU64)
    (hpaid : Cₘ aw ≤ C)
    (h : RD (deployedRuntime v) I g s0 ret (⟨0⟩ :: ⟨0⟩ :: amount :: R) mem aw rdata post.accountMap k C) :
    beforeSwapReturn v I g s0 mem free ret R post (some (beforeSwapReturnValues amount ⟨0⟩ ⟨0⟩)) := by
  exact ⟨amount, ⟨0⟩, ⟨0⟩, ⟨0⟩, mem, rdata, free, aw, k, C, hI, hσ0, rfl, by decide,
    by decide, hpaid, h, ⟨hfree, le_refl _, hf, fun _ _ hs _ _ => hs⟩⟩

theorem beforeSwapReturn_hook {v : PoolManagerImmutables} {I : ExecutionEnv} {g : Sat256}
    {s0 post : State} {mem out : ByteArray} {free ret amount src len aw : UInt256}
    {hook : AccountAddress} {key : PoolKeyWords} {p : SwapParamsWords} {k C : Nat} {R : List UInt256}
    (hI : post.executionEnv = I) (hσ0 : post.σ₀ = s0.σ₀)
    (hsrc : src.toNat+len.toNat ≤ I.calldata.size) (hlo : 96 ≤ free.toNat)
    (hf : free.toNat+len.toNat+480 < UInt256.size)
    (hbound : (beforeSwapFree free len).toNat+out.size+4096 ≤ solcMaxU64) (hpaid : Cₘ aw ≤ C)
    (h : RD (deployedRuntime v) I g s0 ret
      (beforeSwapRawFee key out :: beforeSwapReplyHook hook out :: beforeSwapReplyAmount hook amount out :: R)
      (beforeSwapReplyMemory I.calldata mem src.toNat free len I.source key p out) aw out post.accountMap k C) :
    beforeSwapReturn v I g s0 mem free ret R post
      (some (beforeSwapReturnValues (beforeSwapReplyAmount hook amount out)
        (beforeSwapReplyHook hook out) (beforeSwapFee key out))) := by
  have hb := beforeSwapReplyFree_bounds free len out hf hbound
  refine ⟨_, _, _, beforeSwapRawFee key out, _, out, beforeSwapReplyFree free len out, aw, k, C,
    hI, hσ0, rfl, beforeSwapFee_bound key out, beforeSwapRawFee_clean key out, hpaid, h, ?_⟩
  exact ⟨beforeSwapReplyMemory_free _ _ _ _ _ _ _ _ _ hlo hf, hb.1, hb.2,
    fun _ _ hs hl he => hs.beforeSwapReply I.calldata src.toNat free len I.source key p out hsrc hl he hf⟩

end Benchmarks.UniswapV4PoolManager
