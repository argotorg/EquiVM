import Benchmarks.UniswapV4PoolManager.AfterSwapReplyMemory
import Benchmarks.UniswapV4PoolManager.HookReturnMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager

abbrev AfterSwapReturnMemory := HookReturnMemory 64

def afterSwapReturn (v : PoolManagerImmutables) (I : ExecutionEnv) (g : Sat256) (s0 : State)
    (mem : ByteArray) (start ret : UInt256) (R : List UInt256)
    (post : State) (values : Option (List Value)) : Prop :=
  ∃ delta hookDelta out rdata free aw k C,
    post.executionEnv = I ∧ post.σ₀ = s0.σ₀ ∧
    values = some [.int (EVM.signed delta), .int (EVM.signed hookDelta)] ∧ Cₘ aw ≤ C ∧
    RD (deployedRuntime v) I g s0 ret (hookDelta :: delta :: R) out aw rdata post.accountMap k C ∧
    AfterSwapReturnMemory mem out start free

theorem afterSwapReturn_unchanged {v : PoolManagerImmutables} {I : ExecutionEnv} {g : Sat256}
    {s0 post : State} {mem rdata : ByteArray} {free ret delta hookDelta aw : UInt256} {k C : Nat} {R : List UInt256}
    (hI : post.executionEnv = I) (hσ0 : post.σ₀ = s0.σ₀)
    (hfree : memLoad (UInt256.ofNat 64) mem = free) (hf : free.toNat+64 ≤ solcMaxU64)
    (hpaid : Cₘ aw ≤ C)
    (h : RD (deployedRuntime v) I g s0 ret (hookDelta :: delta :: R) mem aw rdata post.accountMap k C) :
    afterSwapReturn v I g s0 mem free ret R post (some [.int (EVM.signed delta), .int (EVM.signed hookDelta)]) := by
  exact ⟨delta, hookDelta, mem, rdata, free, aw, k, C, hI, hσ0, rfl, hpaid, h,
    ⟨hfree, le_refl _, hf, fun _ _ hs _ _ => hs⟩⟩

theorem afterSwapReturn_hook {v : PoolManagerImmutables} {I : ExecutionEnv} {g : Sat256}
    {s0 post : State} {mem out : ByteArray} {free ret delta hookDelta src len aw initialDelta : UInt256}
    {key : PoolKeyWords} {p : SwapParamsWords} {k C : Nat} {R : List UInt256}
    (hI : post.executionEnv = I) (hσ0 : post.σ₀ = s0.σ₀)
    (hsrc : src.toNat+len.toNat ≤ I.calldata.size) (hlo : 96 ≤ free.toNat)
    (hf : free.toNat+len.toNat+512 < UInt256.size)
    (hbound : (afterSwapFree free len).toNat+out.size+4096 ≤ solcMaxU64) (hpaid : Cₘ aw ≤ C)
    (h : RD (deployedRuntime v) I g s0 ret (hookDelta :: delta :: R)
      (afterSwapReplyMemory I.calldata mem src.toNat free len I.source key p initialDelta out)
      aw out post.accountMap k C) :
    afterSwapReturn v I g s0 mem free ret R post (some [.int (EVM.signed delta), .int (EVM.signed hookDelta)]) := by
  have hb := afterSwapReplyFree_bounds free len out hf hbound
  refine ⟨delta, hookDelta, _, out, afterSwapReplyFree free len out, aw, k, C, hI, hσ0, rfl, hpaid, h, ?_⟩
  exact ⟨afterSwapReplyMemory_free _ _ _ _ _ _ _ _ _ _ hlo hf, hb.1, by omega,
    fun _ _ hs hl he => hs.afterSwapReply I.calldata src.toNat free len I.source key p initialDelta out hsrc hl he hf⟩

end Benchmarks.UniswapV4PoolManager
