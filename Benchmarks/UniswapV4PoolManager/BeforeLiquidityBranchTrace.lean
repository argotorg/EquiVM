import Benchmarks.UniswapV4PoolManager.BeforeLiquidityActiveTrace
import Benchmarks.UniswapV4PoolManager.BeforeLiquiditySelectTrace
import Benchmarks.UniswapV4PoolManager.BeforeLiquidityReplyMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem beforeLiquidityBranchCallTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {free a b keyPtr paramsPtr src len : UInt256} {hook : AccountAddress}
    {R : List UInt256} {key : PoolKeyWords} {p : ModifyLiquidityWords}
    (v : PoolManagerImmutables) (add : Bool) (hstack : R.length+28 ≤ 1024)
    (hI : evm.executionEnv = I) (hσ0 : evm.σ₀ = s0.σ₀)
    (hk : PoolKeyView mem keyPtr key)
    (hp : MemorySlice mem paramsPtr.toNat (wordBytes (modifyLiquidityWords p)))
    (hc : PoolKeyCanonical key) (hl : int24Canonical p.lower) (hu : int24Canonical p.upper)
    (hkb : keyPtr.toNat+160 ≤ free.toNat) (hpb : paramsPtr.toNat+128 ≤ free.toNat)
    (hlo : 96 ≤ free.toNat) (hf : free.toNat+len.toNat+512 < UInt256.size)
    (hsrc : src.toNat+len.toNat ≤ I.calldata.size)
    (hgas : g.toNat < 324518553658429321982441292826060)
    (hfree : memLoad (UInt256.ofNat 64) mem = free)
    (h : beforeLiquidityBranchTrace v I g s0 mem rdata evm.accountMap add hook src paramsPtr len keyPtr a b R) :
    X (g.toNat+1) (D_J (deployedRuntime v) 0) s0 = .error .OutOfGass ∨
    ∃ post z out, AllocationBounds free (beforeLiquidityAllocationSize len) ∧
      callViaEVM evm hook 0 (beforeLiquidityPayload add I.source key p
        (I.calldata.extract src.toNat (src.toNat+len.toNat))) (z, post, out) ∧
      post.executionEnv = I ∧ post.σ₀ = s0.σ₀ ∧ out.size < 2^138 ∧
      (z = true ∧ hookReplyValid (beforeLiquidityPayload add I.source key p
        (I.calldata.extract src.toNat (src.toNat+len.toNat))) out →
        (beforeLiquidityFree free len).toNat+out.size+4096 ≤ solcMaxU64) ∧
      (if z = true ∧ hookReplyValid (beforeLiquidityPayload add I.source key p
          (I.calldata.extract src.toNat (src.toNat+len.toNat))) out then
        beforeLiquidityContinuation v I g s0
          (beforeLiquidityReplyMemory add I.calldata mem src.toNat free len I.source key p out) out
          post.accountMap src paramsPtr len keyPtr a b R
      else RDrev (deployedRuntime v) g s0) := by
  obtain ⟨j0, j1, aw, k, C, hpaid, rd⟩ := h
  rcases beforeLiquidityActiveTrace v add (by simp only [List.length_cons]; omega)
    hI hσ0 hk hp hc hl hu hkb hpb hlo hf hsrc hgas hpaid hfree rd with
    hog | ⟨post, z, out, hb, hcall, henv, hworld, ho, hr⟩
  · exact .inl hog
  by_cases hh : z = true ∧ hookReplyValid (beforeLiquidityPayload add I.source key p
      (I.calldata.extract src.toNat (src.toNat+len.toNat))) out
  · rw [if_pos hh] at hr
    obtain ⟨aw', k', C', hpay', hbound, rd'⟩ := hr
    refine .inr ⟨post, z, out, hb, hcall, henv, hworld, ho, (fun _ => hbound), ?_⟩
    rw [if_pos hh]
    exact beforeLiquidityResumeTrace v add (by omega) hpay' rd'
  · rw [if_neg hh] at hr
    refine .inr ⟨post, z, out, hb, hcall, henv, hworld, ho, (fun hv => (hh hv).elim), ?_⟩
    rw [if_neg hh]
    exact hr

end Benchmarks.UniswapV4PoolManager
