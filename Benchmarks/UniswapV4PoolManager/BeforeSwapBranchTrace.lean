import Benchmarks.UniswapV4PoolManager.BeforeSwapActiveTrace
import Benchmarks.UniswapV4PoolManager.BeforeSwapReplyTrace
import Benchmarks.UniswapV4PoolManager.BeforeSwapReplyMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000
attribute [local irreducible] beforeSwapReplyResult

theorem beforeSwapBranchTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw free keyPtr paramsPtr src len ret : UInt256} {hook : AccountAddress}
    {k C : Nat} {R : List UInt256} {key : PoolKeyWords} {p : SwapParamsWords}
    (f : Frame) (v : PoolManagerImmutables) (hstack : R.length+24 ≤ 1024)
    (hI : evm.executionEnv = I) (hσ0 : evm.σ₀ = s0.σ₀)
    (hk : PoolKeyView mem keyPtr key)
    (hp : MemorySlice mem paramsPtr.toNat (wordBytes (swapParamsWordList p)))
    (hc : PoolKeyCanonical key) (hl : p.priceLimit.toNat < 2^160)
    (hkb : keyPtr.toNat+160 ≤ free.toNat) (hpb : paramsPtr.toNat+96 ≤ free.toNat)
    (hklo : 96 ≤ keyPtr.toNat) (hf : free.toNat+len.toNat+480 < UInt256.size)
    (hsrc : src.toNat+len.toNat ≤ I.calldata.size)
    (hgas : g.toNat < 324518553658429321982441292826060) (hpaid : Cₘ aw ≤ C)
    (hfree : memLoad (UInt256.ofNat 64) mem = free)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨15230⟩
      (src :: len :: paramsPtr :: accountWord hook :: keyPtr :: ret :: ⟨0⟩ :: ⟨0⟩ :: p.amountSpecified :: R)
      mem aw rdata evm.accountMap k C) :
    X (g.toNat+1) (D_J (deployedRuntime v) 0) s0 = .error .OutOfGass ∨
    ∃ post z out,
      callViaEVM evm hook 0 (beforeSwapPayload I.source key p
        (I.calldata.extract src.toNat (src.toNat+len.toNat))) (z, post, out) ∧
      post.executionEnv = I ∧ post.σ₀ = s0.σ₀ ∧
      blockResultTrace (deployedRuntime v) g s0 (fun _ next => next = post ∧
        (beforeSwapFree free len).toNat+out.size+4096 ≤ solcMaxU64 ∧
        ∃ aw' k' C', Cₘ aw' ≤ C' ∧ RD (deployedRuntime v) I g s0 ret
          (beforeSwapRawFee key out :: beforeSwapReplyHook hook out :: beforeSwapReplyAmount hook p.amountSpecified out :: R)
          (beforeSwapReplyMemory I.calldata mem src.toNat free len I.source key p out) aw' out next.accountMap k' C')
        (fun _ _ => False)
        (beforeSwapBranchResult f post hook key p.amountSpecified z
          (beforeSwapPayload I.source key p (I.calldata.extract src.toNat (src.toNat+len.toNat))) out) := by
  rcases beforeSwapActiveTrace v (by simp only [List.length_cons]; omega) hI hσ0 hk hp hc hl
      hkb hpb (by omega) hf hsrc hgas hpaid hfree h with
    hog | ⟨post, z, out, hb, hcall, henv, hworld, ho, hr⟩
  · exact .inl hog
  refine .inr ⟨post, z, out, hcall, henv, hworld, ?_⟩
  let payload := beforeSwapPayload I.source key p (I.calldata.extract src.toNat (src.toNat+len.toNat))
  by_cases hv : z = true ∧ hookReplyValid payload out
  · rw [if_pos hv] at hr
    rw [beforeSwapBranchResult, if_pos hv]
    obtain ⟨aw1, k1, C1, hpay1, hbound, rd1⟩ := hr
    have hfit : (beforeSwapFree free len).toNat+96 < UInt256.size := by
      change _ ≤ 2^64-1 at hbound
      change _ < 2^256
      omega
    have hkey : PoolKeyView (beforeSwapReplyMemory I.calldata mem src.toNat free len I.source key p out) keyPtr key := by
      refine ⟨hk.slice.beforeSwapReply I.calldata src.toNat free len I.source key p out hsrc hklo ?_ hf, hk.fits⟩
      simpa only [wordBytes_size, poolKeyWordList, List.length_cons, List.length_nil] using hkb
    have hdata := beforeSwapMemory_object I.calldata mem src.toNat free len I.source key p hsrc (by omega)
    have hmem := hdata.inBounds
    have hview := returnDataMemory_view (beforeSwapMemory I.calldata mem src.toNat free len I.source key p)
      (beforeSwapFree free len) out (by omega) (by omega)
    have ht := beforeSwapReplyTrace (beforeSwapHookFrame f payload out) v (by omega) hkey hc.2.2.1
      hview (lt_trans ho (by decide)) hfit hret rd1
    refine blockResultTrace_mono ht ?_
    rintro f' next _ ⟨he, aw', k', C', hcost, rd⟩
    exact ⟨he, hbound, aw', k', C', by omega, rd⟩
  · rw [if_neg hv] at hr
    rw [beforeSwapBranchResult, if_neg hv]
    exact hr

end Benchmarks.UniswapV4PoolManager
