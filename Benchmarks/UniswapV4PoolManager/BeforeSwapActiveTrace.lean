import Benchmarks.UniswapV4PoolManager.BeforeSwapPrepareTrace
import Benchmarks.UniswapV4PoolManager.HookCallPaidTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem beforeSwapActiveTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw free keyPtr paramsPtr src len : UInt256} {hook : AccountAddress}
    {k C : Nat} {R : List UInt256} {key : PoolKeyWords} {p : SwapParamsWords}
    (v : PoolManagerImmutables) (hstack : R.length+20 ≤ 1024)
    (hI : evm.executionEnv = I) (hσ0 : evm.σ₀ = s0.σ₀)
    (hk : PoolKeyView mem keyPtr key)
    (hp : MemorySlice mem paramsPtr.toNat (wordBytes (swapParamsWordList p)))
    (hc : PoolKeyCanonical key) (hl : p.priceLimit.toNat < 2^160)
    (hkb : keyPtr.toNat+160 ≤ free.toNat) (hpb : paramsPtr.toNat+96 ≤ free.toNat)
    (hlo : 96 ≤ free.toNat) (hf : free.toNat+len.toNat+480 < UInt256.size)
    (hsrc : src.toNat+len.toNat ≤ I.calldata.size)
    (hgas : g.toNat < 324518553658429321982441292826060) (hpaid : Cₘ aw ≤ C)
    (hfree : memLoad (UInt256.ofNat 64) mem = free)
    (h : RD (deployedRuntime v) I g s0 ⟨15230⟩
      (src :: len :: paramsPtr :: accountWord hook :: keyPtr :: R) mem aw rdata evm.accountMap k C) :
    X (g.toNat+1) (D_J (deployedRuntime v) 0) s0 = .error .OutOfGass ∨
    ∃ post z out, AllocationBounds free (beforeSwapAllocationSize len) ∧
      callViaEVM evm hook 0 (beforeSwapPayload I.source key p
        (I.calldata.extract src.toNat (src.toNat+len.toNat))) (z, post, out) ∧
      post.executionEnv = I ∧ post.σ₀ = s0.σ₀ ∧ out.size < 2^138 ∧
      (if z = true ∧ hookReplyValid (beforeSwapPayload I.source key p
          (I.calldata.extract src.toNat (src.toNat+len.toNat))) out then
        ∃ aw' k' C', Cₘ aw' ≤ C' ∧ (beforeSwapFree free len).toNat+out.size+4096 ≤ solcMaxU64 ∧
        RD (deployedRuntime v) I g s0 ⟨15462⟩
          (beforeSwapFree free len :: accountWord hook :: keyPtr :: R)
          (solcReturnDataMem (beforeSwapMemory I.calldata mem src.toNat free len I.source key p)
            (beforeSwapFree free len) out) aw' out post.accountMap k' C'
      else RDrev (deployedRuntime v) g s0) := by
  rcases beforeSwapPrepareTrace v hstack hk hp hc hl hkb hpb hf hgas hpaid hfree h with
    hog | ⟨hb, aw1, k1, C1, hpay1, rd1⟩
  · exact .inl hog
  have he := beforeSwapFree_toNat free len hf
  have hb' : (beforeSwapFree free len).toNat ≤ solcMaxU64 := hb.2
  have hfit : (beforeSwapFree free len).toNat+32 < UInt256.size := by
    have : solcMaxU64+32 < UInt256.size := by decide
    omega
  have hsize : (I.calldata.extract src.toNat (src.toNat+len.toNat)).size = len.toNat := by
    rw [ByteArray.size_extract]; omega
  have hdata := beforeSwapMemory_object I.calldata mem src.toNat free len I.source key p hsrc hlo
  have hin := hdata.inBounds
  rcases hookCallPaidTrace v
    (by simp only [List.length_cons]; omega) hI hσ0 (by omega) hdata
    (by rw [beforeSwapPayload, swapHookPayload_size]; change 32 ≤ 356+_; omega)
    (by
      rw [beforeSwapPayload, swapHookPayload_size, hsize]
      change 356+paddedSize len.toNat ≤ Ethereum.EVM.maxReturnDataSizeByGas
      have hmax : solcMaxU64 ≤ Ethereum.EVM.maxReturnDataSizeByGas := by decide
      rw [he] at hb'
      omega)
    (by omega) (by rw [beforeSwapPayload, swapHookPayload_size, hsize, he]; change _+32+(356+_) ≤ _; omega)
    hfit (beforeSwapMemory_free _ _ _ _ _ _ _ _)
    hgas hpay1 (by rw [poolManagerPatchedValidJumps v]; jump_dest) rd1 with
      hog | ⟨post, z, out, hcall, henv, hworld, ho, hr⟩
  · exact .inl hog
  · exact .inr ⟨post, z, out, hb, hcall, henv, hworld, ho, hr⟩

end Benchmarks.UniswapV4PoolManager
