import Benchmarks.UniswapV4PoolManager.AfterSwapPrepareTrace
import Benchmarks.UniswapV4PoolManager.AfterSwapReplyMemory
import Benchmarks.UniswapV4PoolManager.HookDeltaPaidTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem afterSwapActiveTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw free keyPtr paramsPtr src len unspecified specified delta ret : UInt256}
    {hook : AccountAddress} {k C : Nat} {R : List UInt256} {key : PoolKeyWords} {p : SwapParamsWords}
    (f : Frame) (v : PoolManagerImmutables) (hstack : R.length+26 ≤ 1024)
    (hI : evm.executionEnv = I) (hσ0 : evm.σ₀ = s0.σ₀)
    (hk : PoolKeyView mem keyPtr key)
    (hp : MemorySlice mem paramsPtr.toNat (wordBytes (swapParamsWordList p)))
    (hc : PoolKeyCanonical key) (hl : p.priceLimit.toNat < 2^160)
    (hkb : keyPtr.toNat+160 ≤ free.toNat) (hpb : paramsPtr.toNat+96 ≤ free.toNat)
    (hlo : 96 ≤ free.toNat) (hf : free.toNat+len.toNat+512 < UInt256.size)
    (hsrc : src.toNat+len.toNat ≤ I.calldata.size)
    (hgas : g.toNat < 324518553658429321982441292826060) (hpaid : Cₘ aw ≤ C)
    (hfree : memLoad (UInt256.ofNat 64) mem = free)
    (h : RD (deployedRuntime v) I g s0 ⟨15936⟩
      (paramsPtr :: len :: src :: keyPtr :: accountWord hook :: unspecified :: specified :: delta :: ret :: paramsPtr :: R)
      mem aw rdata evm.accountMap k C) :
    X (g.toNat+1) (D_J (deployedRuntime v) 0) s0 = .error .OutOfGass ∨
    ∃ post z out, callViaEVM evm hook 0 (afterSwapPayload I.source key p delta
        (I.calldata.extract src.toNat (src.toNat+len.toNat))) (z, post, out) ∧
      post.executionEnv = I ∧ post.σ₀ = s0.σ₀ ∧
      functionResultTrace (deployedRuntime v) g s0 (fun next values => next = post ∧
        values = some [.int (EVM.signed (hookDeltaWord out (afterSwapParse hook)))] ∧
        ∃ aw' k' C', Cₘ aw' ≤ C' ∧ (afterSwapFree free len).toNat+out.size+4096 ≤ solcMaxU64 ∧
        RD (deployedRuntime v) I g s0 ⟨6381⟩
          (hookDeltaWord out (afterSwapParse hook) :: UInt256.ofNat 16136 :: unspecified ::
            UInt256.ofNat 16142 :: specified :: delta :: ret :: paramsPtr :: R)
          (afterSwapReplyMemory I.calldata mem src.toNat free len I.source key p delta out)
          aw' out next.accountMap k' C')
        (hookDeltaResult f post z (afterSwapPayload I.source key p delta
          (I.calldata.extract src.toNat (src.toNat+len.toNat))) out (afterSwapParse hook)) := by
  rcases afterSwapPrepareTrace v hstack hk hp hc hl hkb hpb hf hgas hpaid hfree h with
    hog | ⟨hb, aw1, k1, C1, hpay1, rd1⟩
  · exact .inl hog
  have he := afterSwapFree_toNat free len hf
  have hb' : (afterSwapFree free len).toNat ≤ solcMaxU64 := hb.2
  have hfit : (afterSwapFree free len).toNat+64 < UInt256.size := by
    have : solcMaxU64+64 < UInt256.size := by decide
    omega
  have hsize : (I.calldata.extract src.toNat (src.toNat+len.toNat)).size = len.toNat := by
    rw [ByteArray.size_extract]; omega
  have hdata := afterSwapMemory_object I.calldata mem src.toNat free len I.source key p delta hsrc hlo
  have hin := hdata.inBounds
  rcases hookDeltaPaidTrace f v
    (by simp only [List.length_cons]; omega) hI hσ0 (by omega) hdata
    (by rw [afterSwapPayload, swapHookPayload_size]; change 32 ≤ 388+_; omega)
    (by
      rw [afterSwapPayload, swapHookPayload_size, hsize]
      change 388+paddedSize len.toNat ≤ Ethereum.EVM.maxReturnDataSizeByGas
      have hmax : solcMaxU64 ≤ Ethereum.EVM.maxReturnDataSizeByGas := by decide
      rw [he] at hb'
      omega)
    (by omega) (by rw [afterSwapPayload, swapHookPayload_size, hsize, he]; change _+32+(388+_) ≤ _; omega)
    hfit (afterSwapMemory_free _ _ _ _ _ _ _ _ _) hgas hpay1
    (by rw [poolManagerPatchedValidJumps v]; jump_dest) rd1 with
      hog | ⟨post, z, out, hcall, henv, hworld, ho, hr⟩
  · exact .inl hog
  · exact .inr ⟨post, z, out, hcall, henv, hworld, hr⟩

end Benchmarks.UniswapV4PoolManager
