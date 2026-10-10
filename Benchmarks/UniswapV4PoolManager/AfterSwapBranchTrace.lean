import Benchmarks.UniswapV4PoolManager.AfterSwapActiveTrace
import Benchmarks.UniswapV4PoolManager.AfterSwapUpdateTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000
attribute [local irreducible] afterSwapUpdateResult

theorem afterSwapBranchTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw free keyPtr paramsPtr src len specified delta ret : UInt256}
    {unspecified : Int} {hook : AccountAddress} {k C : Nat} {R : List UInt256}
    {key : PoolKeyWords} {p : SwapParamsWords}
    (f : Frame) (v : PoolManagerImmutables) (hstack : R.length+26 ≤ 1024)
    (hI : evm.executionEnv = I) (hσ0 : evm.σ₀ = s0.σ₀)
    (hk : PoolKeyView mem keyPtr key)
    (hp : MemorySlice mem paramsPtr.toNat (wordBytes (swapParamsWordList p)))
    (hc : PoolKeyCanonical key) (hl : p.priceLimit.toNat < 2^160)
    (hu : signedFits ⟨128, by decide⟩ unspecified)
    (hkb : keyPtr.toNat+160 ≤ free.toNat) (hpb : paramsPtr.toNat+96 ≤ free.toNat)
    (hlo : 96 ≤ free.toNat) (hf : free.toNat+len.toNat+512 < UInt256.size)
    (hsrc : src.toNat+len.toNat ≤ I.calldata.size)
    (hgas : g.toNat < 324518553658429321982441292826060) (hpaid : Cₘ aw ≤ C)
    (hfree : memLoad (UInt256.ofNat 64) mem = free)
    (h : RD (deployedRuntime v) I g s0 ⟨15936⟩
      (paramsPtr :: len :: src :: keyPtr :: accountWord hook :: EVM.wordOfInt unspecified ::
        specified :: delta :: ret :: paramsPtr :: R) mem aw rdata evm.accountMap k C) :
    X (g.toNat+1) (D_J (deployedRuntime v) 0) s0 = .error .OutOfGass ∨
    ∃ post z out, callViaEVM evm hook 0 (afterSwapPayload I.source key p delta
        (I.calldata.extract src.toNat (src.toNat+len.toNat))) (z, post, out) ∧
      post.executionEnv = I ∧ post.σ₀ = s0.σ₀ ∧
      blockResultTrace (deployedRuntime v) g s0 (fun _ next => next = post ∧
        (afterSwapFree free len).toNat+out.size+4096 ≤ solcMaxU64 ∧
        ∃ aw' k' C', Cₘ aw' ≤ C' ∧ RD (deployedRuntime v) I g s0 ⟨15800⟩
          (paramsPtr :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
            EVM.wordOfInt (unspecified+EVM.signed (hookDeltaWord out (afterSwapParse hook))) ::
            specified :: delta :: ret :: paramsPtr :: R)
          (afterSwapReplyMemory I.calldata mem src.toNat free len I.source key p delta out)
          aw' out next.accountMap k' C') (fun _ _ => False)
        (afterSwapBranchResult f post unspecified z (afterSwapPayload I.source key p delta
          (I.calldata.extract src.toNat (src.toNat+len.toNat))) out (afterSwapParse hook)) := by
  rcases afterSwapActiveTrace f v hstack hI hσ0 hk hp hc hl hkb hpb hlo hf hsrc hgas hpaid hfree h with
    hog | ⟨post, z, out, hcall, henv, hworld, hr⟩
  · exact .inl hog
  refine .inr ⟨post, z, out, hcall, henv, hworld, ?_⟩
  let payload := afterSwapPayload I.source key p delta (I.calldata.extract src.toNat (src.toNat+len.toNat))
  by_cases hv : z = true ∧ hookReplyValid payload out
  · rw [hookDeltaResult, if_pos hv, hookDeltaReplyResult] at hr
    rw [afterSwapBranchResult, if_pos hv]
    by_cases hbad : afterSwapParse hook = true ∧ out.size ≠ 64
    · rw [if_pos hbad] at hr ⊢
      exact hr
    · rw [if_neg hbad] at hr ⊢
      obtain ⟨_, _, aw1, k1, C1, hpay1, hbound, rd1⟩ := hr
      have ht := afterSwapUpdateTrace (afterSwapReplyFrame f payload out (afterSwapParse hook)) v
        (by simp only [List.length_cons]; omega) hu (by rw [poolManagerPatchedValidJumps v]; jump_dest) rd1
      refine blockResultTrace_mono ht ?_
      rintro f' next _ ⟨rfl, k2, C2, hcost, rd2⟩
      have rd3 := poolManagerBlocks.poolManager_block_16142 (by omega)
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd2
      exact ⟨rfl, hbound, _, _, _, by omega, rd3⟩
  · rw [hookDeltaResult, if_neg hv] at hr
    rw [afterSwapBranchResult, if_neg hv]
    exact hr

end Benchmarks.UniswapV4PoolManager
