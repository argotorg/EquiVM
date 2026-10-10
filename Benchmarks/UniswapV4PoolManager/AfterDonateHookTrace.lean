import Benchmarks.UniswapV4PoolManager.DonateHookActiveTrace
import Benchmarks.UniswapV4PoolManager.FunctionResultTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem donateWordReturnTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw x0 x1 x2 x3 x4 x5 x6 delta : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (v : PoolManagerImmutables) (hstack : R.length+13 ≤ 1024)
    (h : RD (deployedRuntime v) I g s0 ⟨10381⟩
      (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: delta :: ⟨32⟩ :: R) mem aw rdata σ k C) :
    RDret (deployedRuntime v) g s0 σ delta.toByteArray := by
  have hr := poolManagerBlocks.poolManager_block_10381 hstack h
  change RDret _ _ _ _ (writeWord mem (memLoad (UInt256.ofNat 64) mem).toNat delta
    |>.readWithPadding (memLoad (UInt256.ofNat 64) mem).toNat 32) at hr
  rwa [writeWord_sparse_read_back] at hr

theorem afterDonateHookTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw free keyPtr src amount0 amount1 len delta junk : UInt256}
    {hook : AccountAddress} {k C : Nat} {R : List UInt256} {key : PoolKeyWords}
    (f : Frame) (v : PoolManagerImmutables) (hstack : R.length+31 ≤ 1024)
    (hI : evm.executionEnv = I) (hσ0 : evm.σ₀ = s0.σ₀)
    (hk : PoolKeyView mem keyPtr key) (hc : PoolKeyCanonical key)
    (hb : keyPtr.toNat+160 ≤ free.toNat) (hlo : 96 ≤ free.toNat)
    (hf : free.toNat+len.toNat+448 < UInt256.size) (hsrc : src.toNat+len.toNat ≤ I.calldata.size)
    (hgas : g.toNat < 324518553658429321982441292826060) (hpaid : Cₘ aw ≤ C)
    (hfree : memLoad (UInt256.ofNat 64) mem = free)
    (h : RD (deployedRuntime v) I g s0 (if I.source = hook then ⟨10381⟩ else ⟨10391⟩)
      (accountWord hook :: amount1 :: keyPtr :: src :: accountWord hook :: amount0 :: len :: delta :: ⟨32⟩ :: junk :: R)
      mem aw rdata evm.accountMap k C) :
    X (g.toNat+1) (D_J (deployedRuntime v) 0) s0 = .error .OutOfGass ∨
    ∃ post z out,
      (hookEnabled I.source hook ⟨16⟩ → callViaEVM evm hook 0
        (donateHookPayload true I.source key amount0 amount1 (I.calldata.extract src.toNat (src.toNat+len.toNat)))
        (z, post, out)) ∧
      functionResultTrace (deployedRuntime v) g s0
        (fun post values => values = none ∧ RDret (deployedRuntime v) g s0 post.accountMap delta.toByteArray)
        (hookInvocationResult f evm post (hookEnabled I.source hook ⟨16⟩) z
          (donateHookPayload true I.source key amount0 amount1 (I.calldata.extract src.toNat (src.toNat+len.toNat))) out) := by
  by_cases hself : I.source = hook
  · rw [if_pos hself] at h
    have hn : ¬hookEnabled I.source hook ⟨16⟩ := fun he => he.1 hself
    refine .inr ⟨evm, false, .empty, fun he => (hn he).elim, ?_⟩
    simp only [hookInvocationResult, if_neg hn, functionResultTrace]
    exact ⟨True.intro, donateWordReturnTrace v (by simp only [List.length_cons]; omega) h⟩
  rw [if_neg hself] at h
  have hcomm : UInt256.land (UInt256.ofNat 16) (accountWord hook) = UInt256.land (accountWord hook) ⟨16⟩ :=
    u256_land_comm ..
  by_cases hz : UInt256.land (accountWord hook) ⟨16⟩ = ⟨0⟩
  · have hn : ¬hookEnabled I.source hook ⟨16⟩ := fun he => he.2 hz
    have rd1 := poolManagerBlocks.poolManager_block_10391_fallthrough
      (by simp only [List.length_cons]; omega) (hcomm.trans hz) h
    have rd2 := poolManagerBlocks.poolManager_block_10399
      (by simp only [List.length_cons]; omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
    refine .inr ⟨evm, false, .empty, fun he => (hn he).elim, ?_⟩
    simp only [hookInvocationResult, if_neg hn, functionResultTrace]
    exact ⟨True.intro, donateWordReturnTrace v (by simp only [List.length_cons]; omega) rd2⟩
  have hen : hookEnabled I.source hook ⟨16⟩ := ⟨hself, hz⟩
  have rd1 := poolManagerBlocks.poolManager_block_10391_taken
    (by simp only [List.length_cons]; omega) (fun he => hz (hcomm.symm.trans he))
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
  rcases donateHookActiveTrace (hookPtr := ⟨0⟩) (R := junk :: R) v true
      (by simp only [List.length_cons]; omega) hI hσ0 hk hc hb hlo hf hsrc hgas
      (by omega) hfree rd1 with hog | ⟨post, z, out, hcall, henv, hworld, ho, hr⟩
  · exact .inl hog
  refine .inr ⟨post, z, out, fun _ => hcall, ?_⟩
  simp only [hookInvocationResult, if_pos hen]
  split_ifs with hv
  · rw [if_pos hv] at hr
    obtain ⟨hm, aw2, k2, C2, hpaid2, rd2⟩ := hr
    have rd3 := poolManagerBlocks.poolManager_block_10470 (by omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd2
    have rd4 := poolManagerBlocks.poolManager_block_10399
      (by simp only [List.length_cons]; omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd3
    exact ⟨rfl, donateWordReturnTrace v (by simp only [List.length_cons]; omega) rd4⟩
  · rwa [if_neg hv] at hr

end Benchmarks.UniswapV4PoolManager
