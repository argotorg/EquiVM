import Benchmarks.UniswapV4PoolManager.DonateHookActiveTrace
import Benchmarks.UniswapV4PoolManager.FunctionResultTrace
import Benchmarks.UniswapV4PoolManager.PoolStorage
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_028
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_030

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def beforeDonateReturn (v : PoolManagerImmutables) (I : ExecutionEnv) (g : Sat256) (s0 : State)
    (mem : ByteArray) (free id keyPtr src amount0 amount1 len junk : UInt256) (R : List UInt256)
    (post : State) (values : Option (List Value)) : Prop :=
  post.executionEnv = I ∧ post.σ₀ = s0.σ₀ ∧ values = none ∧
  ∃ out data nextFree aw k C j0 j1,
    HookReturnMemory 4000 mem out free nextFree ∧ Cₘ aw ≤ C ∧
    RD (deployedRuntime v) I g s0 ⟨10191⟩
      (j0 :: j1 :: (keyPtr+UInt256.ofNat 128) :: keyPtr :: src :: amount1 :: amount0 :: len ::
        poolSlot id :: id :: junk :: R) out aw data post.accountMap k C

theorem beforeDonateHookTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw free id keyPtr src amount0 amount1 len junk : UInt256}
    {hook : AccountAddress} {k C : Nat} {R : List UInt256} {key : PoolKeyWords}
    (f : Frame) (v : PoolManagerImmutables) (hstack : R.length+33 ≤ 1024)
    (hI : evm.executionEnv = I) (hσ0 : evm.σ₀ = s0.σ₀)
    (hk : PoolKeyView mem keyPtr key) (hc : PoolKeyCanonical key) (hw : accountWord hook = key.hooks)
    (hb : keyPtr.toNat+160 ≤ free.toNat) (hlo : 96 ≤ free.toNat)
    (hf : free.toNat+len.toNat+448 < UInt256.size) (hroom : free.toNat+4000 ≤ solcMaxU64)
    (hsrc : src.toNat+len.toNat ≤ I.calldata.size)
    (hgas : g.toNat < 324518553658429321982441292826060) (hpaid : Cₘ aw ≤ C+49)
    (hfree : memLoad (UInt256.ofNat 64) mem = free)
    (h : RD (deployedRuntime v) I g s0 ⟨10153⟩
      (keyPtr :: src :: amount1 :: amount0 :: len :: poolSlot id :: id :: junk :: R)
      mem aw rdata evm.accountMap k C) :
    X (g.toNat+1) (D_J (deployedRuntime v) 0) s0 = .error .OutOfGass ∨
    ∃ post z out,
      (hookEnabled I.source hook ⟨32⟩ → callViaEVM evm hook 0
        (donateHookPayload false I.source key amount0 amount1 (I.calldata.extract src.toNat (src.toNat+len.toNat)))
        (z, post, out)) ∧
      functionResultTrace (deployedRuntime v) g s0
        (beforeDonateReturn v I g s0 mem free id keyPtr src amount0 amount1 len junk R)
        (hookInvocationResult f evm post (hookEnabled I.source hook ⟨32⟩) z
          (donateHookPayload false I.source key amount0 amount1 (I.calldata.extract src.toNat (src.toNat+len.toNat))) out) := by
  have hload : memLoad (keyPtr+UInt256.ofNat 128) mem = accountWord hook :=
    (hk.load (i := 4) (word := key.hooks) rfl).trans hw.symm
  have hclean : UInt256.land (accountWord hook) (UInt256.ofNat 1461501637330902918203684832716283019655932542975) =
      accountWord hook := solcAddrMask_clean (accountWord_canonical hook)
  have heq : I.source = hook ↔ accountWord I.source = accountWord hook := by
    simpa only [accountWord_address] using accountWord_eq_iff I.source (accountWord hook) (accountWord_canonical hook)
  have hcond : UInt256.sub (UInt256.ofNat I.source.val)
      (UInt256.land (memLoad (keyPtr+UInt256.ofNat 128) mem)
        (UInt256.ofNat 1461501637330902918203684832716283019655932542975)) = ⟨0⟩ ↔ I.source = hook := by
    rw [hload, hclean, u256_sub_eq_zero_iff_eq]
    exact heq.symm
  have hm : HookReturnMemory 4000 mem mem free free :=
    ⟨hfree, Nat.le_refl _, hroom, fun _ _ hs _ _ => hs⟩
  by_cases hself : I.source = hook
  · have hn : ¬hookEnabled I.source hook ⟨32⟩ := fun he => he.1 hself
    have rd := poolManagerBlocks.poolManager_block_10153_fallthrough
      (by simp only [List.length_cons]; omega) (hcond.mpr hself) h
    simp only [poolManagerBlocks.poolManager_block_10153_fallthrough_stack, hload, hclean] at rd
    refine .inr ⟨evm, false, .empty, fun he => (hn he).elim, ?_⟩
    simp only [hookInvocationResult, if_neg hn, functionResultTrace]
    refine ⟨hI, hσ0, rfl, mem, rdata, free, _, _, _, _, _, hm, ?_, rd⟩
    dsimp only [memExpansionCost]
    omega
  have rd := poolManagerBlocks.poolManager_block_10153_taken
    (by simp only [List.length_cons]; omega) (fun he => hself (hcond.mp he))
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
  simp only [poolManagerBlocks.poolManager_block_10153_taken_stack, hload, hclean] at rd
  have hpaid1 : Cₘ (M aw (keyPtr+UInt256.ofNat 128) ⟨32⟩) ≤
      C+(49+memExpansionCost aw (keyPtr+UInt256.ofNat 128) ⟨32⟩) := by
    dsimp only [memExpansionCost]; omega
  have hcomm : UInt256.land (UInt256.ofNat 32) (accountWord hook) = UInt256.land (accountWord hook) ⟨32⟩ :=
    u256_land_comm ..
  by_cases hz : UInt256.land (accountWord hook) ⟨32⟩ = ⟨0⟩
  · have hn : ¬hookEnabled I.source hook ⟨32⟩ := fun he => he.2 hz
    have rd1 := poolManagerBlocks.poolManager_block_10563_fallthrough
      (by simp only [List.length_cons]; omega) (hcomm.trans hz) rd
    have rd2 := poolManagerBlocks.poolManager_block_10571
      (by simp only [poolManagerBlocks.poolManager_block_10563_fallthrough_stack, List.length_cons]; omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
    refine .inr ⟨evm, false, .empty, fun he => (hn he).elim, ?_⟩
    simp only [hookInvocationResult, if_neg hn, functionResultTrace]
    exact ⟨hI, hσ0, rfl, mem, rdata, free, _, _, _, _, _, hm, by omega, rd2⟩
  have hen : hookEnabled I.source hook ⟨32⟩ := ⟨hself, hz⟩
  have rd1 := poolManagerBlocks.poolManager_block_10563_taken
    (by simp only [List.length_cons]; omega) (fun he => hz (hcomm.symm.trans he))
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd
  rcases donateHookActiveTrace (hookPtr := keyPtr+UInt256.ofNat 128) (delta := ⟨0⟩)
      (R := poolSlot id :: id :: junk :: R) v false
      (by simp only [List.length_cons]; omega) hI hσ0 hk hc hb hlo hf hsrc hgas
      (by omega) hfree rd1 with hog | ⟨post, z, out, hcall, henv, hworld, ho, hr⟩
  · exact .inl hog
  refine .inr ⟨post, z, out, fun _ => hcall, ?_⟩
  simp only [hookInvocationResult, if_pos hen]
  split_ifs with hv
  · rw [if_pos hv] at hr
    obtain ⟨hm', aw2, k2, C2, hpaid2, rd2⟩ := hr
    have rd3 := poolManagerBlocks.poolManager_block_10644 (by omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd2
    have rd4 := poolManagerBlocks.poolManager_block_10571
      (by simp only [poolManagerBlocks.poolManager_block_10644_stack, List.length_cons]; omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd3
    exact ⟨henv, hworld, rfl, _, out, _, _, _, _, _, _, hm', by omega, rd4⟩
  · rwa [if_neg hv] at hr

end Benchmarks.UniswapV4PoolManager
