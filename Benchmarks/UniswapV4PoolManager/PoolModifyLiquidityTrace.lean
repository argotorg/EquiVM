import Benchmarks.UniswapV4PoolManager.PoolModifyLiquidity
import Benchmarks.UniswapV4PoolManager.PoolModifyLiquidityStatic
import Benchmarks.UniswapV4PoolManager.LiquidityAddTrace
import Benchmarks.UniswapV4PoolManager.BalanceDeltaSource
import Benchmarks.UniswapV4PoolManager.BlockResultTrace
import Benchmarks.UniswapV4PoolManager.Signed128Range

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem poolModifyLiquidityExactTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id amount0 amount1 : UInt256} {delta : Int}
    {k C : Nat} {R : List UInt256} (f : Frame)
    (v : PoolManagerImmutables) (hstack : R.length+8 ≤ 1024) (hI : evm.executionEnv = I)
    (hm : memLoad (UInt256.ofNat 128) mem = poolSlot id) (hd : signedFits ⟨128, by decide⟩ delta)
    (h : RD (deployedRuntime v) I g s0 ⟨6461⟩
      (amount1 :: amount0 :: EVM.wordOfInt delta :: R) mem aw rdata evm.accountMap k C) :
    blockResultTrace (deployedRuntime v) g s0 (fun _ post =>
      post.executionEnv = I ∧ post.σ₀ = evm.σ₀ ∧ ∃ k' C',
        RD (deployedRuntime v) I g s0 ⟨6390⟩ (balanceDeltaWord amount0 amount1 :: R)
          mem (M aw (UInt256.ofNat 128) ⟨32⟩) rdata post.accountMap k' C') (fun _ _ => False)
      (poolModifyLiquidityResult f evm id delta) := by
  have hslot : memLoad (UInt256.ofNat 128) mem + UInt256.ofNat 3 = poolLiquiditySlot id := by
    rw [hm]; rfl
  have hread : (evm.accountMap.get? I.codeOwner |>.option (⟨0⟩ : UInt256)
      (fun ac => ac.storage.getD (poolLiquiditySlot id) ⟨0⟩)) = poolLiquidityPacked evm id :=
    (storageLoad_codeOwner_eq_solcSlotWordAt evm I _ (by rw [hI])).symm
  have hs : UInt256.signextend (UInt256.ofNat 15) (EVM.wordOfInt delta) = EVM.wordOfInt delta :=
    signextend128_wordOfInt hd.1 hd.2
  obtain ⟨k1, C1, rd1⟩ := poolManagerBlocks.poolManager_block_6461 (by omega)
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
  simp only [poolManagerBlocks.poolManager_block_6461_stack, hslot, hread, hs] at rd1
  have hadd := liquidityAddTrace v (by simp only [List.length_cons]; omega) (poolLiquidity_bound evm id)
    hd.1 hd.2 (by rw [deployedRuntime_jumps]; jump_dest) rd1
  by_cases hf : liquidityAddFits (poolLiquidityWord evm id) delta
  · rw [poolModifyLiquidityResult, if_pos hf]
    rw [if_pos hf] at hadd
    obtain ⟨k2, C2, rd2⟩ := hadd
    by_cases hp : evm.executionEnv.perm = false
    · rw [if_pos hp]
      exact poolModifyLiquidityStatic (by simp only [List.length_cons]; omega) (by rw [← hI]; exact hp) rd2
    · rw [if_neg hp]
      obtain ⟨k3, C3, rd3⟩ := poolManagerBlocks.poolManager_block_6524
        (by simp only [List.length_cons]; omega) (by rw [← hI]; exact Bool.eq_true_of_not_eq_false hp)
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd2
      have hclean := u256LandMaskCleanOfToNat (liquidityAddResultWord (poolLiquidityWord evm id) delta)
        (UInt256.ofNat (2^128-1)) rfl (liquidityAddResultWord_bound hf)
      change UInt256.land (EVM.wordOfInt (Int.ofNat (poolLiquidityWord evm id).toNat+delta))
        (UInt256.ofNat 340282366920938463463374607431768211455) = _ at hclean
      simp only [poolManagerBlocks.poolManager_block_6524_stack, hread, hclean] at rd3
      rw [u256_land_comm (poolLiquidityPacked evm id)
        (UInt256.ofNat 115792089237316195423570985008687907852929702298719625575994209400481361428480)] at rd3
      have haccts : (poolLiquidityStore evm id (liquidityAddResultWord (poolLiquidityWord evm id) delta)).accountMap =
          sstoreAccountMap I.codeOwner evm.accountMap (poolLiquiditySlot id)
            (wordLowSet (poolLiquidityPacked evm id) (liquidityAddResultWord (poolLiquidityWord evm id) delta) 128) := by
        rw [poolLiquidityStore, storageStore_accountMap, hI]
      refine ⟨?_, ?_, k3, C3, ?_⟩
      · exact (storageStore_executionEnv _ _ _ _).trans hI
      · exact storageStore_σ₀ _ _ _ _
      · rw [haccts]
        exact rd3
  · rw [poolModifyLiquidityResult, if_neg hf]
    rw [if_neg hf] at hadd
    exact hadd

theorem poolModifyLiquidityTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id amount0 amount1 : UInt256} {delta : Int}
    {k C : Nat} {R : List UInt256} (f : Frame)
    (v : PoolManagerImmutables) (hstack : R.length+8 ≤ 1024) (hI : evm.executionEnv = I)
    (hm : memLoad (UInt256.ofNat 128) mem = poolSlot id) (hd : signedFits ⟨128, by decide⟩ delta)
    (h : RD (deployedRuntime v) I g s0 ⟨6461⟩
      (amount1 :: amount0 :: EVM.wordOfInt delta :: R) mem aw rdata evm.accountMap k C) :
    blockResultTrace (deployedRuntime v) g s0 (fun _ post =>
      post.executionEnv = I ∧ post.σ₀ = evm.σ₀ ∧ ∃ aw' k' C',
        RD (deployedRuntime v) I g s0 ⟨6390⟩ (balanceDeltaWord amount0 amount1 :: R)
          mem aw' rdata post.accountMap k' C') (fun _ _ => False)
      (poolModifyLiquidityResult f evm id delta) := by
  have hr := poolModifyLiquidityExactTrace f v hstack hI hm hd h
  apply blockResultTrace_mono hr
  intro f' post _ ht
  exact ⟨ht.1, ht.2.1, _, ht.2.2⟩

end Benchmarks.UniswapV4PoolManager
