import Benchmarks.UniswapV4PoolManager.PositionUpdateSource
import Benchmarks.UniswapV4PoolManager.PositionStoreStatic
import Benchmarks.UniswapV4PoolManager.LiquidityAddTrace
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_018
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_020

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def positionUpdateInputStack (evm : State) (id key : UInt256) (delta : Int)
    (fee0 upper x0 x1 x2 x3 x4 x5 lower x9 fee1 : UInt256) (R : List UInt256) : List UInt256 :=
  fee0 :: upper :: EVM.wordOfInt delta :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 ::
    positionSlot id key :: positionLiquidityWord evm id key :: lower :: x9 :: fee1 :: R

def positionUpdateContinuation (delta : Int) (upper x0 x1 x2 x3 x4 x5 lower x9 : UInt256)
    (R : List UInt256) : List UInt256 :=
  upper :: EVM.wordOfInt delta :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 ::
    ⟨6222⟩ :: ⟨6240⟩ :: lower :: x9 :: ⟨64⟩ :: R

theorem positionChangeState_env (evm : State) (id key liquidity : UInt256) (delta : Int) :
    (positionChangeState evm id key liquidity delta).executionEnv = evm.executionEnv := by
  unfold positionChangeState
  split
  · rfl
  · exact storageStore_executionEnv _ _ _ _

theorem positionChangeState_original (evm : State) (id key liquidity : UInt256) (delta : Int) :
    (positionChangeState evm id key liquidity delta).σ₀ = evm.σ₀ := by
  unfold positionChangeState
  split
  · rfl
  · exact storageStore_σ₀ _ _ _ _

theorem positionLiquidityTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id key fee0 upper x0 x1 x2 x3 x4 x5 lower x9 fee1 : UInt256} {delta : Int}
    {k C : Nat} {R : List UInt256} (v : PoolManagerImmutables) (hstack : R.length+25 ≤ 1024)
    (hI : evm.executionEnv = I) (hlo : -(2^127 : Int) ≤ delta) (hhi : delta < 2^127)
    (h : RD (deployedRuntime v) I g s0 ⟨5915⟩
      (positionUpdateInputStack evm id key delta fee0 upper x0 x1 x2 x3 x4 x5 lower x9 fee1 R)
      mem aw rdata evm.accountMap k C) :
    if positionChangeReverts (positionLiquidityWord evm id key) delta then RDrev (deployedRuntime v) g s0 else
      if delta ≠ 0 ∧ evm.executionEnv.perm = false then RDstatic (deployedRuntime v) g s0 else
        ∃ k' C', RD (deployedRuntime v) I g s0 ⟨5950⟩
          (positionLiquidityWord evm id key :: fee1 :: positionSlot id key :: ⟨5993⟩ :: ⟨5999⟩ :: fee0 ::
            positionUpdateContinuation delta upper x0 x1 x2 x3 x4 x5 lower x9 R)
          mem aw rdata (positionChangeState evm id key (positionLiquidityWord evm id key) delta).accountMap k' C' := by
  have hsign : UInt256.signextend (UInt256.ofNat 15) (EVM.wordOfInt delta) = EVM.wordOfInt delta :=
    signextend128_wordOfInt hlo hhi
  by_cases hz : delta = 0
  · have hd : EVM.wordOfInt delta = ⟨0⟩ := by rw [hz, wordOfInt_zero]
    have rd1 := poolManagerBlocks.poolManager_block_5915_fallthrough
      (by simp only [List.length_cons]; omega) (by rw [hsign, hd]; decide) h
    by_cases hlz : positionLiquidityWord evm id key = ⟨0⟩
    · simp only [positionChangeReverts, if_pos hz, if_pos hlz]
      have rd2 := poolManagerBlocks.poolManager_block_5926_taken
        (by simp only [List.length_cons]; omega) (by rw [hlz]; decide)
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
      exact poolManagerBlocks.poolManager_block_6730 (by simp only [List.length_cons]; omega) rd2
    · simp only [positionChangeReverts, if_neg hlz, ne_eq, hz, not_true_eq_false, false_and,
        if_false, positionChangeState, if_true]
      have rd2 := poolManagerBlocks.poolManager_block_5926_fallthrough
        (by simp only [List.length_cons]; omega) (isZero_eq_zero_of_ne hlz) rd1
      have rd3 := poolManagerBlocks.poolManager_block_5932 (by change R.length+19 ≤ 1024; omega) rd2
      simp only [poolManagerBlocks.poolManager_block_5932_stack, hz] at rd3
      exact ⟨_, _, rd3⟩
  · have hd : EVM.wordOfInt delta ≠ ⟨0⟩ := by
      intro he
      have hs := signed_wordOfInt (i := delta) (show int256Fits delta from ⟨by change -(2^255 : Int) ≤ delta; omega,
        by change delta < (2^255 : Int); omega⟩)
      rw [he] at hs
      exact hz hs.symm
    have rd1 := poolManagerBlocks.poolManager_block_5915_taken
      (by simp only [List.length_cons]; omega)
      (by rw [hsign, isZero_eq_zero_of_ne hd, uInt256_eq_self]; decide)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    have rd2 := poolManagerBlocks.poolManager_block_6770 (by change R.length+24 ≤ 1024; omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
    simp only [poolManagerBlocks.poolManager_block_6770_stack, hsign] at rd2
    have hadd := liquidityAddTrace v (by simp only [List.length_cons]; omega)
      (positionLiquidity_bound evm id key) hlo hhi (by rw [poolManagerPatchedValidJumps]; jump_dest) rd2
    by_cases hfit : liquidityAddFits (positionLiquidityWord evm id key) delta
    · rw [if_pos hfit] at hadd
      simp only [positionChangeReverts, hfit, not_true_eq_false, if_false, ne_eq, hz,
        not_false_eq_true, true_and]
      obtain ⟨k3, C3, rd3⟩ := hadd
      by_cases hp : evm.executionEnv.perm = false
      · rw [if_pos hp]
        exact positionLiquidityStoreStatic (by simp only [List.length_cons]; omega) (by rw [← hI]; exact hp) rd3
      · rw [if_neg hp]
        obtain ⟨k4, C4, rd4⟩ := poolManagerBlocks.poolManager_block_6818
          (by simp only [List.length_cons]; omega) (by rw [← hI]; exact Bool.eq_true_of_not_eq_false hp)
          (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd3
        have hclean := u256LandMaskCleanOfToNat (liquidityAddResultWord (positionLiquidityWord evm id key) delta)
          (UInt256.ofNat (2^128-1)) rfl (liquidityAddResultWord_bound hfit)
        change UInt256.land (EVM.wordOfInt (Int.ofNat (positionLiquidityWord evm id key).toNat+delta))
          (UInt256.ofNat 340282366920938463463374607431768211455) = _ at hclean
        have hread : (evm.accountMap.get? I.codeOwner |>.option (⟨0⟩ : UInt256)
            (fun ac => ac.storage.getD (positionSlot id key) ⟨0⟩)) = positionPackedWord evm id key :=
          (storageLoad_codeOwner_eq_solcSlotWordAt evm I _ (by rw [hI])).symm
        have haccts : (positionChangeState evm id key (positionLiquidityWord evm id key) delta).accountMap =
            sstoreAccountMap I.codeOwner evm.accountMap (positionSlot id key)
              (wordLowSet (positionPackedWord evm id key)
                (liquidityAddResultWord (positionLiquidityWord evm id key) delta) 128) := by
          rw [positionChangeState, if_neg hz, positionLiquidityStore, storageStore_accountMap, hI]
        simp only [poolManagerBlocks.poolManager_block_6818_stack, hread] at rd4
        rw [hclean, u256_land_comm] at rd4
        rw [haccts]
        exact ⟨k4, C4, rd4⟩
    · rw [if_neg hfit] at hadd
      simpa only [positionChangeReverts, if_neg hz, hfit, not_false_eq_true, if_true] using hadd

end Benchmarks.UniswapV4PoolManager
