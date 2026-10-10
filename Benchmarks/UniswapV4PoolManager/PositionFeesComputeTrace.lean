import Benchmarks.UniswapV4PoolManager.PositionFeesSource
import Benchmarks.UniswapV4PoolManager.FullMath128Trace
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_018

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def positionFeesStoreStack (evm : State) (id key liquidity fee0 fee1 r0 r1 : UInt256) (R : List UInt256) : List UInt256 :=
  positionFeesOwed evm id key liquidity fee1 true :: fee0 :: positionFeeSlot id key true :: fee1 ::
    positionFeesOwed evm id key liquidity fee0 false :: r0 :: r1 :: positionFeeSlot id key false :: R

theorem positionFeesComputeTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id key liquidity fee0 fee1 r0 r1 : UInt256} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+18 ≤ 1024) (hI : evm.executionEnv = I)
    (h : RD (deployedRuntime v) I g s0 ⟨5950⟩
      (liquidity :: fee1 :: positionSlot id key :: r0 :: r1 :: fee0 :: R) mem aw rdata evm.accountMap k C) :
    if fullMath128Fits (positionFeeDifference evm id key fee0 false) liquidity then
      if fullMath128Fits (positionFeeDifference evm id key fee1 true) liquidity then
        ∃ k' C', RD (deployedRuntime v) I g s0 ⟨5985⟩
          (positionFeesStoreStack evm id key liquidity fee0 fee1 r0 r1 R) mem aw rdata evm.accountMap k' C'
      else RDrev (deployedRuntime v) g s0
    else RDrev (deployedRuntime v) g s0 := by
  have hread (slot : UInt256) :
      (evm.accountMap.get? I.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD slot ⟨0⟩)) =
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot :=
    (storageLoad_codeOwner_eq_solcSlotWordAt evm I slot (by rw [hI])).symm
  obtain ⟨k1, C1, rd1⟩ := poolManagerBlocks.poolManager_block_5950
    (by change R.length+13 ≤ 1024; omega)
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
  simp only [poolManagerBlocks.poolManager_block_5950_stack, hread] at rd1
  have hfirst := fullMath128Trace v (by simp only [List.length_cons]; omega)
    (by rw [poolManagerPatchedValidJumps v]; jump_dest) rd1
  change (if fullMath128Fits (positionFeeDifference evm id key fee0 false) liquidity then _ else _) at hfirst
  by_cases hf0 : fullMath128Fits (positionFeeDifference evm id key fee0 false) liquidity
  · rw [if_pos hf0] at hfirst ⊢
    obtain ⟨k2, C2, rd2⟩ := hfirst
    obtain ⟨k3, C3, rd3⟩ := poolManagerBlocks.poolManager_block_5973
      (by simp only [List.length_cons]; omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd2
    simp only [poolManagerBlocks.poolManager_block_5973_stack, hread] at rd3
    have hsecond := fullMath128Trace v (by simp only [List.length_cons]; omega)
      (by rw [poolManagerPatchedValidJumps v]; jump_dest) rd3
    change (if fullMath128Fits (positionFeeDifference evm id key fee1 true) liquidity then _ else _) at hsecond
    by_cases hf1 : fullMath128Fits (positionFeeDifference evm id key fee1 true) liquidity
    · rw [if_pos hf1] at hsecond ⊢
      obtain ⟨k4, C4, rd4⟩ := hsecond
      exact ⟨k4, C4, rd4⟩
    · rw [if_neg hf1] at hsecond ⊢
      exact hsecond
  · rw [if_neg hf0] at hfirst ⊢
    exact hfirst

end Benchmarks.UniswapV4PoolManager
