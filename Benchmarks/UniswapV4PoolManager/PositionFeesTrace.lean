import Benchmarks.UniswapV4PoolManager.PositionFeesComputeTrace
import Benchmarks.UniswapV4PoolManager.PositionStoreStatic
import Benchmarks.UniswapV4PoolManager.FunctionResultTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def positionUpdateReturnTrace (v : PoolManagerImmutables) (I : ExecutionEnv) (g : Sat256) (s0 : State)
    (σ₀ : AccountMap) (mem rdata : ByteArray) (aw r0 r1 : UInt256) (R : List UInt256)
    (post : State) (values : Option (List Value)) : Prop :=
  post.executionEnv = I ∧ post.σ₀ = σ₀ ∧ ∃ owed0 owed1 : UInt256,
    values = some [.int (Int.ofNat owed0.toNat), .int (Int.ofNat owed1.toNat)] ∧
      ∃ k C, RD (deployedRuntime v) I g s0 ⟨12458⟩ (owed0 :: r0 :: r1 :: owed1 :: R)
        mem aw rdata post.accountMap k C

theorem positionFeesStoreTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id key fee0 fee1 owed0 owed1 r0 r1 : UInt256} {k C : Nat} {R : List UInt256}
    (f : Frame) (v : PoolManagerImmutables) (hstack : R.length+8 ≤ 1024) (hI : evm.executionEnv = I)
    (h : RD (deployedRuntime v) I g s0 ⟨5985⟩
      (owed1 :: fee0 :: positionFeeSlot id key true :: fee1 :: owed0 :: r0 :: r1 :: positionFeeSlot id key false :: R)
      mem aw rdata evm.accountMap k C) :
    functionResultTrace (deployedRuntime v) g s0
      (positionUpdateReturnTrace v I g s0 evm.σ₀ mem rdata aw r0 r1 R)
      (positionFeesStoreResult f evm id key fee0 fee1 owed0 owed1) := by
  simp only [positionFeesStoreResult]
  by_cases hp : evm.executionEnv.perm = false
  · rw [if_pos hp]
    exact positionFeesStoreStatic hstack (by rw [← hI]; exact hp) h
  · rw [if_neg hp]
    obtain ⟨k1, C1, rd1⟩ := poolManagerBlocks.poolManager_block_5985 hstack
      (by rw [← hI]; exact Bool.eq_true_of_not_eq_false hp)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    simp only [poolManagerBlocks.poolManager_block_5985_stack] at rd1
    have haccts : (positionFeeStores evm id key fee0 fee1).accountMap =
        sstoreAccountMap I.codeOwner (sstoreAccountMap I.codeOwner evm.accountMap (positionFeeSlot id key false) fee0)
          (positionFeeSlot id key true) fee1 := by
      simp only [positionFeeStores, storageStore_accountMap, storageStore_executionEnv, hI]
    refine ⟨?_, ?_, owed0, owed1, rfl, k1, C1, ?_⟩
    · simp only [positionFeeStores, storageStore_executionEnv, hI]
    · simp only [positionFeeStores, storageStore_σ₀]
    · rw [haccts]
      exact rd1

theorem positionFeesTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id key liquidity fee0 fee1 r0 r1 : UInt256} {k C : Nat} {R : List UInt256}
    (f : Frame) (v : PoolManagerImmutables) (hstack : R.length+18 ≤ 1024) (hI : evm.executionEnv = I)
    (h : RD (deployedRuntime v) I g s0 ⟨5950⟩
      (liquidity :: fee1 :: positionSlot id key :: r0 :: r1 :: fee0 :: R) mem aw rdata evm.accountMap k C) :
    functionResultTrace (deployedRuntime v) g s0
      (positionUpdateReturnTrace v I g s0 evm.σ₀ mem rdata aw r0 r1 R)
      (positionFeesResult f evm id key liquidity fee0 fee1) := by
  have hr := positionFeesComputeTrace v hstack hI h
  simp only [positionFeesResult]
  by_cases hf0 : fullMath128Fits (positionFeeDifference evm id key fee0 false) liquidity
  · rw [if_pos hf0] at hr ⊢
    by_cases hf1 : fullMath128Fits (positionFeeDifference evm id key fee1 true) liquidity
    · rw [if_pos hf1] at hr ⊢
      obtain ⟨k1, C1, rd1⟩ := hr
      exact positionFeesStoreTrace f v (by omega) hI rd1
    · rw [if_neg hf1] at hr ⊢
      exact hr
  · rw [if_neg hf0] at hr ⊢
    exact hr

end Benchmarks.UniswapV4PoolManager
