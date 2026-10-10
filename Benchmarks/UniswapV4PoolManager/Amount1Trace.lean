import Benchmarks.UniswapV4PoolManager.Amount1Words
import Benchmarks.UniswapV4PoolManager.FullMath96Trace
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_065
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_038

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem amount1Trace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw a b liquidity ret : UInt256} {roundUp : Bool}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+14 ≤ 1024)
    (ha : a.toNat < 2^160) (hb : b.toNat < 2^160) (hl : liquidity.toNat < 2^128)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 (if roundUp then ⟨23010⟩ else ⟨23101⟩)
      (a :: b :: liquidity :: ret :: R) mem aw rdata σ k C) :
    if amount1Fits a b liquidity then ∃ k' C', RD (deployedRuntime v) I g s0 ret
      (amount1Word a b liquidity roundUp :: R) mem aw rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  have hac := u256LandMaskCleanOfToNat a (UInt256.ofNat 1461501637330902918203684832716283019655932542975) rfl ha
  have hbc := u256LandMaskCleanOfToNat b (UInt256.ofNat 1461501637330902918203684832716283019655932542975) rfl hb
  have hlc := u256LandMaskCleanOfToNat liquidity (UInt256.ofNat 340282366920938463463374607431768211455) rfl hl
  have hab := absDiffWord_compiled (a := a) (b := b) (by omega) (by omega)
  cases roundUp with
  | false =>
    have rd1 := poolManagerBlocks.poolManager_block_23101
      (by simp only [List.length_cons]; omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    simp only [poolManagerBlocks.poolManager_block_23101_stack, hac, hbc, hlc, hab] at rd1
    have ht := fullMath96Trace v (by change R.length+1+9 ≤ 1024; omega)
      (by rw [poolManagerPatchedValidJumps v]; jump_dest) rd1
    by_cases hfit : amount1Fits a b liquidity
    · rw [if_pos hfit] at ht ⊢
      obtain ⟨k2, C2, rd2⟩ := ht
      rw [amount1Word_down]
      exact ⟨_, _, poolManagerBlocks.poolManager_block_13903
        (by change R.length+2 ≤ 1024; omega) hret rd2⟩
    · rw [if_neg hfit] at ht ⊢
      exact ht
  | true =>
    have rd1 := poolManagerBlocks.poolManager_block_23010
      (by simp only [List.length_cons]; omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    simp only [poolManagerBlocks.poolManager_block_23010_stack, hac, hbc, hlc, hab] at rd1
    have ht := fullMath96Trace v (by change R.length+5+9 ≤ 1024; omega)
      (by rw [poolManagerPatchedValidJumps v]; jump_dest) rd1
    by_cases hfit : amount1Fits a b liquidity
    · rw [if_pos hfit] at ht ⊢
      obtain ⟨k2, C2, rd2⟩ := ht
      rw [amount1Word_up]
      exact ⟨_, _, poolManagerBlocks.poolManager_block_23092
        (by change R.length+6 ≤ 1024; omega) hret rd2⟩
    · rw [if_neg hfit] at ht ⊢
      exact ht

end Benchmarks.UniswapV4PoolManager
