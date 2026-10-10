import Benchmarks.UniswapV4PoolManager.Amount0CoreTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem amount0UpTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw a b liquidity ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+16 ≤ 1024)
    (ha : a.toNat < 2^160) (hb : b.toNat < 2^160) (hl : liquidity.toNat < 2^128)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨23165⟩ (a :: b :: liquidity :: ret :: R) mem aw rdata σ k C) :
    if amount0Fits a b liquidity true then ∃ k' C', RD (deployedRuntime v) I g s0 ret
      (amount0Word a b liquidity true :: R) mem aw rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  have hca := u256LandMaskCleanOfToNat a (UInt256.ofNat 1461501637330902918203684832716283019655932542975) rfl ha
  have hcb := u256LandMaskCleanOfToNat b (UInt256.ofNat 1461501637330902918203684832716283019655932542975) rfl hb
  by_cases ho : b.toNat < a.toNat
  · have rd1 := poolManagerBlocks.poolManager_block_23165_taken
      (by change R.length+7 ≤ 1024; omega)
      (by rw [hca, hcb, ugt_one ho]; decide)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    have rd2 := poolManagerBlocks.poolManager_block_23342
      (by change R.length+5 ≤ 1024; omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
    have hc := amount0UpCoreTrace v hstack (Nat.le_of_lt ho) ha hl hret rd2
    simpa only [amount0Fits, amount0Word, amount0Lo, amount0Hi, if_pos ho] using hc
  · have rd1 := poolManagerBlocks.poolManager_block_23165_fallthrough
      (by change R.length+7 ≤ 1024; omega) (by rw [hca, hcb]; exact ugt_zero (Nat.le_of_not_gt ho)) h
    have hc := amount0UpCoreTrace v hstack (Nat.le_of_not_gt ho) hb hl hret rd1
    simpa only [amount0Fits, amount0Word, amount0Lo, amount0Hi, if_neg ho] using hc

theorem amount0DownTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw a b liquidity ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+13 ≤ 1024)
    (ha : a.toNat < 2^160) (hb : b.toNat < 2^160) (hl : liquidity.toNat < 2^128)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨23348⟩ (a :: b :: liquidity :: ret :: R) mem aw rdata σ k C) :
    if amount0Fits a b liquidity false then ∃ k' C', RD (deployedRuntime v) I g s0 ret
      (amount0Word a b liquidity false :: R) mem aw rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  have hca := u256LandMaskCleanOfToNat a (UInt256.ofNat 1461501637330902918203684832716283019655932542975) rfl ha
  have hcb := u256LandMaskCleanOfToNat b (UInt256.ofNat 1461501637330902918203684832716283019655932542975) rfl hb
  by_cases ho : b.toNat < a.toNat
  · have rd1 := poolManagerBlocks.poolManager_block_23348_taken
      (by change R.length+7 ≤ 1024; omega)
      (by rw [hca, hcb, ugt_one ho]; decide)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    have rd2 := poolManagerBlocks.poolManager_block_23509
      (by change R.length+5 ≤ 1024; omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
    have hc := amount0DownCoreTrace v hstack (Nat.le_of_lt ho) ha hl hret rd2
    simpa only [amount0Fits, amount0Word, amount0Lo, amount0Hi, if_pos ho] using hc
  · have rd1 := poolManagerBlocks.poolManager_block_23348_fallthrough
      (by change R.length+7 ≤ 1024; omega) (by rw [hca, hcb]; exact ugt_zero (Nat.le_of_not_gt ho)) h
    have hc := amount0DownCoreTrace v hstack (Nat.le_of_not_gt ho) hb hl hret rd1
    simpa only [amount0Fits, amount0Word, amount0Lo, amount0Hi, if_neg ho] using hc

end Benchmarks.UniswapV4PoolManager
