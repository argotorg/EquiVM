import Benchmarks.UniswapV4PoolManager.ExttloadArrayTrace
import Benchmarks.UniswapV4PoolManager.WordArrayTraceReturn

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 3000

theorem exttloadArrayPrepareTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} {n : Nat} (v : PoolManagerImmutables)
    (hstack : R.length + 9 ≤ 1024) (hn : n ≤ solcMaxU64)
    (h : RD (deployedRuntime v) I g s0 ⟨2879⟩
      (UInt256.ofNat n :: UInt256.ofNat (36+(calldataWord I.calldata 4).toNat) :: R)
      entryMemory aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨2914⟩ (exttloadArrayStack I n 0 R)
      (arrayHeaderMemory n) aw' rdata σ k' C' := by
  obtain ⟨aw1, k1, C1, rd⟩ := poolManagerBlocks.poolManager_block_2879_packed (by omega) h
  have hs : UInt256.shiftLeft (UInt256.ofNat n) (UInt256.ofNat 5) = UInt256.ofNat (32*n) :=
    shiftLeft5_ofNat_eq (n := n) (by norm_num [solcMaxU64, UInt256.size] at hn ⊢; omega)
  have hf : memLoad (UInt256.ofNat 64) entryMemory = UInt256.ofNat 160 := entryMemory_load64
  refine ⟨aw1, k1, C1, ?_⟩
  simpa only [poolManagerBlocks.poolManager_block_2879_stack,
    poolManagerBlocks.poolManager_block_2879_memory, hf, hs, ofNat_add_words,
    show 160+32*n+64 = 224+32*n by omega,
    exttloadArrayStack, wordArrayTraceStack, wordReadTraceStack, wordArrayTraceCursor, arrayHeaderMemory, Reasoning.Theory.writeWord, Nat.mul_zero, Nat.add_zero] using rd

theorem exttloadArrayTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} {n : Nat} (v : PoolManagerImmutables)
    (hstack : R.length + 9 ≤ 1024) (hn : n ≤ solcMaxU64)
    (ho : (calldataWord I.calldata 4).toNat ≤ solcMaxU64)
    (h : RD (deployedRuntime v) I g s0 ⟨2879⟩
      (UInt256.ofNat n :: UInt256.ofNat (36+(calldataWord I.calldata 4).toNat) :: R)
      entryMemory aw rdata σ k C) :
    RDret (deployedRuntime v) g s0 σ
      (wordBytes ([UInt256.ofNat 32, UInt256.ofNat n] ++ wordArrayWords (exttloadTraceValue I σ) 0 n)) := by
  obtain ⟨aw1, k1, C1, rd⟩ := exttloadArrayPrepareTrace v hstack hn h
  exact wordArrayTraceReturn v hstack hn
    (fun _ _ _ _ _ hi h => exttloadArrayTraceStep v hstack hn ho hi h) rd

end Benchmarks.UniswapV4PoolManager
