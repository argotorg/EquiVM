import Benchmarks.UniswapV3.Pool.BoundedActiveWords
import Benchmarks.UniswapV3.Pool.SwapCacheHeadTrace
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_013

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def swapStateTailMem (mem : ByteArray) (cursor growth liquidity : UInt256) : ByteArray :=
  writeWord (writeWord (writeWord mem cursor.toNat growth)
    (UInt256.ofNat 32 + cursor).toNat ⟨0⟩)
    (UInt256.ofNat 32 + (UInt256.ofNat 32 + cursor)).toNat liquidity

theorem swapStateTailMemory_eq (mem : ByteArray) (cursor growth liquidity cache : UInt256)
    (hl : UInt256.land (UInt256.ofNat (2 ^ 128 - 1))
      (memLoad (UInt256.ofNat 32 + cache)
        (writeWord (writeWord mem cursor.toNat growth)
          (UInt256.ofNat 32 + cursor).toNat ⟨0⟩)) = liquidity) :
    uniswapV3Pool_block_2950_memory (mem := mem) (x0 := growth) (x1 := cursor) (x5 := cache) =
      swapStateTailMem mem cursor growth liquidity := by
  have hz : UInt256.land (UInt256.ofNat (2 ^ 128 - 1)) (UInt256.ofNat 0) = ⟨0⟩ := rfl
  simp only [uniswapV3Pool_block_2950_memory, solcMask128, hz]
  change writeWord (writeWord (writeWord mem cursor.toNat growth)
    (UInt256.ofNat 32 + cursor).toNat ⟨0⟩)
    (UInt256.ofNat 32 + (UInt256.ofNat 32 + cursor)).toNat
    (UInt256.land (UInt256.ofNat (2 ^ 128 - 1))
      (memLoad (UInt256.ofNat 32 + cache)
        (writeWord (writeWord mem cursor.toNat growth)
          (UInt256.ofNat 32 + cursor).toNat ⟨0⟩))) = _
  rw [hl]
  rfl

theorem swapStateTailBoundedX {limit : Nat} {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw cursor growth liquidity cache state x3 exact : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨2950⟩
      (growth :: cursor :: state :: x3 :: exact :: cache :: R) mem aw rdata σ k C)
    (hl : UInt256.land (UInt256.ofNat (2 ^ 128 - 1))
      (memLoad (UInt256.ofNat 32 + cache)
        (writeWord (writeWord mem cursor.toNat growth)
          (UInt256.ofNat 32 + cursor).toNat ⟨0⟩)) = liquidity)
    (ha : BoundedActiveWords aw limit) (hb : cursor.toNat + 96 ≤ limit)
    (hc : cache.toNat + 64 ≤ limit) (hov : R.length + 9 ≤ 1024) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ⟨2991⟩ (state :: exact :: cache :: R)
      (swapStateTailMem mem cursor growth liquidity) aw' rdata σ k' C' ∧
      BoundedActiveWords aw' limit ∧
      cursor.toNat + 96 ≤ aw'.toNat * 32 + 32 := by
  have hsmall := ha.small
  have r1 := uniswapV3Pool_block_2950 (immWords := wordsOf (immStore v)) hov rd
  rw [swapStateTailMemory_eq mem cursor growth liquidity cache hl] at r1
  have h32 : (UInt256.ofNat 32 + cursor).toNat = cursor.toNat + 32 := by
    rw [u256_add_comm]
    exact uadd_word_ofNat_toNat cursor 32 (by change _ < 2 ^ 256; omega)
  have h64 : (UInt256.ofNat 32 + (UInt256.ofNat 32 + cursor)).toNat = cursor.toNat + 64 := by
    rw [u256_add_comm, uadd_word_ofNat_toNat _ 32 (by rw [h32]; change _ < 2 ^ 256; omega), h32]
  have hc32 : (UInt256.ofNat 32 + cache).toNat = cache.toNat + 32 := by
    rw [u256_add_comm]
    exact uadd_word_ofNat_toNat cache 32 (by change _ < 2 ^ 256; omega)
  have ha1 := ha.expand32 (off := cursor) (by omega)
  have ha2 := ha1.expand32 (off := UInt256.ofNat 32 + cursor) (by rw [h32]; omega)
  have ha3 := ha2.expand32 (off := UInt256.ofNat 32 + cache) (by rw [hc32]; omega)
  have ha4 := ha3.expand32 (off := UInt256.ofNat 32 + (UInt256.ofNat 32 + cursor))
    (by rw [h64]; omega)
  have hcover := expandedWords32_cover ha3.active
    (off := UInt256.ofNat 32 + (UInt256.ofNat 32 + cursor)) (by rw [h64]; omega)
  rw [h64] at hcover
  exact ⟨_, _, _, r1, ha4, by dsimp only [M, expandedWords] at hcover ⊢; omega⟩

theorem swapStateTailX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw cursor growth liquidity cache state x3 exact : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨2950⟩
      (growth :: cursor :: state :: x3 :: exact :: cache :: R) mem aw rdata σ k C)
    (hl : UInt256.land (UInt256.ofNat (2 ^ 128 - 1))
      (memLoad (UInt256.ofNat 32 + cache)
        (writeWord (writeWord mem cursor.toNat growth)
          (UInt256.ofNat 32 + cursor).toNat ⟨0⟩)) = liquidity)
    (ha : ActiveWords aw) (hb : cursor.toNat + 96 ≤ 2 ^ 200)
    (hc : cache.toNat + 64 ≤ 2 ^ 200) (hov : R.length + 9 ≤ 1024) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ⟨2991⟩ (state :: exact :: cache :: R)
      (swapStateTailMem mem cursor growth liquidity) aw' rdata σ k' C' ∧ ActiveWords aw' := by
  obtain ⟨aw', k', C', rd', ha', _⟩ := swapStateTailBoundedX (v := v)
    rd hl (BoundedActiveWords.of_active ha) hb hc hov
  exact ⟨aw', k', C', rd', ha'.active⟩

end Benchmarks.UniswapV3.Pool
