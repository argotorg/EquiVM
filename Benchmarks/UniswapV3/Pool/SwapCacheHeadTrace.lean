import Benchmarks.UniswapV3.Pool.BoundedActiveWords
import Benchmarks.UniswapV3.Pool.Slot0MemoryFields
import Benchmarks.UniswapV3.Pool.BlockTimestamp
import Benchmarks.UniswapV3.Pool.PoolLiquidityStorage
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_012

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem swapCacheFeeX {σ snap : AccountMap} {ee I : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p x0 x1 x2 : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables} (zero : Bool)
    (rd : RD (deployedRuntime v) ee g s0 (if zero then ⟨2770⟩ else ⟨2754⟩)
      (x0 :: x1 :: x2 :: p :: R) mem aw rdata σ k C)
    (hp : UInt256.land (UInt256.ofNat 255) (memLoad (UInt256.ofNat 160 + p) mem) =
      slot0FieldWord 29 1 snap I) (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨2789⟩
      (poolProtocolDivisor (!zero) snap I :: x0 :: x1 :: x2 :: p :: R)
      mem (M aw (UInt256.ofNat 160 + p) ⟨32⟩) rdata σ k' C' := by
  cases zero
  · have r1 := uniswapV3Pool_block_2754 (immWords := wordsOf (immStore v)) (by omega)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    simpa only [uniswapV3Pool_block_2754_stack, hp, slot0FeeProtocol_shr4] using RD.pack r1
  · have r1 := uniswapV3Pool_block_2770_taken (immWords := wordsOf (immStore v)) hov (by decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    simp only [uniswapV3Pool_block_2770_taken_stack] at r1
    have r2 := uniswapV3Pool_block_2787 (immWords := wordsOf (immStore v))
      (by change R.length + 4 + 2 ≤ 1024; omega) r1
    simpa only [uniswapV3Pool_block_2787_stack, hp, slot0FeeProtocol_mod16] using RD.pack r2

def swapCacheHeadMem (mem : ByteArray) (p fee : UInt256) (σ : AccountMap) (I : ExecutionEnv) :
    ByteArray :=
  writeWord (writeWord mem p.toNat fee) (p + UInt256.ofNat 32).toNat (poolLiquidityWord σ I)

theorem swapCacheHeadBoundedX {limit : Nat} {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p fee : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨2789⟩ (fee :: p :: R) mem aw rdata σ k C)
    (hf : UInt256.land (UInt256.ofNat 255) fee = fee) (ha : BoundedActiveWords aw limit)
    (hb : p.toNat + 64 ≤ limit) (hov : R.length + 5 ≤ 1024) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ⟨2822⟩
      (UInt256.ofNat ee.header.timestamp :: (UInt256.ofNat 64 + p) :: R)
      (swapCacheHeadMem mem p fee σ ee) aw' rdata σ k' C' ∧ BoundedActiveWords aw' limit := by
  have hsmall := ha.small
  obtain ⟨kr, Cr, rr⟩ := uniswapV3Pool_block_2789 (immWords := wordsOf (immStore v)) hov
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
  have hmem : uniswapV3Pool_block_2789_memory (ee := ee) (σ := σ) (mem := mem)
      (x0 := fee) (x1 := p) = swapCacheHeadMem mem p fee σ ee := by
    simp only [uniswapV3Pool_block_2789_memory, solcMask128, hf,
      swapCacheHeadMem, poolLiquidityWord, u256_land_comm, Reasoning.Theory.writeWord]
    rfl
  simp only [uniswapV3Pool_block_2789_stack, hmem] at rr
  obtain ⟨kt, Ct, rt⟩ := blockTimestampX (v := v) rr
    (by rw [uniswapV3PoolPatchedValidJumps v]; jump_dest)
    (by change R.length + 1 + 2 ≤ 1024; omega)
  have hp32 := uadd_word_ofNat_toNat p 32
    (show p.toNat + 32 < UInt256.size by change _ < 2 ^ 256; omega)
  exact ⟨_, kt, Ct, rt, BoundedActiveWords.expand32
    (BoundedActiveWords.expand32 ha (by omega)) (by rw [hp32]; omega)⟩

theorem swapCacheHeadX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p fee : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨2789⟩ (fee :: p :: R) mem aw rdata σ k C)
    (hf : UInt256.land (UInt256.ofNat 255) fee = fee) (ha : ActiveWords aw)
    (hb : p.toNat + 64 ≤ 2 ^ 200) (hov : R.length + 5 ≤ 1024) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ⟨2822⟩
      (UInt256.ofNat ee.header.timestamp :: (UInt256.ofNat 64 + p) :: R)
      (swapCacheHeadMem mem p fee σ ee) aw' rdata σ k' C' ∧ ActiveWords aw' := by
  obtain ⟨aw', k', C', rd', ha'⟩ := swapCacheHeadBoundedX (v := v)
    rd hf (BoundedActiveWords.of_active ha) hb hov
  exact ⟨aw', k', C', rd', ha'.active⟩

end Benchmarks.UniswapV3.Pool
