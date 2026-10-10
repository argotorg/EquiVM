import Benchmarks.UniswapV3.Pool.UpdatePositionEntryTrace
import Benchmarks.UniswapV3.Pool.ObserveInputTrace
import Benchmarks.UniswapV3.Pool.BlockTimestamp

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def updatePositionObserveWords (σ : AccountMap) (ee : ExecutionEnv) : List UInt256 :=
  [slot0FieldWord 25 2 σ ee, poolLiquidityWord σ ee, slot0FieldWord 23 2 σ ee,
    EVM.wordOfInt (slot0TickValue σ ee), ⟨0⟩, UInt256.ofNat ee.header.timestamp, ⟨8⟩]

theorem updatePositionObserveEntryX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨19190⟩ R mem aw rdata σ k C)
    (hov : R.length + 15 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨13193⟩
      (updatePositionObserveWords σ ee ++
        UInt256.ofNat 19273 :: ⟨0⟩ :: ⟨0⟩ :: UInt256.ofNat ee.header.timestamp :: R)
      mem aw rdata σ k' C' := by
  have r1 := uniswapV3Pool_block_19190 (immWords := wordsOf (immStore v)) (by evm_ov)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
  obtain ⟨_, _, r2⟩ := blockTimestampX (v := v) r1
    (by rw [uniswapV3PoolPatchedValidJumps v]; jump_dest) (by evm_ov)
  obtain ⟨_, _, r3⟩ := uniswapV3Pool_block_19199 (immWords := wordsOf (immStore v)) (by evm_ov)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r2
  obtain ⟨hc, hl⟩ := observeStorageArgs σ ee
  have ht := slot0TickWord σ ee
  have hi := slot0FieldShift 23 2
    (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 184)) (UInt256.ofNat 65535) σ ee
    (by native_decide) (by decide)
  simp only [solcSlotWordAt, solcSlotWord] at hc hl ht hi
  simp only [uniswapV3Pool_block_19199_stack,
    show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl,
    show UInt256.ofNat 4 = (⟨4⟩ : UInt256) from rfl, hc, hl, ← ht, ← hi] at r3
  exact ⟨_, _, r3⟩

end Benchmarks.UniswapV3.Pool
