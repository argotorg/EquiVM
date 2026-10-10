import Benchmarks.UniswapV3.Pool.UpdatePositionTickModel
import Benchmarks.UniswapV3.Pool.UpdatePositionObserveTrace
import Benchmarks.UniswapV3.Pool.TickUpdateMaskedTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def updatePositionTickSavedWords (v : UniswapV3PoolImmutables) (a : UpdatePositionArgs)
    (evm : EVM.State) (upper : Bool) : List UInt256 :=
  [(snapshotCurrent evm.accountMap evm.executionEnv).secondsPerLiquidity,
    EVM.wordOfInt (snapshotCurrent evm.accountMap evm.executionEnv).tickCumulative,
    UInt256.ofNat evm.executionEnv.header.timestamp, ⟨0⟩,
    if upper then (updatePositionFlipped v a evm false).toUInt256 else ⟨0⟩,
    feeGrowthWord true evm.accountMap evm.executionEnv,
    feeGrowthWord false evm.accountMap evm.executionEnv,
    solcMappingSlot ⟨7⟩ (updatePositionKey a), EVM.wordOfInt a.current, EVM.wordOfInt a.delta,
    EVM.wordOfInt a.upper, EVM.wordOfInt a.lower, EVM.word a.owner.val]

def updatePositionTickEntryWords (v : UniswapV3PoolImmutables) (a : UpdatePositionArgs)
    (evm : EVM.State) (upper : Bool) : List UInt256 :=
  if upper then
    (updatePositionFlipped v a evm false).toUInt256 :: updatePositionTickSavedWords v a evm false
  else
    [(snapshotCurrent evm.accountMap evm.executionEnv).secondsPerLiquidity,
      EVM.wordOfInt (snapshotCurrent evm.accountMap evm.executionEnv).tickCumulative,
      ⟨0⟩, ⟨0⟩, UInt256.ofNat evm.executionEnv.header.timestamp] ++
      updatePositionPrefixWords a evm.accountMap evm.executionEnv

def updatePositionTickEntryPC (upper : Bool) : UInt256 := if upper then ⟨19331⟩ else ⟨19273⟩

def updatePositionTickReturnPC (upper : Bool) : UInt256 := if upper then ⟨19386⟩ else ⟨19331⟩

theorem updatePositionTickEntryX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (a : UpdatePositionArgs) (evm : EVM.State) (upper : Bool)
    (rd : RD (deployedRuntime v) ee g s0 (updatePositionTickEntryPC upper)
      (updatePositionTickEntryWords v a evm upper ++ R) mem aw rdata σ k C)
    (hov : R.length + 27 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨20795⟩
      (tickUpdateWords ((updatePositionTickArgs v a evm upper).withRaw
        (UInt256.ofNat evm.executionEnv.header.timestamp) v.maxLiquidityPerTick) ++
        updatePositionTickReturnPC upper :: updatePositionTickSavedWords v a evm upper ++ R)
      mem aw rdata σ k' C' := by
  cases upper
  · simp only [updatePositionTickEntryPC, updatePositionTickEntryWords,
      Bool.false_eq_true, if_false, List.cons_append, List.nil_append,
      updatePositionPrefixWords] at rd
    have r1 := uniswapV3Pool_block_19273 (immWords := wordsOf (immStore v))
      (by evm_ov) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    simp only [uniswapV3Pool_block_19273_stack, wordsOf_immStore_maxLiquidityPerTick,
      wordOfInt_ofNat_toNat] at r1
    refine ⟨k + 20, C + 61, ?_⟩
    simpa only [tickUpdateWords, TickUpdateArgs.withRaw, updatePositionTickArgs,
      updatePositionTickReturnPC, updatePositionTickSavedWords, Bool.false_eq_true, if_false,
      List.cons_append, List.nil_append] using r1
  · simp only [updatePositionTickEntryPC, updatePositionTickEntryWords, if_true,
      updatePositionTickSavedWords, Bool.false_eq_true, if_false,
      List.cons_append, List.nil_append] at rd
    have r1 := uniswapV3Pool_block_19331 (immWords := wordsOf (immStore v))
      (by evm_ov) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    simp only [uniswapV3Pool_block_19331_stack, wordsOf_immStore_maxLiquidityPerTick,
      wordOfInt_ofNat_toNat] at r1
    refine ⟨k + 17, C + 53, ?_⟩
    simpa only [tickUpdateWords, TickUpdateArgs.withRaw, updatePositionTickArgs,
      updatePositionTickReturnPC, updatePositionTickSavedWords, if_true,
      List.cons_append, List.nil_append] using r1

end Benchmarks.UniswapV3.Pool
