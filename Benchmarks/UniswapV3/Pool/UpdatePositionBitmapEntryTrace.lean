import Benchmarks.UniswapV3.Pool.UpdatePositionTickEntryTrace
import Benchmarks.UniswapV3.Pool.UpdatePositionBitmapModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def updatePositionBitmapWords (v : UniswapV3PoolImmutables) (a : UpdatePositionArgs)
    (evm : EVM.State) : List UInt256 :=
  [(snapshotCurrent evm.accountMap evm.executionEnv).secondsPerLiquidity,
    EVM.wordOfInt (snapshotCurrent evm.accountMap evm.executionEnv).tickCumulative,
    UInt256.ofNat evm.executionEnv.header.timestamp,
    (updatePositionFlipped v a evm true).toUInt256, (updatePositionFlipped v a evm false).toUInt256,
    feeGrowthWord true evm.accountMap evm.executionEnv,
    feeGrowthWord false evm.accountMap evm.executionEnv,
    solcMappingSlot ⟨7⟩ (updatePositionKey a), EVM.wordOfInt a.current, EVM.wordOfInt a.delta,
    EVM.wordOfInt a.upper, EVM.wordOfInt a.lower, EVM.word a.owner.val]

def updatePositionBitmapEntryWords (v : UniswapV3PoolImmutables) (a : UpdatePositionArgs)
    (evm : EVM.State) (upper : Bool) : List UInt256 :=
  if upper then updatePositionBitmapWords v a evm else
    (updatePositionFlipped v a evm true).toUInt256 :: updatePositionTickSavedWords v a evm true

def updatePositionBitmapEntryPC (upper : Bool) : UInt256 := if upper then ⟨19438⟩ else ⟨19386⟩
def updatePositionBitmapCallPC (upper : Bool) : UInt256 := if upper then ⟨19445⟩ else ⟨19395⟩
def updatePositionBitmapReturnPC (upper : Bool) : UInt256 := if upper then ⟨19488⟩ else ⟨19438⟩

theorem updatePositionBitmapGuardX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (a : UpdatePositionArgs) (evm : EVM.State) (upper : Bool)
    (rd : RD (deployedRuntime v) ee g s0 (updatePositionBitmapEntryPC upper)
      (updatePositionBitmapEntryWords v a evm upper ++ R) mem aw rdata σ k C)
    (hov : R.length + 15 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0
      (if updatePositionFlipped v a evm upper then updatePositionBitmapCallPC upper
        else updatePositionBitmapReturnPC upper)
      (updatePositionBitmapWords v a evm ++ R) mem aw rdata σ k' C' := by
  cases upper
  · simp only [updatePositionBitmapEntryPC, updatePositionBitmapEntryWords,
      updatePositionTickSavedWords, Bool.false_eq_true, if_false, if_true,
      List.cons_append, List.nil_append] at rd
    cases hf : updatePositionFlipped v a evm false
    · have r1 := uniswapV3Pool_block_19386_taken (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [hf]; decide)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
      refine ⟨k + 7, C + 25, ?_⟩
      simpa only [uniswapV3Pool_block_19386_taken_stack, updatePositionBitmapWords,
        updatePositionBitmapReturnPC, hf, Bool.false_eq_true, if_false,
        List.cons_append, List.nil_append] using r1
    · have r1 := uniswapV3Pool_block_19386_fallthrough (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [hf]; rfl) rd
      refine ⟨k + 7, C + 25, ?_⟩
      simpa only [uniswapV3Pool_block_19386_fallthrough_stack, updatePositionBitmapWords,
        updatePositionBitmapCallPC, hf, Bool.false_eq_true, if_false, if_true,
        List.cons_append, List.nil_append] using r1
  · simp only [updatePositionBitmapEntryPC, updatePositionBitmapEntryWords,
      updatePositionBitmapWords, if_true, List.cons_append, List.nil_append] at rd
    cases hf : updatePositionFlipped v a evm true
    · have r1 := uniswapV3Pool_block_19438_taken (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [hf]; decide)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
      refine ⟨k + 5, C + 20, ?_⟩
      simpa only [updatePositionBitmapWords, updatePositionBitmapReturnPC, hf,
        Bool.false_eq_true, if_false, if_true, List.cons_append, List.nil_append] using r1
    · have r1 := uniswapV3Pool_block_19438_fallthrough (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [hf]; rfl) rd
      refine ⟨k + 5, C + 20, ?_⟩
      simpa only [updatePositionBitmapWords, updatePositionBitmapCallPC, hf, if_true,
        List.cons_append, List.nil_append] using r1

theorem updatePositionBitmapCallEntryX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (a : UpdatePositionArgs) (evm : EVM.State) (upper : Bool)
    (rd : RD (deployedRuntime v) ee g s0 (updatePositionBitmapCallPC upper)
      (updatePositionBitmapWords v a evm ++ R) mem aw rdata σ k C)
    (hov : R.length + 18 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨21285⟩
      (v.tickSpacing :: EVM.wordOfInt (if upper then a.upper else a.lower) :: ⟨6⟩ ::
        updatePositionBitmapReturnPC upper :: updatePositionBitmapWords v a evm ++ R)
      mem aw rdata σ k' C' := by
  cases upper
  all_goals
    simp only [updatePositionBitmapCallPC, updatePositionBitmapWords, Bool.false_eq_true,
      if_false, if_true, List.cons_append, List.nil_append] at rd
  · have r1 := uniswapV3Pool_block_19395 (immWords := wordsOf (immStore v))
      (by evm_ov) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    refine ⟨k + 6, C + 23, ?_⟩
    simpa only [uniswapV3Pool_block_19395_stack, wordsOf_immStore_tickSpacing,
      wordOfInt_ofNat_toNat, updatePositionBitmapReturnPC, updatePositionBitmapWords,
      Bool.false_eq_true, if_false, List.cons_append, List.nil_append] using r1
  · have r1 := uniswapV3Pool_block_19445 (immWords := wordsOf (immStore v))
      (by evm_ov) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    refine ⟨k + 6, C + 23, ?_⟩
    simpa only [uniswapV3Pool_block_19445_stack, wordsOf_immStore_tickSpacing,
      wordOfInt_ofNat_toNat, updatePositionBitmapReturnPC, updatePositionBitmapWords,
      if_true, List.cons_append, List.nil_append] using r1

end Benchmarks.UniswapV3.Pool
