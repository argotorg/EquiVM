import Benchmarks.UniswapV3.Pool.UpdatePositionFeeModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem updatePositionFeeEntryX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : UpdatePositionArgs) (evm : EVM.State)
    (rd : RD (deployedRuntime v) ee g s0 ⟨19492⟩ (updatePositionChangedWords v a evm ++ R)
      mem aw rdata σ k C) (hov : R.length + 20 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨21387⟩
      ((updatePositionFeeArgs a evm).global1 :: (updatePositionFeeArgs a evm).global0 ::
        EVM.wordOfInt a.current :: EVM.wordOfInt a.upper :: EVM.wordOfInt a.lower :: ⟨5⟩ ::
        ⟨19510⟩ :: ⟨0⟩ :: ⟨0⟩ :: updatePositionChangedWords v a evm ++ R)
      mem aw rdata σ k' C' := by
  rw [updatePositionChangedWords_eq] at rd
  have r1 := uniswapV3Pool_block_19492 (immWords := wordsOf (immStore v))
    (by change R.length + 1 + 19 ≤ 1024; omega)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
  refine ⟨k + 12, C + 39, ?_⟩
  simpa only [uniswapV3Pool_block_19492_stack, updatePositionChangedWords_eq, updatePositionFeeArgs,
    List.cons_append, List.nil_append] using r1

theorem updatePositionFeeX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : UpdatePositionArgs) (evm : EVM.State)
    (hs : SourceState s0 ee σ (updatePositionChangedState v a evm))
    (rd : RD (deployedRuntime v) ee g s0 ⟨19492⟩ (updatePositionChangedWords v a evm ++ R)
      mem aw rdata σ k C) (ha : a.Fits) (hm : HeapMemory mem aw p) (hov : R.length + 30 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨19510⟩
      (updatePositionInside v a evm true :: updatePositionInside v a evm false ::
        ⟨0⟩ :: ⟨0⟩ :: updatePositionChangedWords v a evm ++ R)
      (tickFeeMemory mem (updatePositionFeeArgs a evm)) aw rdata σ k' C' ∧
      HeapMemory (tickFeeMemory mem (updatePositionFeeArgs a evm)) aw p := by
  obtain ⟨_, _, r1⟩ := updatePositionFeeEntryX (v := v) a evm rd (by omega)
  obtain ⟨k2, C2, r2, hm2⟩ := tickFeeHeapX (v := v) (updatePositionFeeArgs a evm) r1
    (updatePositionFeeArgs_fits a evm ha) hm
    (by rw [uniswapV3PoolPatchedValidJumps v]; jump_dest)
    (by rw [updatePositionChangedWords_eq]; change R.length + 12 + 18 ≤ 1024; omega)
  refine ⟨k2, C2, ?_, hm2⟩
  simpa only [updatePositionInside, hs.accounts, hs.env] using r2

theorem updatePositionPositionEntryX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : UpdatePositionArgs) (evm : EVM.State)
    (rd : RD (deployedRuntime v) ee g s0 ⟨19510⟩
      (updatePositionInside v a evm true :: updatePositionInside v a evm false ::
        ⟨0⟩ :: ⟨0⟩ :: updatePositionChangedWords v a evm ++ R) mem aw rdata σ k C)
    (hov : R.length + 18 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨21559⟩
      ((updatePositionPositionArgs v a evm).growth1 :: (updatePositionPositionArgs v a evm).growth0 ::
        EVM.wordOfInt a.delta :: solcMappingSlot ⟨7⟩ (updatePositionKey a) :: ⟨19527⟩ ::
        updatePositionInside v a evm true :: updatePositionInside v a evm false ::
        updatePositionChangedWords v a evm ++ R) mem aw rdata σ k' C' := by
  rw [updatePositionChangedWords_eq] at rd
  have r1 := uniswapV3Pool_block_19510 (immWords := wordsOf (immStore v))
    (by change R.length + 3 + 15 ≤ 1024; omega)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
  refine ⟨k + 13, C + 40, ?_⟩
  simpa only [uniswapV3Pool_block_19510_stack, updatePositionChangedWords_eq,
    updatePositionPositionArgs, List.cons_append, List.nil_append] using r1

end Benchmarks.UniswapV3.Pool
