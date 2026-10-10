import Benchmarks.UniswapV4PoolManager.SwapTargetWords
import Benchmarks.UniswapV4PoolManager.SwapStepFlags
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_055

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def swapStepStartMemory (mem : ByteArray) (next writeBase writeOffset : UInt256) : ByteArray :=
  next.toByteArray.write 0 mem (writeBase+writeOffset).toNat 32

def swapStepStartAW (aw writeBase writeOffset pricePtr paramsPtr liquidityOffset : UInt256) : UInt256 :=
  M (M (M (M aw (writeBase+writeOffset) ⟨32⟩) pricePtr ⟨32⟩) (paramsPtr+UInt256.ofNat 96) ⟨32⟩)
    (pricePtr+liquidityOffset) ⟨32⟩

/-- The inlined target selection and mode test, including the preceding tick-price memory store. -/
theorem swapStepStartTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray}
    {aw next limit price liquidity writeBase writeOffset liquidityOffset pricePtr paramsPtr fee remaining j x1 x3 x4 x6 x7 x8 : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (zeroForOne : Bool) (hstack : R.length+21 ≤ 1024)
    (hn : next.toNat < 2^160) (hlim : limit.toNat < 2^160)
    (hp : UInt256.land (memLoad pricePtr (swapStepStartMemory mem next writeBase writeOffset))
      (UInt256.ofNat 1461501637330902918203684832716283019655932542975) = price)
    (ht : UInt256.land (memLoad (paramsPtr+UInt256.ofNat 96) (swapStepStartMemory mem next writeBase writeOffset))
      (UInt256.ofNat 1461501637330902918203684832716283019655932542975) = limit)
    (hl : UInt256.land (memLoad (pricePtr+liquidityOffset) (swapStepStartMemory mem next writeBase writeOffset))
      (UInt256.ofNat 340282366920938463463374607431768211455) = liquidity)
    (h : RD (deployedRuntime v) I g s0 ⟨19479⟩
      ([next, solcAddrMask, writeBase, writeOffset, ⟨1⟩, liquidityOffset,
        UInt256.ofNat 340282366920938463463374607431768211455, pricePtr, fee,
        if zeroForOne then ⟨0⟩ else ⟨1⟩, remaining, x1, paramsPtr, x3, x4, fee, x6, x7, x8, j] ++ R)
      mem aw rdata σ k C) :
    ∃ k' C', C ≤ C' ∧ RD (deployedRuntime v) I g s0
      (if swapStepExactInput remaining then ⟨19593⟩ else ⟨20607⟩)
      ([price, j, if swapStepDirection price (swapTargetWord zeroForOne next limit) then ⟨1⟩ else ⟨0⟩,
        swapTargetWord zeroForOne next limit, fee, liquidity, remaining,
        x1, paramsPtr, x3, x4, fee, x6, x7, x8, j] ++ R)
      (swapStepStartMemory mem next writeBase writeOffset)
      (swapStepStartAW aw writeBase writeOffset pricePtr paramsPtr liquidityOffset) rdata σ k' C' := by
  have hnext : UInt256.land next solcAddrMask = next := solcAddrMask_clean hn
  have htarget : UInt256.land (swapTargetWord zeroForOne next limit)
      (UInt256.ofNat 1461501637330902918203684832716283019655932542975) = swapTargetWord zeroForOne next limit :=
    solcAddrMask_clean (swapTargetWord_canonical hn hlim)
  have hselect := swapTargetCompiled_eq zeroForOne next limit
  unfold swapTargetCompiled at hselect
  simp only [swapStepStartMemory] at hp ht hl
  cases he : swapStepExactInput remaining with
  | false =>
    simp only [he, Bool.false_eq_true, if_false]
    have rd := poolManagerBlocks.poolManager_block_19479_taken hstack
      (by rw [swapStepExactInput_test, he]; decide +kernel)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    simp only [poolManagerBlocks.poolManager_block_19479_taken_stack,
      poolManagerBlocks.poolManager_block_19479_taken_memory, hnext, hp, ht, hl,
      swapTargetDirection_test, hselect, htarget, swapStepDirection_test] at rd
    exact ⟨_, _, by omega, rd⟩
  | true =>
    simp only [he, if_true]
    have rd := poolManagerBlocks.poolManager_block_19479_fallthrough hstack
      (by rw [swapStepExactInput_test, he]; decide +kernel) h
    simp only [poolManagerBlocks.poolManager_block_19479_fallthrough_stack,
      poolManagerBlocks.poolManager_block_19479_fallthrough_memory, hnext, hp, ht, hl,
      swapTargetDirection_test, hselect, htarget, swapStepDirection_test] at rd
    exact ⟨_, _, by omega, rd⟩

end Benchmarks.UniswapV4PoolManager
