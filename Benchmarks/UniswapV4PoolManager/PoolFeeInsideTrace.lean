import Benchmarks.UniswapV4PoolManager.PoolFeeInsideSource
import Benchmarks.UniswapV4PoolManager.PoolFeeInsideStartTrace
import Benchmarks.UniswapV4PoolManager.PoolFeeInsideRegionTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

open poolManagerBlocks in
theorem poolFeeInsideExactTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id lower upper x0 x1 x2 x3 x4 x5 delta x9 x10 : UInt256}
    {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+18 ≤ 1024) (hI : evm.executionEnv = I)
    (hm : memLoad (UInt256.ofNat 128) mem = poolSlot id) (hmem : 160 ≤ mem.size)
    (hl : int24Canonical lower) (hu : int24Canonical upper)
    (h : RD (deployedRuntime v) I g s0 ⟨5722⟩
      (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: upper :: delta :: lower :: x9 :: x10 :: R)
      mem aw rdata evm.accountMap k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ⟨5802⟩
      (poolFeeInsideOutputStack lower upper x0 x1 x2 x3 x4 x5 delta x9 x10
        (poolFeeInsideWord evm id (EVM.signed lower) (EVM.signed upper) false)
        (poolFeeInsideWord evm id (EVM.signed lower) (EVM.signed upper) true) R)
      (poolFeeInsideMemory mem id lower upper) (M aw (UInt256.ofNat 128) ⟨32⟩) rdata evm.accountMap k' C' := by
  obtain ⟨k1, C1, rd1⟩ := poolFeeInsideStartExactTrace v (by simp only [List.length_cons]; omega)
    hI hm hmem hl hu h
  have hm' : memLoad (UInt256.ofNat 128) (poolFeeInsideMemory mem id lower upper) = poolSlot id := by
    have hp := poolFeeInsideMemory_load (mem := mem) id lower upper (UInt256.ofNat 128) (by decide) hmem
    rw [hp]
    exact hm
  by_cases hb : poolCurrentTick evm id < EVM.signed lower
  · rw [if_pos hb] at rd1
    have hr := poolFeeInsideRegionExactTrace .below v hstack hI hm' rd1
    simpa only [poolFeeInsideRegionActiveWords, memoryWords_idem, poolFeeInsideWord, poolFeeInsideRegion, if_pos hb] using hr
  · rw [if_neg hb] at rd1
    dsimp only [poolFeeInsideStartStack] at rd1
    by_cases ha : poolCurrentTick evm id ≥ EVM.signed upper
    · have hg : UInt256.sgt upper (slot0TickWord (poolSlot0Word evm id)) = UInt256.ofNat 0 := by
        rw [sgt_signed, decide_eq_false (show ¬ EVM.signed (slot0TickWord (poolSlot0Word evm id)) <
          EVM.signed upper from not_lt.mpr ha)]
        rfl
      have rd2 := poolManager_block_6863_fallthrough (by simp only [List.length_cons]; omega) hg rd1
      dsimp only [poolManager_block_6863_fallthrough_stack] at rd2
      have hr := poolFeeInsideRegionExactTrace (cur := slot0TickWord (poolSlot0Word evm id)) .above v hstack hI hm' rd2
      simpa only [poolFeeInsideRegionActiveWords, memoryWords_idem, poolFeeInsideWord, poolFeeInsideRegion, if_neg hb, if_pos ha] using hr
    · have hg : UInt256.sgt upper (slot0TickWord (poolSlot0Word evm id)) ≠ UInt256.ofNat 0 := by
        rw [sgt_signed, decide_eq_true (show EVM.signed (slot0TickWord (poolSlot0Word evm id)) <
          EVM.signed upper from lt_of_not_ge ha)]
        decide
      have rd2 := poolManager_block_6863_taken (by simp only [List.length_cons]; omega) hg
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
      dsimp only [poolManager_block_6863_taken_stack] at rd2
      have hr := poolFeeInsideRegionExactTrace (cur := slot0TickWord (poolSlot0Word evm id)) .inside v hstack hI hm' rd2
      simpa only [poolFeeInsideRegionActiveWords, memoryWords_idem, poolFeeInsideWord, poolFeeInsideRegion, if_neg hb, if_neg ha] using hr

theorem poolFeeInsideTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id lower upper x0 x1 x2 x3 x4 x5 delta x9 x10 : UInt256}
    {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+18 ≤ 1024) (hI : evm.executionEnv = I)
    (hm : memLoad (UInt256.ofNat 128) mem = poolSlot id) (hmem : 160 ≤ mem.size)
    (hl : int24Canonical lower) (hu : int24Canonical upper)
    (h : RD (deployedRuntime v) I g s0 ⟨5722⟩
      (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: upper :: delta :: lower :: x9 :: x10 :: R)
      mem aw rdata evm.accountMap k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨5802⟩
      (poolFeeInsideOutputStack lower upper x0 x1 x2 x3 x4 x5 delta x9 x10
        (poolFeeInsideWord evm id (EVM.signed lower) (EVM.signed upper) false)
        (poolFeeInsideWord evm id (EVM.signed lower) (EVM.signed upper) true) R)
      (poolFeeInsideMemory mem id lower upper) aw' rdata evm.accountMap k' C' := by
  obtain ⟨k', C', hr⟩ := poolFeeInsideExactTrace v hstack hI hm hmem hl hu h
  exact ⟨_, k', C', hr⟩

end Benchmarks.UniswapV4PoolManager
