import Benchmarks.UniswapV4PoolManager.SwapPoolAllocateTrace
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_008

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem swapPoolSelectTrace {I : ExecutionEnv} {g : Sat256} {s0 : State} {σ : AccountMap}
    {mem rdata : ByteArray} {aw free rawFee fee before amount src len id keyPtr paramsPtr junk : UInt256}
    {key : PoolKeyWords} {p : SwapParamsWords} {R : List UInt256} {k C : Nat}
    (v : PoolManagerImmutables) (hstack : R.length+18 ≤ 1024)
    (hkey : PoolKeyView (swapPoolMemory mem free (swapPoolParams key p amount fee)) keyPtr key)
    (hp : MemorySlice (swapPoolMemory mem free (swapPoolParams key p amount fee)) paramsPtr.toNat
      (wordBytes (swapParamsWordList p)))
    (hf : free.toNat+160 < UInt256.size) (hclean : UInt256.land rawFee (UInt256.ofNat 16777215) = fee)
    (hpaid : Cₘ aw ≤ C)
    (h : RD (deployedRuntime v) I g s0 ⟨1669⟩
      ([amount, key.tickSpacing, UInt256.fromBool p.zeroForOne, p.priceLimit, rawFee,
        poolSlot id, src, len, before, free, keyPtr, id, keyPtr+UInt256.ofNat 128, paramsPtr, junk]++R)
      (writeWord mem 64 (free+UInt256.ofNat 160)) aw rdata σ k C) :
    ∃ aw' k' C', Cₘ aw' ≤ C' ∧ RD (deployedRuntime v) I g s0 ⟨18777⟩
      ([poolSlot id, free, ⟨1755⟩, id, UInt256.ofNat 16777215, paramsPtr, accountWord (swapPoolCurrency key p),
        src, len, before, ⟨1935⟩, keyPtr, ⟨1954⟩, keyPtr+UInt256.ofNat 128, UInt256.ofNat 32, junk]++R)
      (swapPoolMemory mem free (swapPoolParams key p amount fee)) aw' rdata σ k' C' := by
  have hm : poolManagerBlocks.poolManager_block_1669_taken_memory
      (mem := writeWord mem 64 (free+UInt256.ofNat 160)) (x0 := amount) (x1 := key.tickSpacing)
      (x2 := UInt256.fromBool p.zeroForOne) (x3 := p.priceLimit) (x4 := rawFee) (x9 := free) =
      swapPoolMemory mem free (swapPoolParams key p amount fee) :=
    swapPoolMemory_compiled (mem := mem) (p := swapPoolParams key p amount fee) hf hclean
  have hz : memLoad paramsPtr (swapPoolMemory mem free (swapPoolParams key p amount fee)) =
      UInt256.fromBool p.zeroForOne := hp.word_load (i := 0) rfl (by omega)
  have hk0 : memLoad keyPtr (swapPoolMemory mem free (swapPoolParams key p amount fee)) = key.currency0 := by
    have hh := hkey.load (i := 0) rfl
    change memLoad (keyPtr+⟨0⟩) _ = key.currency0 at hh
    simpa only [uadd_zero_r] using hh
  have hk1 : memLoad (keyPtr+UInt256.ofNat 32) (swapPoolMemory mem free (swapPoolParams key p amount fee)) =
      key.currency1 := hkey.load (i := 1) rfl
  by_cases hd : p.zeroForOne = false
  ·
    have hcond : UInt256.eq ⟨0⟩ (UInt256.isZero (UInt256.isZero
        (memLoad paramsPtr (poolManagerBlocks.poolManager_block_1669_taken_memory
          (mem := writeWord mem 64 (free+UInt256.ofNat 160)) (x0 := amount) (x1 := key.tickSpacing)
          (x2 := UInt256.fromBool p.zeroForOne) (x3 := p.priceLimit) (x4 := rawFee) (x9 := free))))) ≠ ⟨0⟩ := by
      rw [hm, hz, hd]
      decide
    have rd1 := poolManagerBlocks.poolManager_block_1669_taken (R := junk::R)
      (by simp only [List.length_cons]; omega) hcond
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    rw [hm] at rd1
    simp only [poolManagerBlocks.poolManager_block_1669_taken_stack] at rd1
    have rd2 := poolManagerBlocks.poolManager_block_2048 (R := junk::R)
      (by simp only [List.length_cons]; omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
    simp only [poolManagerBlocks.poolManager_block_2048_stack, hk1] at rd2
    have hc := memoryAccessCost_covers aw
      [(free, ⟨32⟩), (free+UInt256.ofNat 32, ⟨32⟩), (free+UInt256.ofNat 64, ⟨32⟩),
       (free+UInt256.ofNat 96, ⟨32⟩), (free+UInt256.ofNat 128, ⟨32⟩), (paramsPtr, ⟨32⟩),
       (keyPtr+UInt256.ofNat 32, ⟨32⟩)]
    dsimp only [memoryAccessWords, memoryAccessCost] at hc
    refine ⟨_, _, _, ?_, by
      simpa only [swapPoolCurrency, hd, Bool.false_eq_true, if_false, accountWord_fromId] using rd2⟩
    omega
  · have hd : p.zeroForOne = true := Bool.eq_true_of_not_eq_false hd
    have hcond : UInt256.eq ⟨0⟩ (UInt256.isZero (UInt256.isZero
        (memLoad paramsPtr (poolManagerBlocks.poolManager_block_1669_fallthrough_memory
          (mem := writeWord mem 64 (free+UInt256.ofNat 160)) (x0 := amount) (x1 := key.tickSpacing)
          (x2 := UInt256.fromBool p.zeroForOne) (x3 := p.priceLimit) (x4 := rawFee) (x9 := free))))) = ⟨0⟩ := by
      change UInt256.eq ⟨0⟩ (UInt256.isZero (UInt256.isZero
        (memLoad paramsPtr (poolManagerBlocks.poolManager_block_1669_taken_memory
          (mem := writeWord mem 64 (free+UInt256.ofNat 160)) (x0 := amount) (x1 := key.tickSpacing)
          (x2 := UInt256.fromBool p.zeroForOne) (x3 := p.priceLimit) (x4 := rawFee) (x9 := free))))) = ⟨0⟩
      rw [hm, hz, hd]
      rfl
    have rd1 := poolManagerBlocks.poolManager_block_1669_fallthrough (R := junk::R)
      (by simp only [List.length_cons]; omega) hcond h
    change RD _ _ _ _ _ _ (poolManagerBlocks.poolManager_block_1669_taken_memory
      (mem := writeWord mem 64 (free+UInt256.ofNat 160)) (x0 := amount) (x1 := key.tickSpacing)
      (x2 := UInt256.fromBool p.zeroForOne) (x3 := p.priceLimit) (x4 := rawFee) (x9 := free)) _ _ _ _ _ at rd1
    rw [hm] at rd1
    simp only [poolManagerBlocks.poolManager_block_1669_fallthrough_stack] at rd1
    have rd2 := poolManagerBlocks.poolManager_block_1726
      (R := [UInt256.ofNat 1954, keyPtr+UInt256.ofNat 128, UInt256.ofNat 32, junk]++R)
      (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
    simp only [poolManagerBlocks.poolManager_block_1726_stack, hk0] at rd2
    have hc := memoryAccessCost_covers aw
      [(free, ⟨32⟩), (free+UInt256.ofNat 32, ⟨32⟩), (free+UInt256.ofNat 64, ⟨32⟩),
       (free+UInt256.ofNat 96, ⟨32⟩), (free+UInt256.ofNat 128, ⟨32⟩), (paramsPtr, ⟨32⟩), (keyPtr, ⟨32⟩)]
    dsimp only [memoryAccessWords, memoryAccessCost] at hc
    refine ⟨_, _, _, ?_, by simpa only [swapPoolCurrency, hd, if_true, accountWord_fromId] using rd2⟩
    omega

end Benchmarks.UniswapV4PoolManager
