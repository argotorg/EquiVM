import Benchmarks.UniswapV4PoolManager.PoolKeyView
import Benchmarks.UniswapV4PoolManager.SwapParams

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

def swapDecodeMemory (key : PoolKeyWords) (p : SwapParamsWords) : ByteArray :=
  wordSequenceMemory (writeWord (poolKeyMemory key) 64 ⟨416⟩) 320 (swapParamsWordList p)

theorem swapDecodeMemory_size (key : PoolKeyWords) (p : SwapParamsWords) :
    (swapDecodeMemory key p).size = 416 := by
  rw [swapDecodeMemory,
    wordSequenceMemory_size _ (by rw [writeWord_sparse_size, poolKeyMemory_size]; decide),
    writeWord_sparse_size, poolKeyMemory_size]
  rfl

theorem swapDecodeMemory_key (key : PoolKeyWords) (p : SwapParamsWords) :
    PoolKeyView (swapDecodeMemory key p) ⟨160⟩ key := by
  have hk := (poolKeyMemory_view key).writeWord 64 ⟨416⟩ (.inr (by decide))
  refine ⟨hk.slice.wordSequence 320 (swapParamsWordList p) ?_, hk.fits⟩
  rw [wordBytes_size]
  exact le_refl 320

theorem swapDecodeMemory_params (key : PoolKeyWords) (p : SwapParamsWords) :
    MemorySlice (swapDecodeMemory key p) 320 (wordBytes (swapParamsWordList p)) := by
  refine ⟨?_, ?_⟩
  · rw [wordBytes_size]
    exact wordSequenceMemory_read _ _ _
  · rw [wordBytes_size, swapDecodeMemory_size]
    rfl

theorem swapDecodeMemory_free (key : PoolKeyWords) (p : SwapParamsWords) :
    memLoad ⟨64⟩ (swapDecodeMemory key p) = ⟨416⟩ := by
  apply loadedWord_of_read
  · rw [swapDecodeMemory_size]; decide
  · change (wordSequenceMemory (writeWord (poolKeyMemory key) 64 ⟨416⟩) 320
      (swapParamsWordList p)).readWithPadding 64 32 = _
    rw [wordSequenceMemory_read_below _ _ _ _ (by rw [writeWord_sparse_size]; omega) (by decide),
      writeWord_sparse_read_back]

end Benchmarks.UniswapV4PoolManager
