import Benchmarks.UniswapV4PoolManager.PoolKeyView
import Benchmarks.UniswapV4PoolManager.ModifyLiquidityParams

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

def modifyLiquidityDecodeMemory (key : PoolKeyWords) (p : ModifyLiquidityWords) : ByteArray :=
  wordSequenceMemory (writeWord (poolKeyMemory key) 64 ⟨448⟩) 320 (modifyLiquidityWords p)

theorem modifyLiquidityDecodeMemory_size (key : PoolKeyWords) (p : ModifyLiquidityWords) :
    (modifyLiquidityDecodeMemory key p).size = 448 := by
  rw [modifyLiquidityDecodeMemory,
    wordSequenceMemory_size _ (by rw [writeWord_sparse_size, poolKeyMemory_size]; decide),
    writeWord_sparse_size, poolKeyMemory_size]
  rfl

theorem modifyLiquidityDecodeMemory_key (key : PoolKeyWords) (p : ModifyLiquidityWords) :
    PoolKeyView (modifyLiquidityDecodeMemory key p) ⟨160⟩ key := by
  have hk := (poolKeyMemory_view key).writeWord 64 ⟨448⟩ (.inr (by decide))
  refine ⟨hk.slice.wordSequence 320 (modifyLiquidityWords p) ?_, hk.fits⟩
  rw [wordBytes_size]
  exact le_refl 320

theorem modifyLiquidityDecodeMemory_params (key : PoolKeyWords) (p : ModifyLiquidityWords) :
    MemorySlice (modifyLiquidityDecodeMemory key p) 320 (wordBytes (modifyLiquidityWords p)) := by
  refine ⟨?_, ?_⟩
  · rw [wordBytes_size]
    exact wordSequenceMemory_read _ _ _
  · rw [wordBytes_size, modifyLiquidityDecodeMemory_size]
    rfl

theorem modifyLiquidityDecodeMemory_free (key : PoolKeyWords) (p : ModifyLiquidityWords) :
    memLoad ⟨64⟩ (modifyLiquidityDecodeMemory key p) = ⟨448⟩ := by
  apply loadedWord_of_read
  · rw [modifyLiquidityDecodeMemory_size]; decide
  · change (wordSequenceMemory (writeWord (poolKeyMemory key) 64 ⟨448⟩) 320
      (modifyLiquidityWords p)).readWithPadding 64 32 = _
    rw [wordSequenceMemory_read_below _ _ _ _ (by rw [writeWord_sparse_size]; omega) (by decide),
      writeWord_sparse_read_back]

end Benchmarks.UniswapV4PoolManager
