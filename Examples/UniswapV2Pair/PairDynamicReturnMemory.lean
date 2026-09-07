import Examples.UniswapV2Pair.PairDynamicMemory
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000


-- LIBRARY CANDIDATE: the ABI window formed by two consecutive word writes.
theorem pairDynamicMem_read_ptr {mem : ByteArray} (ptr word0 word1 : UInt256)
    (hgap : ptr.toNat - mem.size < USize.size) (hfit : ptr.toNat + 32 < UInt256.size) :
    (pairDynamicMem mem ptr word0 word1).readWithPadding ptr.toNat 64 = word0.toByteArray ++ word1.toByteArray := by
  have h32 : (ptr + ⟨32⟩).toNat = ptr.toNat + 32 := uadd_word_ofNat_toNat ptr 32 hfit
  obtain ⟨hs0, hs⟩ := pairDynamicMem_sizes ptr word0 word1 hgap hfit
  have hr0 : (pairDynamicMem mem ptr word0 word1).readWithPadding ptr.toNat 32 = word0.toByteArray := by
    unfold pairDynamicMem
    rw [write32_read_below _ _ (ptr + ⟨32⟩).toNat ptr.toNat (by rw [toByteArray_size])
      (by rw [h32, hs0]; omega) (by rw [h32])]
    exact writeWord_read_back mem ptr.toNat word0 hgap
  have hoff32 : (ptr + ⟨32⟩).toNat ≤ (pairDynamicMem0 mem ptr word0).size := by rw [h32, hs0]; omega
  have hr1 := toByteArray_write32_read_back (pairDynamicMem0 mem ptr word0) word1 (ptr + ⟨32⟩).toNat hoff32
  change (pairDynamicMem mem ptr word0 word1).readWithPadding (ptr + ⟨32⟩).toNat 32 = word1.toByteArray at hr1
  rw [h32] at hr1
  rw [byteArray_readWithPadding_split _ ptr.toNat 32 32 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by rw [hs]; omega), hr0, hr1]

end UniswapV2Pair
