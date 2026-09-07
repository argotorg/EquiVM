import Reasoning.MemCascade
import Examples.UniswapV2Pair.MemorySteps
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000


-- GENERALIZES the fixed-pointer Sync memory layout to two arbitrary words.
noncomputable def pairDynamicMem0 (mem : ByteArray) (ptr word0 : UInt256) : ByteArray :=
  word0.toByteArray.write 0 mem ptr.toNat 32
noncomputable def pairDynamicMem (mem : ByteArray) (ptr word0 word1 : UInt256) : ByteArray :=
  word1.toByteArray.write 0 (pairDynamicMem0 mem ptr word0) (ptr + ⟨32⟩).toNat 32
abbrev pairDynamicWords0 (aw ptr : UInt256) : UInt256 := memoryWordActiveWords aw ptr
abbrev pairDynamicWords (aw ptr : UInt256) : UInt256 := memoryWordActiveWords (pairDynamicWords0 aw ptr) (ptr + ⟨32⟩)

theorem pairDynamicMem_sizes {mem : ByteArray} (ptr word0 word1 : UInt256)
    (hgap : ptr.toNat - mem.size < USize.size) (hfit : ptr.toNat + 32 < UInt256.size) :
    (pairDynamicMem0 mem ptr word0).size = max mem.size (ptr.toNat + 32) ∧
    (pairDynamicMem mem ptr word0 word1).size = max mem.size (ptr.toNat + 64) := by
  have h32 : (ptr + ⟨32⟩).toNat = ptr.toNat + 32 := uadd_word_ofNat_toNat ptr 32 hfit
  have hs0 : (pairDynamicMem0 mem ptr word0).size = max mem.size (ptr.toNat + 32) := writeWord_size mem ptr.toNat word0 hgap
  have hs1 := toByteArray_write32_size_of_le (pairDynamicMem0 mem ptr word0) word1 (ptr + ⟨32⟩).toNat
    (max mem.size (ptr.toNat + 32)) (max mem.size (ptr.toNat + 64)) hs0
    (by rw [h32]; rw [hs0]; omega) (by rw [h32]; omega)
  exact ⟨hs0, hs1⟩

theorem pairDynamicMem_read_below {mem : ByteArray} (ptr word0 word1 : UInt256) (off : Nat)
    (hin : off + 32 ≤ mem.size) (hlo : off + 32 ≤ ptr.toNat)
    (hgap : ptr.toNat - mem.size < USize.size) (hfit : ptr.toNat + 32 < UInt256.size) :
    (pairDynamicMem mem ptr word0 word1).readWithPadding off 32 = mem.readWithPadding off 32 := by
  have h32 : (ptr + ⟨32⟩).toNat = ptr.toNat + 32 := uadd_word_ofNat_toNat ptr 32 hfit
  have hu : 0 < USize.size := lt_usize 0 (by omega)
  unfold pairDynamicMem pairDynamicMem0
  rw [h32]
  change (writeCascade mem [(ptr.toNat, word0), (ptr.toNat + 32, word1)]).readWithPadding off 32 = _
  apply writeCascade_read_preserved
  simp only [WindowDisjointFromWrites]
  refine ⟨?_, Or.inl ⟨?_, ?_⟩, ?_, Or.inl ⟨?_, ?_⟩, trivial⟩ <;> omega

theorem pairDynamicWords_bounds (aw ptr : UInt256)
    (haw : aw.toNat * 32 < UInt256.size) (hfit : ptr.toNat + 95 < UInt256.size) :
    (pairDynamicWords aw ptr).toNat * 32 < UInt256.size ∧
      ptr.toNat + 64 ≤ (pairDynamicWords aw ptr).toNat * 32 := by
  have h32 : (ptr + ⟨32⟩).toNat = ptr.toNat + 32 := uadd_word_ofNat_toNat ptr 32 (by omega)
  have hb0 := UInt256_ofNat_M_mul32_lt aw ptr haw (by omega)
  have hb1 := UInt256_ofNat_M_mul32_lt (pairDynamicWords0 aw ptr) (ptr + ⟨32⟩) hb0 (by rw [h32]; omega)
  have hc1 := UInt256_ofNat_M_covers (pairDynamicWords0 aw ptr) (ptr + ⟨32⟩) hb0 (by rw [h32]; omega)
  refine ⟨hb1, ?_⟩
  change (ptr + ⟨32⟩).toNat + 32 ≤ (pairDynamicWords aw ptr).toNat * 32 at hc1
  rw [h32] at hc1
  omega

theorem pairDynamicMem_mload64 {mem : ByteArray} (aw ptr word0 word1 : UInt256)
    (hin : 96 ≤ mem.size) (hlo : 96 ≤ ptr.toNat) (hgap : ptr.toNat - mem.size < USize.size)
    (hfit : ptr.toNat + 95 < UInt256.size) (haw : aw.toNat * 32 < UInt256.size)
    (hread : mem.readWithPadding 64 32 = ptr.toByteArray) :
    memoryWordLoad (pairDynamicMem mem ptr word0 word1) (pairDynamicWords aw ptr) ⟨64⟩ = ptr ∧
    memoryWordActiveWords (pairDynamicWords aw ptr) ⟨64⟩ = pairDynamicWords aw ptr := by
  obtain ⟨hb, hc⟩ := pairDynamicWords_bounds aw ptr haw hfit
  have hcover : (⟨64⟩ : UInt256).toNat + 32 ≤ (pairDynamicWords aw ptr).toNat * 32 := by change 64 + 32 ≤ _; omega
  refine ⟨?_, UInt256_M_same_of_cover _ _ hb hcover⟩
  apply mloadWordValue_of_readWithPadding
  · change 64 < _
    rw [(pairDynamicMem_sizes ptr word0 word1 hgap (by omega)).2]; omega
  · exact UInt256_mload_haw_of_cover _ _ hb hcover
  · exact (pairDynamicMem_read_below ptr word0 word1 64 hin hlo hgap (by omega)).trans hread

end UniswapV2Pair
