import Examples.UniswapV2Pair.PairDynamicMemory
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000

-- LIBRARY CANDIDATE: four consecutive word writes, composed from two pairs.
noncomputable def quadDynamicMem (mem : ByteArray) (ptr word0 word1 word2 word3 : UInt256) : ByteArray :=
  pairDynamicMem (pairDynamicMem mem ptr word0 word1) (ptr + ⟨64⟩) word2 word3
abbrev quadDynamicWords (aw ptr : UInt256) : UInt256 :=
  pairDynamicWords (pairDynamicWords aw ptr) (ptr + ⟨64⟩)

theorem quadDynamicMem_size {mem : ByteArray} (ptr word0 word1 word2 word3 : UInt256)
    (hgap : ptr.toNat - mem.size < USize.size) (hfit : ptr.toNat + 96 < UInt256.size) :
    (quadDynamicMem mem ptr word0 word1 word2 word3).size = max mem.size (ptr.toNat + 128) := by
  have h64 : (ptr + ⟨64⟩).toNat = ptr.toNat + 64 := uadd_word_ofNat_toNat ptr 64 (by omega)
  have hs := (pairDynamicMem_sizes ptr word0 word1 hgap (by omega)).2
  have hg : (ptr + ⟨64⟩).toNat - (pairDynamicMem mem ptr word0 word1).size < USize.size := by
    rw [h64, hs, Nat.sub_eq_zero_of_le (by omega)]
    exact lt_usize 0 (by omega)
  rw [quadDynamicMem, (pairDynamicMem_sizes (ptr + ⟨64⟩) word2 word3 hg (by rw [h64]; omega)).2, h64, hs]
  omega

theorem quadDynamicMem_read_below {mem : ByteArray} (ptr word0 word1 word2 word3 : UInt256) (off : Nat)
    (hin : off + 32 ≤ mem.size) (hlo : off + 32 ≤ ptr.toNat)
    (hgap : ptr.toNat - mem.size < USize.size) (hfit : ptr.toNat + 96 < UInt256.size) :
    (quadDynamicMem mem ptr word0 word1 word2 word3).readWithPadding off 32 = mem.readWithPadding off 32 := by
  have h64 : (ptr + ⟨64⟩).toNat = ptr.toNat + 64 := uadd_word_ofNat_toNat ptr 64 (by omega)
  have hs := (pairDynamicMem_sizes ptr word0 word1 hgap (by omega)).2
  have hg : (ptr + ⟨64⟩).toNat - (pairDynamicMem mem ptr word0 word1).size < USize.size := by
    rw [h64, hs, Nat.sub_eq_zero_of_le (by omega)]
    exact lt_usize 0 (by omega)
  unfold quadDynamicMem
  rw [pairDynamicMem_read_below (ptr + ⟨64⟩) word2 word3 off (by rw [hs]; omega)
    (by rw [h64]; omega) hg (by rw [h64]; omega)]
  exact pairDynamicMem_read_below ptr word0 word1 off hin hlo hgap (by omega)

theorem quadDynamicWords_bounds (aw ptr : UInt256)
    (haw : aw.toNat * 32 < UInt256.size) (hfit : ptr.toNat + 159 < UInt256.size) :
    (quadDynamicWords aw ptr).toNat * 32 < UInt256.size ∧
      ptr.toNat + 128 ≤ (quadDynamicWords aw ptr).toNat * 32 := by
  have h64 : (ptr + ⟨64⟩).toNat = ptr.toNat + 64 := uadd_word_ofNat_toNat ptr 64 (by omega)
  obtain ⟨hb, _⟩ := pairDynamicWords_bounds aw ptr haw (by omega)
  obtain ⟨hb', hc'⟩ := pairDynamicWords_bounds (pairDynamicWords aw ptr) (ptr + ⟨64⟩) hb
    (by rw [h64]; omega)
  refine ⟨hb', ?_⟩
  change (ptr + ⟨64⟩).toNat + 64 ≤ (quadDynamicWords aw ptr).toNat * 32 at hc'
  rw [h64] at hc'
  omega

theorem quadDynamicMem_mload64 {mem : ByteArray} (aw ptr word0 word1 word2 word3 : UInt256)
    (hin : 96 ≤ mem.size) (hlo : 96 ≤ ptr.toNat) (hgap : ptr.toNat - mem.size < USize.size)
    (hfit : ptr.toNat + 159 < UInt256.size) (haw : aw.toNat * 32 < UInt256.size)
    (hread : mem.readWithPadding 64 32 = ptr.toByteArray) :
    memoryWordLoad (quadDynamicMem mem ptr word0 word1 word2 word3) (quadDynamicWords aw ptr) ⟨64⟩ = ptr ∧
    memoryWordActiveWords (quadDynamicWords aw ptr) ⟨64⟩ = quadDynamicWords aw ptr := by
  obtain ⟨hb, hc⟩ := quadDynamicWords_bounds aw ptr haw hfit
  have hcover : (⟨64⟩ : UInt256).toNat + 32 ≤ (quadDynamicWords aw ptr).toNat * 32 := by change 64 + 32 ≤ _; omega
  refine ⟨?_, UInt256_M_same_of_cover _ _ hb hcover⟩
  apply mloadWordValue_of_readWithPadding
  · change 64 < _
    rw [quadDynamicMem_size ptr word0 word1 word2 word3 hgap (by omega)]; omega
  · exact UInt256_mload_haw_of_cover _ _ hb hcover
  · exact (quadDynamicMem_read_below ptr word0 word1 word2 word3 64 hin hlo hgap (by omega)).trans hread

end UniswapV2Pair
