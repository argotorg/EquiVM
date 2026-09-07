import Reasoning.Solc
import Reasoning.MemCascade
import Examples.UniswapV2Pair.MemorySteps
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

-- GENERALIZES Reasoning.Theory.solcErrorStringMem0–3: arbitrary free-memory pointer.
noncomputable def solcErrorDynamicMem0 (mem : ByteArray) (ptr : UInt256) : ByteArray :=
  solcErrorStringSelector.toByteArray.write 0 mem ptr.toNat 32
noncomputable def solcErrorDynamicMem1 (mem : ByteArray) (ptr : UInt256) : ByteArray :=
  (⟨32⟩ : UInt256).toByteArray.write 0 (solcErrorDynamicMem0 mem ptr) (ptr + ⟨4⟩).toNat 32
noncomputable def solcErrorDynamicMem2 (mem : ByteArray) (ptr len : UInt256) : ByteArray :=
  len.toByteArray.write 0 (solcErrorDynamicMem1 mem ptr) (ptr + ⟨36⟩).toNat 32
noncomputable def solcErrorDynamicMem3 (mem : ByteArray) (ptr len word : UInt256) : ByteArray :=
  word.toByteArray.write 0 (solcErrorDynamicMem2 mem ptr len) (ptr + ⟨68⟩).toNat 32
abbrev solcErrorDynamicWords0 (aw ptr : UInt256) : UInt256 := memoryWordActiveWords aw ptr
abbrev solcErrorDynamicWords1 (aw ptr : UInt256) : UInt256 := memoryWordActiveWords (solcErrorDynamicWords0 aw ptr) (ptr + ⟨4⟩)
abbrev solcErrorDynamicWords2 (aw ptr : UInt256) : UInt256 := memoryWordActiveWords (solcErrorDynamicWords1 aw ptr) (ptr + ⟨36⟩)
abbrev solcErrorDynamicWords3 (aw ptr : UInt256) : UInt256 := memoryWordActiveWords (solcErrorDynamicWords2 aw ptr) (ptr + ⟨68⟩)

theorem solcErrorDynamicMem_sizes {mem : ByteArray} (ptr len word : UInt256)
    (hgap : ptr.toNat - mem.size < USize.size) (hfit : ptr.toNat + 68 < UInt256.size) :
    (solcErrorDynamicMem0 mem ptr).size = max mem.size (ptr.toNat + 32) ∧
    (solcErrorDynamicMem1 mem ptr).size = max mem.size (ptr.toNat + 36) ∧
    (solcErrorDynamicMem2 mem ptr len).size = max mem.size (ptr.toNat + 68) ∧
    (solcErrorDynamicMem3 mem ptr len word).size = max mem.size (ptr.toNat + 100) := by
  have h4 : (ptr + ⟨4⟩).toNat = ptr.toNat + 4 := uadd_word_ofNat_toNat ptr 4 (by omega)
  have h36 : (ptr + ⟨36⟩).toNat = ptr.toNat + 36 := uadd_word_ofNat_toNat ptr 36 (by omega)
  have h68 : (ptr + ⟨68⟩).toNat = ptr.toNat + 68 := uadd_word_ofNat_toNat ptr 68 hfit
  have hs0 : (solcErrorDynamicMem0 mem ptr).size = max mem.size (ptr.toNat + 32) := writeWord_size mem ptr.toNat solcErrorStringSelector hgap
  have hs1 := toByteArray_write32_size_of_le (solcErrorDynamicMem0 mem ptr) ⟨32⟩ (ptr + ⟨4⟩).toNat
    (max mem.size (ptr.toNat + 32)) (max mem.size (ptr.toNat + 36)) hs0 (by rw [h4]; rw [hs0]; omega) (by rw [h4]; omega)
  change (solcErrorDynamicMem1 mem ptr).size = max mem.size (ptr.toNat + 36) at hs1
  have hs2 := toByteArray_write32_size_of_le (solcErrorDynamicMem1 mem ptr) len (ptr + ⟨36⟩).toNat
    (max mem.size (ptr.toNat + 36)) (max mem.size (ptr.toNat + 68)) hs1 (by rw [h36]; rw [hs1]; omega) (by rw [h36]; omega)
  change (solcErrorDynamicMem2 mem ptr len).size = max mem.size (ptr.toNat + 68) at hs2
  have hs3 := toByteArray_write32_size_of_le (solcErrorDynamicMem2 mem ptr len) word (ptr + ⟨68⟩).toNat
    (max mem.size (ptr.toNat + 68)) (max mem.size (ptr.toNat + 100)) hs2 (by rw [h68]; rw [hs2]; omega) (by rw [h68]; omega)
  exact ⟨hs0, hs1, hs2, hs3⟩

theorem solcErrorDynamicMem3_read64 {mem : ByteArray} (ptr len word : UInt256)
    (hin : 96 ≤ mem.size) (hlo : 96 ≤ ptr.toNat) (hgap : ptr.toNat - mem.size < USize.size)
    (hfit : ptr.toNat + 68 < UInt256.size) :
    (solcErrorDynamicMem3 mem ptr len word).readWithPadding 64 32 = mem.readWithPadding 64 32 := by
  have h4 : (ptr + ⟨4⟩).toNat = ptr.toNat + 4 := uadd_word_ofNat_toNat ptr 4 (by omega)
  have h36 : (ptr + ⟨36⟩).toNat = ptr.toNat + 36 := uadd_word_ofNat_toNat ptr 36 (by omega)
  have h68 : (ptr + ⟨68⟩).toNat = ptr.toNat + 68 := uadd_word_ofNat_toNat ptr 68 hfit
  have hu : 0 < USize.size := lt_usize 0 (by omega)
  unfold solcErrorDynamicMem3 solcErrorDynamicMem2 solcErrorDynamicMem1 solcErrorDynamicMem0
  rw [h4, h36, h68]
  change (writeCascade mem [(ptr.toNat, solcErrorStringSelector), (ptr.toNat + 4, ⟨32⟩),
    (ptr.toNat + 36, len), (ptr.toNat + 68, word)]).readWithPadding 64 32 = _
  apply writeCascade_read_preserved
  simp only [WindowDisjointFromWrites]
  refine ⟨?_, Or.inl ⟨?_, ?_⟩, ?_, Or.inl ⟨?_, ?_⟩,
    ?_, Or.inl ⟨?_, ?_⟩, ?_, Or.inl ⟨?_, ?_⟩, trivial⟩ <;> omega

theorem solcErrorDynamicWords3_bounds (aw ptr : UInt256)
    (haw : aw.toNat * 32 < UInt256.size) (hfit : ptr.toNat + 131 < UInt256.size) :
    (solcErrorDynamicWords3 aw ptr).toNat * 32 < UInt256.size ∧
      ptr.toNat + 100 ≤ (solcErrorDynamicWords3 aw ptr).toNat * 32 := by
  have h4 : (ptr + ⟨4⟩).toNat = ptr.toNat + 4 := uadd_word_ofNat_toNat ptr 4 (by omega)
  have h36 : (ptr + ⟨36⟩).toNat = ptr.toNat + 36 := uadd_word_ofNat_toNat ptr 36 (by omega)
  have h68 : (ptr + ⟨68⟩).toNat = ptr.toNat + 68 := uadd_word_ofNat_toNat ptr 68 (by omega)
  have hb0 := UInt256_ofNat_M_mul32_lt aw ptr haw (by omega)
  have hb1 := UInt256_ofNat_M_mul32_lt (solcErrorDynamicWords0 aw ptr) (ptr + ⟨4⟩) hb0 (by rw [h4]; omega)
  have hb2 := UInt256_ofNat_M_mul32_lt (solcErrorDynamicWords1 aw ptr) (ptr + ⟨36⟩) hb1 (by rw [h36]; omega)
  have hb3 := UInt256_ofNat_M_mul32_lt (solcErrorDynamicWords2 aw ptr) (ptr + ⟨68⟩) hb2 (by rw [h68]; omega)
  have hc3 := UInt256_ofNat_M_covers (solcErrorDynamicWords2 aw ptr) (ptr + ⟨68⟩) hb2 (by rw [h68]; omega)
  refine ⟨hb3, ?_⟩
  change (ptr + ⟨68⟩).toNat + 32 ≤ (solcErrorDynamicWords3 aw ptr).toNat * 32 at hc3
  rw [h68] at hc3
  omega

theorem solcErrorDynamicMem3_mload64 {mem : ByteArray} (aw ptr len word : UInt256)
    (hin : 96 ≤ mem.size) (hlo : 96 ≤ ptr.toNat) (hgap : ptr.toNat - mem.size < USize.size)
    (hfit : ptr.toNat + 131 < UInt256.size) (haw : aw.toNat * 32 < UInt256.size)
    (hread : mem.readWithPadding 64 32 = ptr.toByteArray) :
    memoryWordLoad (solcErrorDynamicMem3 mem ptr len word) (solcErrorDynamicWords3 aw ptr) ⟨64⟩ = ptr ∧
    memoryWordActiveWords (solcErrorDynamicWords3 aw ptr) ⟨64⟩ = solcErrorDynamicWords3 aw ptr := by
  obtain ⟨hb, hc⟩ := solcErrorDynamicWords3_bounds aw ptr haw hfit
  have hcover : (⟨64⟩ : UInt256).toNat + 32 ≤ (solcErrorDynamicWords3 aw ptr).toNat * 32 := by change 64 + 32 ≤ _; omega
  refine ⟨?_, UInt256_M_same_of_cover _ _ hb hcover⟩
  apply mloadWordValue_of_readWithPadding
  · change 64 < _
    rw [(solcErrorDynamicMem_sizes ptr len word hgap (by omega)).2.2.2]; omega
  · exact UInt256_mload_haw_of_cover _ _ hb hcover
  · exact (solcErrorDynamicMem3_read64 ptr len word hin hlo hgap (by omega)).trans hread

end UniswapV2Pair
