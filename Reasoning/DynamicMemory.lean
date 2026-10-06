import Reasoning.Solc
import Reasoning.MemCascade

/-!
# Dynamic Solidity memory layouts

Consecutive ABI words, return-data allocations, and error payloads at arbitrary free-memory
pointers, with their size, read-back, and memory-expansion facts.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Reach

namespace Reasoning.Theory

set_option autoImplicit false

def pairDynamicMem0 (mem : ByteArray) (ptr word0 : UInt256) : ByteArray :=
  word0.toByteArray.write 0 mem ptr.toNat 32

def pairDynamicMem (mem : ByteArray) (ptr word0 word1 : UInt256) : ByteArray :=
  word1.toByteArray.write 0 (pairDynamicMem0 mem ptr word0) (ptr + ⟨32⟩).toNat 32

abbrev pairDynamicWords0 (aw ptr : UInt256) : UInt256 := memoryWordActiveWords aw ptr

abbrev pairDynamicWords (aw ptr : UInt256) : UInt256 :=
  memoryWordActiveWords (pairDynamicWords0 aw ptr) (ptr + ⟨32⟩)

theorem pairDynamicMem_sizes {mem : ByteArray} (ptr word0 word1 : UInt256)
    (hgap : ptr.toNat - mem.size < USize.size) (hfit : ptr.toNat + 32 < UInt256.size) :
    (pairDynamicMem0 mem ptr word0).size = max mem.size (ptr.toNat + 32) ∧
    (pairDynamicMem mem ptr word0 word1).size = max mem.size (ptr.toNat + 64) := by
  have h32 : (ptr + ⟨32⟩).toNat = ptr.toNat + 32 := uadd_word_ofNat_toNat ptr 32 hfit
  have hs0 : (pairDynamicMem0 mem ptr word0).size = max mem.size (ptr.toNat + 32) :=
    writeWord_size mem ptr.toNat word0 hgap
  have hs1 :=
    toByteArray_write32_size_of_le (pairDynamicMem0 mem ptr word0) word1 (ptr + ⟨32⟩).toNat
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
  have hb1 :=
    UInt256_ofNat_M_mul32_lt (pairDynamicWords0 aw ptr) (ptr + ⟨32⟩) hb0 (by rw [h32]; omega)
  have hc1 :=
    UInt256_ofNat_M_covers (pairDynamicWords0 aw ptr) (ptr + ⟨32⟩) hb0 (by rw [h32]; omega)
  refine ⟨hb1, ?_⟩
  change (ptr + ⟨32⟩).toNat + 32 ≤ (pairDynamicWords aw ptr).toNat * 32 at hc1
  rw [h32] at hc1
  omega

theorem pairDynamicMem_mload64 {mem : ByteArray} (aw ptr word0 word1 : UInt256)
    (hin : 96 ≤ mem.size) (hlo : 96 ≤ ptr.toNat) (hgap : ptr.toNat - mem.size < USize.size)
    (hfit : ptr.toNat + 95 < UInt256.size) (haw : aw.toNat * 32 < UInt256.size)
    (hread : mem.readWithPadding 64 32 = ptr.toByteArray) :
    memoryWordLoad (pairDynamicMem mem ptr word0 word1) ⟨64⟩ = ptr ∧
    memoryWordActiveWords (pairDynamicWords aw ptr) ⟨64⟩ = pairDynamicWords aw ptr := by
  obtain ⟨hb, hc⟩ := pairDynamicWords_bounds aw ptr haw hfit
  have hcover : (⟨64⟩ : UInt256).toNat + 32 ≤ (pairDynamicWords aw ptr).toNat * 32 := by
    change 64 + 32 ≤ _; omega
  refine ⟨?_, UInt256_M_same_of_cover _ _ hb hcover⟩
  apply mloadWordValue_of_readWithPadding
  · change 64 < _
    rw [(pairDynamicMem_sizes ptr word0 word1 hgap (by omega)).2]; omega
  · exact (pairDynamicMem_read_below ptr word0 word1 64 hin hlo hgap (by omega)).trans hread

def quadDynamicMem (mem : ByteArray) (ptr word0 word1 word2 word3 : UInt256) : ByteArray :=
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
  rw [quadDynamicMem, (pairDynamicMem_sizes (ptr + ⟨64⟩) word2 word3 hg (by rw [h64]; omega)).2,
    h64, hs]
  omega

theorem quadDynamicMem_read_below {mem : ByteArray} (ptr word0 word1 word2 word3 : UInt256)
    (off : Nat)
    (hin : off + 32 ≤ mem.size) (hlo : off + 32 ≤ ptr.toNat)
    (hgap : ptr.toNat - mem.size < USize.size) (hfit : ptr.toNat + 96 < UInt256.size) :
    (quadDynamicMem mem ptr word0 word1 word2 word3).readWithPadding off 32 = mem.readWithPadding
      off 32 := by
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
    memoryWordLoad (quadDynamicMem mem ptr word0 word1 word2 word3) ⟨64⟩ = ptr ∧
    memoryWordActiveWords (quadDynamicWords aw ptr) ⟨64⟩ = quadDynamicWords aw ptr := by
  obtain ⟨hb, hc⟩ := quadDynamicWords_bounds aw ptr haw hfit
  have hcover : (⟨64⟩ : UInt256).toNat + 32 ≤ (quadDynamicWords aw ptr).toNat * 32 := by
    change 64 + 32 ≤ _; omega
  refine ⟨?_, UInt256_M_same_of_cover _ _ hb hcover⟩
  apply mloadWordValue_of_readWithPadding
  · change 64 < _
    rw [quadDynamicMem_size ptr word0 word1 word2 word3 hgap (by omega)]; omega
  · exact (quadDynamicMem_read_below ptr word0 word1 word2 word3 64 hin hlo hgap (by omega)).trans
      hread

theorem pairDynamicMem_read_ptr {mem : ByteArray} (ptr word0 word1 : UInt256)
    (hgap : ptr.toNat - mem.size < USize.size) (hfit : ptr.toNat + 32 < UInt256.size) :
    (pairDynamicMem mem ptr word0 word1).readWithPadding ptr.toNat 64 = word0.toByteArray ++
      word1.toByteArray := by
  have h32 : (ptr + ⟨32⟩).toNat = ptr.toNat + 32 := uadd_word_ofNat_toNat ptr 32 hfit
  obtain ⟨hs0, hs⟩ := pairDynamicMem_sizes ptr word0 word1 hgap hfit
  have hr0 : (pairDynamicMem mem ptr word0 word1).readWithPadding ptr.toNat 32 = word0.toByteArray
    := by
    unfold pairDynamicMem
    rw [write32_read_below _ _ (ptr + ⟨32⟩).toNat ptr.toNat (by rw [toByteArray_size])
      (by rw [h32, hs0]; omega) (by rw [h32])]
    exact writeWord_read_back mem ptr.toNat word0 hgap
  have hoff32 : (ptr + ⟨32⟩).toNat ≤ (pairDynamicMem0 mem ptr word0).size := by rw [h32, hs0]; omega
  have hr1 :=
    toByteArray_write32_read_back (pairDynamicMem0 mem ptr word0) word1 (ptr + ⟨32⟩).toNat hoff32
  change (pairDynamicMem mem ptr word0 word1).readWithPadding (ptr + ⟨32⟩).toNat 32 =
    word1.toByteArray at hr1
  rw [h32] at hr1
  rw [byteArray_readWithPadding_split _ ptr.toNat 32 32 (by decide) (by decide) (by decide)
    (by decide)
    (by decide) (by rw [hs]; omega), hr0, hr1]

theorem byteArray_write_prefix32 (src base : ByteArray) (dest : Nat)
    (hsrc : 32 ≤ src.size) (hdest : dest ≤ base.size) :
    (src.write 0 base dest src.size).readWithPadding dest 32 = src.extract 0 32 := by
  have hne : src.size ≠ 0 := by omega
  have hprefix : (base.extract 0 dest).size = dest := by rw [ByteArray.size_extract]; omega
  by_cases hin : dest + src.size ≤ base.size
  · rw [write_eq_gen src base dest src.size hne le_rfl hin]
    rw [readWithPadding_eq_extract _ dest (by
      rw [ByteArray.size_append, ByteArray.size_append, hprefix, ByteArray.size_extract]
      omega)]
    rw [extract_append_left _ _ dest (dest + 32) (by
      rw [ByteArray.size_append, hprefix, ByteArray.size_extract]
      omega)]
    rw [extract_append_right_window _ _ dest (dest + 32) (by rw [hprefix])]
    rw [hprefix, Nat.sub_self, Nat.add_sub_cancel_left, extract_extract_BA]
    simp only [Nat.zero_add, Nat.min_eq_left hsrc]
  · rw [write_eq_gen_extend src base dest src.size hne le_rfl hdest (by omega)]
    rw [readWithPadding_eq_extract _ dest (by
      rw [ByteArray.size_append, hprefix, ByteArray.size_extract]
      omega)]
    rw [extract_append_right_window _ _ dest (dest + 32) (by rw [hprefix])]
    rw [hprefix, Nat.sub_self, Nat.add_sub_cancel_left, extract_extract_BA]
    simp only [Nat.zero_add, Nat.min_eq_left hsrc]

theorem byteArray_write_all_size (src base : ByteArray) (dest : Nat) (hdest : dest ≤ base.size) :
    (src.write 0 base dest src.size).size = max base.size (dest + src.size) := by
  by_cases hz : src.size = 0
  · rw [hz, byteArray_write_len_zero, Nat.add_zero, Nat.max_eq_left hdest]
  · by_cases hin : dest + src.size ≤ base.size
    · rw [write_eq_gen src base dest src.size hz le_rfl hin,
        ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
        ByteArray.size_extract, ByteArray.size_extract]
      omega
    · rw [write_eq_gen_extend src base dest src.size hz le_rfl hdest (by omega),
        ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract]
      omega

def solcReturnDataPtrMem (mem : ByteArray) (ptr : UInt256) (out : ByteArray) : ByteArray :=
  (ptr + UInt256.land (UInt256.ofNat out.size + ⟨63⟩) (UInt256.lnot ⟨31⟩)).toByteArray.write 0 mem
    64 32

def solcReturnDataSizeMem (mem : ByteArray) (ptr : UInt256) (out : ByteArray) : ByteArray :=
  (UInt256.ofNat out.size).toByteArray.write 0 (solcReturnDataPtrMem mem ptr out) ptr.toNat 32

def solcReturnDataMem (mem : ByteArray) (ptr : UInt256) (out : ByteArray) : ByteArray :=
  out.write 0 (solcReturnDataSizeMem mem ptr out) (ptr + ⟨32⟩).toNat out.size

abbrev solcReturnDataActiveWords (aw ptr : UInt256) (out : ByteArray) : UInt256 :=
  UInt256.ofNat (MachineState.M aw.toNat (ptr + ⟨32⟩).toNat out.size)

theorem solcReturnDataPtrMem_size {mem : ByteArray} (ptr : UInt256) (out : ByteArray)
    (hin : 96 ≤ mem.size) : (solcReturnDataPtrMem mem ptr out).size = mem.size := by
  have h := toByteArray_write32_size_of_le mem
    (ptr + UInt256.land (UInt256.ofNat out.size + ⟨63⟩) (UInt256.lnot ⟨31⟩)) 64 mem.size mem.size
    rfl (by omega) (by omega)
  exact h

theorem solcReturnDataSizeMem_size {mem : ByteArray} (ptr : UInt256) (out : ByteArray)
    (hin : 96 ≤ mem.size) (hptr : ptr.toNat + 32 ≤ mem.size) :
    (solcReturnDataSizeMem mem ptr out).size = mem.size := by
  have hs := solcReturnDataPtrMem_size ptr out hin
  have h :=
    toByteArray_write32_size_of_le (solcReturnDataPtrMem mem ptr out) (UInt256.ofNat out.size)
    ptr.toNat mem.size mem.size hs (by rw [hs]; omega) (by omega)
  exact h

theorem solcReturnDataMem_size {mem : ByteArray} (ptr : UInt256) (out : ByteArray)
    (hin : 96 ≤ mem.size) (hptr : ptr.toNat + 32 ≤ mem.size) (hfit : ptr.toNat + 32 < UInt256.size)
      :
    (solcReturnDataMem mem ptr out).size = max mem.size (ptr.toNat + 32 + out.size) := by
  have h32 : (ptr + ⟨32⟩).toNat = ptr.toNat + 32 := uadd_word_ofNat_toNat ptr 32 hfit
  have hs := solcReturnDataSizeMem_size ptr out hin hptr
  have h := byteArray_write_all_size out (solcReturnDataSizeMem mem ptr out) (ptr + ⟨32⟩).toNat
    (by rw [h32, hs]; omega)
  change (solcReturnDataMem mem ptr out).size = _ at h
  rw [h32, hs] at h
  exact h

theorem solcReturnDataMem_read_size {mem : ByteArray} (ptr : UInt256) (out : ByteArray)
    (hin : 96 ≤ mem.size) (hptr : ptr.toNat + 32 ≤ mem.size) (hfit : ptr.toNat + 32 < UInt256.size)
      :
    (solcReturnDataMem mem ptr out).readWithPadding ptr.toNat 32 =
      (UInt256.ofNat out.size).toByteArray := by
  have h32 : (ptr + ⟨32⟩).toNat = ptr.toNat + 32 := uadd_word_ofNat_toNat ptr 32 hfit
  have hs := solcReturnDataSizeMem_size ptr out hin hptr
  have hsPtr := solcReturnDataPtrMem_size ptr out hin
  unfold solcReturnDataMem
  by_cases hz : out.size = 0
  · rw [hz, byteArray_write_len_zero]
    unfold solcReturnDataSizeMem
    have h :=
      toByteArray_write32_read_back (solcReturnDataPtrMem mem ptr out) (UInt256.ofNat out.size)
      ptr.toNat (by rw [hsPtr]; omega)
    exact h.trans (congrArg (fun n => (UInt256.ofNat n).toByteArray) hz)
  · rw [write_read_below_gen_extend out _ (ptr + ⟨32⟩).toNat out.size ptr.toNat hz le_rfl
      (by rw [h32, hs]; omega) (by rw [h32])]
    unfold solcReturnDataSizeMem
    have h :=
      toByteArray_write32_read_back (solcReturnDataPtrMem mem ptr out) (UInt256.ofNat out.size)
      ptr.toNat (by rw [hsPtr]; omega)
    exact h

theorem solcReturnDataMem_read_word {mem : ByteArray} (ptr : UInt256) (out : ByteArray)
    (hin : 96 ≤ mem.size) (hptr : ptr.toNat + 32 ≤ mem.size) (hfit : ptr.toNat + 32 < UInt256.size)
    (hout : 32 ≤ out.size) :
    (solcReturnDataMem mem ptr out).readWithPadding (ptr + ⟨32⟩).toNat 32 = out.extract 0 32 := by
  have h32 : (ptr + ⟨32⟩).toNat = ptr.toNat + 32 := uadd_word_ofNat_toNat ptr 32 hfit
  have hs := solcReturnDataSizeMem_size ptr out hin hptr
  have h :=
    byteArray_write_prefix32 out (solcReturnDataSizeMem mem ptr out) (ptr + ⟨32⟩).toNat hout
      (by rw [h32, hs]; omega)
  exact h

theorem solcReturnDataActiveWords_bounds (aw ptr : UInt256) (out : ByteArray)
    (haw : aw.toNat * 32 < UInt256.size) (hfit : ptr.toNat + out.size + 95 < UInt256.size) :
    (solcReturnDataActiveWords aw ptr out).toNat * 32 < UInt256.size ∧
      aw.toNat ≤ (solcReturnDataActiveWords aw ptr out).toNat := by
  have h32 : (ptr + ⟨32⟩).toNat = ptr.toNat + 32 := uadd_word_ofNat_toNat ptr 32 (by omega)
  have hM :=
    MachineState_M_mul32_lt_of_bounds haw
      (show (ptr + ⟨32⟩).toNat + out.size + 31 < UInt256.size by rw [h32]; omega)
  have hMlt : MachineState.M aw.toNat (ptr + ⟨32⟩).toNat out.size < UInt256.size := by omega
  change (UInt256.ofNat (MachineState.M aw.toNat (ptr + ⟨32⟩).toNat out.size)).toNat * 32 <
    UInt256.size ∧
    aw.toNat ≤ (UInt256.ofNat (MachineState.M aw.toNat (ptr + ⟨32⟩).toNat out.size)).toNat
  rw [UInt256.toNat_ofNat_of_lt hMlt]
  exact ⟨hM, MachineState_M_ge_left _ _ _⟩

theorem solcReturnDataMem_mload_size {mem : ByteArray} (aw ptr : UInt256) (out : ByteArray)
    (hin : 96 ≤ mem.size) (hptr : ptr.toNat + 32 ≤ mem.size)
    (hcover : ptr.toNat + 64 ≤ aw.toNat * 32)
    (haw : aw.toNat * 32 < UInt256.size) (hfit : ptr.toNat + out.size + 95 < UInt256.size) :
    memoryWordLoad (solcReturnDataMem mem ptr out) ptr = UInt256.ofNat out.size ∧
    memoryWordActiveWords (solcReturnDataActiveWords aw ptr out) ptr = solcReturnDataActiveWords aw
      ptr out := by
  obtain ⟨hb, hge⟩ := solcReturnDataActiveWords_bounds aw ptr out haw hfit
  have hc : ptr.toNat + 32 ≤ (solcReturnDataActiveWords aw ptr out).toNat * 32 := by omega
  constructor
  · apply mloadWordValue_of_readWithPadding
    · rw [solcReturnDataMem_size ptr out hin hptr (by omega)]
      omega
    · exact solcReturnDataMem_read_size ptr out hin hptr (by omega)
  · exact UInt256_M_same_of_cover _ _ hb hc

theorem solcReturnDataMem_mload_word {mem : ByteArray} (aw ptr : UInt256) (out : ByteArray)
    (hin : 96 ≤ mem.size) (hptr : ptr.toNat + 32 ≤ mem.size)
    (hcover : ptr.toNat + 64 ≤ aw.toNat * 32)
    (haw : aw.toNat * 32 < UInt256.size) (hfit : ptr.toNat + out.size + 95 < UInt256.size)
    (hout : 32 ≤ out.size) :
    memoryWordLoad (solcReturnDataMem mem ptr out) (ptr + ⟨32⟩) =
      UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)) ∧
    memoryWordActiveWords (solcReturnDataActiveWords aw ptr out) (ptr + ⟨32⟩) =
      solcReturnDataActiveWords aw ptr out := by
  have h32 : (ptr + ⟨32⟩).toNat = ptr.toNat + 32 := uadd_word_ofNat_toNat ptr 32 (by omega)
  obtain ⟨hb, hge⟩ := solcReturnDataActiveWords_bounds aw ptr out haw hfit
  have hc : (ptr + ⟨32⟩).toNat + 32 ≤ (solcReturnDataActiveWords aw ptr out).toNat * 32 := by
    rw [h32]; omega
  constructor
  · have hm := mloadValue_eq_readWithPadding_of_lt_size (solcReturnDataMem mem ptr out)
      (ptr + ⟨32⟩) _
      (solcReturnDataMem_size ptr out hin hptr (by omega)) (by rw [h32]; omega)
    exact hm.trans (congrArg (fun bytes => UInt256.ofNat (fromByteArrayBigEndian bytes))
      (solcReturnDataMem_read_word ptr out hin hptr (by omega) hout))
  · exact UInt256_M_same_of_cover _ _ hb hc

theorem solcReturnDataRounded_toNat (size : Nat) (hfit : size + 63 < UInt256.size) :
    (UInt256.land (UInt256.ofNat size + ⟨63⟩) (UInt256.lnot ⟨31⟩)).toNat = (size + 63) / 32 * 32 :=
      by
  rw [u256_land_comm]
  rw [show UInt256.lnot ⟨31⟩ = UInt256.ofNat (2 ^ 256 - 2 ^ 5) by decide,
    u256_land_high_mask_toNat _ 5 (by omega)]
  rw [uadd_toNat, UInt256.toNat_ofNat_of_lt (by omega)]
  change ((size + 63) % UInt256.size) / 32 * 32 = (size + 63) / 32 * 32
  rw [Nat.mod_eq_of_lt hfit]

theorem solcReturnDataMem_read_below_ptr {mem : ByteArray} (ptr : UInt256) (out : ByteArray)
    (read : Nat)
    (hin : 96 ≤ mem.size) (hptr : ptr.toNat + 32 ≤ mem.size) (hfit : ptr.toNat + 32 < UInt256.size)
    (hread : read + 32 ≤ ptr.toNat) :
    (solcReturnDataMem mem ptr out).readWithPadding read 32 =
      (solcReturnDataPtrMem mem ptr out).readWithPadding read 32 := by
  have h32 : (ptr + ⟨32⟩).toNat = ptr.toNat + 32 := uadd_word_ofNat_toNat ptr 32 hfit
  have hsSize := solcReturnDataSizeMem_size ptr out hin hptr
  have hsPtr := solcReturnDataPtrMem_size ptr out hin
  have hcopy : (solcReturnDataMem mem ptr out).readWithPadding read 32 =
      (solcReturnDataSizeMem mem ptr out).readWithPadding read 32 := by
    unfold solcReturnDataMem
    by_cases hz : out.size = 0
    · rw [hz, byteArray_write_len_zero]
    · have h := write_read_below_gen_extend out (solcReturnDataSizeMem mem ptr out)
        (ptr + ⟨32⟩).toNat out.size read hz le_rfl
        (by rw [h32, hsSize]; omega) (by rw [h32]; omega)
      exact h
  rw [hcopy]
  unfold solcReturnDataSizeMem
  exact write32_read_below _ _ ptr.toNat read (by rw [toByteArray_size]) (by rw [hsPtr]; omega)
    hread

theorem solcReturnDataMem_read64 {mem : ByteArray} (ptr : UInt256) (out : ByteArray)
    (hin : 96 ≤ mem.size) (hptr : ptr.toNat + 32 ≤ mem.size) (hfit : ptr.toNat + 32 < UInt256.size)
    (hptrLo : 96 ≤ ptr.toNat) :
    (solcReturnDataMem mem ptr out).readWithPadding 64 32 =
      (ptr + UInt256.land (UInt256.ofNat out.size + ⟨63⟩) (UInt256.lnot ⟨31⟩)).toByteArray := by
  rw [solcReturnDataMem_read_below_ptr ptr out 64 hin hptr hfit hptrLo]
  unfold solcReturnDataPtrMem
  have h := toByteArray_write32_read_back mem
    (ptr + UInt256.land (UInt256.ofNat out.size + ⟨63⟩) (UInt256.lnot ⟨31⟩)) 64 (by omega)
  exact h

theorem solcReturnDataMem_read96 {mem : ByteArray} (ptr : UInt256) (out : ByteArray)
    (hin : 96 ≤ mem.size) (hptr : ptr.toNat + 32 ≤ mem.size) (hfit : ptr.toNat + 32 < UInt256.size)
    (hptrLo : 128 ≤ ptr.toNat) :
    (solcReturnDataMem mem ptr out).readWithPadding 96 32 = mem.readWithPadding 96 32 := by
  rw [solcReturnDataMem_read_below_ptr ptr out 96 hin hptr hfit hptrLo]
  unfold solcReturnDataPtrMem
  exact write32_read_above _ _ 64 96 (by rw [toByteArray_size]) (by omega) (by omega) (by omega)

def solcErrorDynamicMem0 (mem : ByteArray) (ptr : UInt256) : ByteArray :=
  solcErrorStringSelector.toByteArray.write 0 mem ptr.toNat 32

def solcErrorDynamicMem1 (mem : ByteArray) (ptr : UInt256) : ByteArray :=
  (⟨32⟩ : UInt256).toByteArray.write 0 (solcErrorDynamicMem0 mem ptr) (ptr + ⟨4⟩).toNat 32

def solcErrorDynamicMem2 (mem : ByteArray) (ptr len : UInt256) : ByteArray :=
  len.toByteArray.write 0 (solcErrorDynamicMem1 mem ptr) (ptr + ⟨36⟩).toNat 32

def solcErrorDynamicMem3 (mem : ByteArray) (ptr len word : UInt256) : ByteArray :=
  word.toByteArray.write 0 (solcErrorDynamicMem2 mem ptr len) (ptr + ⟨68⟩).toNat 32

abbrev solcErrorDynamicWords0 (aw ptr : UInt256) : UInt256 := memoryWordActiveWords aw ptr

abbrev solcErrorDynamicWords1 (aw ptr : UInt256) : UInt256 :=
  memoryWordActiveWords (solcErrorDynamicWords0 aw ptr) (ptr + ⟨4⟩)

abbrev solcErrorDynamicWords2 (aw ptr : UInt256) : UInt256 :=
  memoryWordActiveWords (solcErrorDynamicWords1 aw ptr) (ptr + ⟨36⟩)

abbrev solcErrorDynamicWords3 (aw ptr : UInt256) : UInt256 :=
  memoryWordActiveWords (solcErrorDynamicWords2 aw ptr) (ptr + ⟨68⟩)

theorem solcErrorDynamicMem_sizes {mem : ByteArray} (ptr len word : UInt256)
    (hgap : ptr.toNat - mem.size < USize.size) (hfit : ptr.toNat + 68 < UInt256.size) :
    (solcErrorDynamicMem0 mem ptr).size = max mem.size (ptr.toNat + 32) ∧
    (solcErrorDynamicMem1 mem ptr).size = max mem.size (ptr.toNat + 36) ∧
    (solcErrorDynamicMem2 mem ptr len).size = max mem.size (ptr.toNat + 68) ∧
    (solcErrorDynamicMem3 mem ptr len word).size = max mem.size (ptr.toNat + 100) := by
  have h4 : (ptr + ⟨4⟩).toNat = ptr.toNat + 4 := uadd_word_ofNat_toNat ptr 4 (by omega)
  have h36 : (ptr + ⟨36⟩).toNat = ptr.toNat + 36 := uadd_word_ofNat_toNat ptr 36 (by omega)
  have h68 : (ptr + ⟨68⟩).toNat = ptr.toNat + 68 := uadd_word_ofNat_toNat ptr 68 hfit
  have hs0 : (solcErrorDynamicMem0 mem ptr).size = max mem.size (ptr.toNat + 32) :=
    writeWord_size mem ptr.toNat solcErrorStringSelector hgap
  have hs1 := toByteArray_write32_size_of_le (solcErrorDynamicMem0 mem ptr) ⟨32⟩ (ptr + ⟨4⟩).toNat
    (max mem.size (ptr.toNat + 32)) (max mem.size (ptr.toNat + 36)) hs0
      (by rw [h4]; rw [hs0]; omega) (by rw [h4]; omega)
  change (solcErrorDynamicMem1 mem ptr).size = max mem.size (ptr.toNat + 36) at hs1
  have hs2 := toByteArray_write32_size_of_le (solcErrorDynamicMem1 mem ptr) len (ptr + ⟨36⟩).toNat
    (max mem.size (ptr.toNat + 36)) (max mem.size (ptr.toNat + 68)) hs1
      (by rw [h36]; rw [hs1]; omega) (by rw [h36]; omega)
  change (solcErrorDynamicMem2 mem ptr len).size = max mem.size (ptr.toNat + 68) at hs2
  have hs3 :=
    toByteArray_write32_size_of_le (solcErrorDynamicMem2 mem ptr len) word (ptr + ⟨68⟩).toNat
    (max mem.size (ptr.toNat + 68)) (max mem.size (ptr.toNat + 100)) hs2
      (by rw [h68]; rw [hs2]; omega) (by rw [h68]; omega)
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
  have hb1 :=
    UInt256_ofNat_M_mul32_lt (solcErrorDynamicWords0 aw ptr) (ptr + ⟨4⟩) hb0 (by rw [h4]; omega)
  have hb2 :=
    UInt256_ofNat_M_mul32_lt (solcErrorDynamicWords1 aw ptr) (ptr + ⟨36⟩) hb1 (by rw [h36]; omega)
  have hb3 :=
    UInt256_ofNat_M_mul32_lt (solcErrorDynamicWords2 aw ptr) (ptr + ⟨68⟩) hb2 (by rw [h68]; omega)
  have hc3 :=
    UInt256_ofNat_M_covers (solcErrorDynamicWords2 aw ptr) (ptr + ⟨68⟩) hb2 (by rw [h68]; omega)
  refine ⟨hb3, ?_⟩
  change (ptr + ⟨68⟩).toNat + 32 ≤ (solcErrorDynamicWords3 aw ptr).toNat * 32 at hc3
  rw [h68] at hc3
  omega

theorem solcErrorDynamicMem3_mload64 {mem : ByteArray} (aw ptr len word : UInt256)
    (hin : 96 ≤ mem.size) (hlo : 96 ≤ ptr.toNat) (hgap : ptr.toNat - mem.size < USize.size)
    (hfit : ptr.toNat + 131 < UInt256.size) (haw : aw.toNat * 32 < UInt256.size)
    (hread : mem.readWithPadding 64 32 = ptr.toByteArray) :
    memoryWordLoad (solcErrorDynamicMem3 mem ptr len word) ⟨64⟩ = ptr ∧
    memoryWordActiveWords (solcErrorDynamicWords3 aw ptr) ⟨64⟩ = solcErrorDynamicWords3 aw ptr := by
  obtain ⟨hb, hc⟩ := solcErrorDynamicWords3_bounds aw ptr haw hfit
  have hcover : (⟨64⟩ : UInt256).toNat + 32 ≤ (solcErrorDynamicWords3 aw ptr).toNat * 32 := by
    change 64 + 32 ≤ _; omega
  refine ⟨?_, UInt256_M_same_of_cover _ _ hb hcover⟩
  apply mloadWordValue_of_readWithPadding
  · change 64 < _
    rw [(solcErrorDynamicMem_sizes ptr len word hgap (by omega)).2.2.2]; omega
  · exact (solcErrorDynamicMem3_read64 ptr len word hin hlo hgap (by omega)).trans hread

def wordBytes : List UInt256 → ByteArray
  | [] => ByteArray.empty
  | w :: ws => UInt256.toByteArray w ++ wordBytes ws

theorem wordBytes_size (ws : List UInt256) : (wordBytes ws).size = 32 * ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp only [wordBytes, ByteArray.size_append, toByteArray_size,
      ih, List.length_cons]; omega

theorem wordBytes_append (xs ys : List UInt256) :
    wordBytes (xs ++ ys) = wordBytes xs ++ wordBytes ys := by
  induction xs with
  | nil => simp [wordBytes]
  | cons w ws ih => simp only [List.cons_append, wordBytes, ih, ByteArray.append_assoc]

theorem wordBytes_eq_list (ws : List UInt256) :
    wordBytes ws = (ws.flatMap EVM.Word.toBytesBE).toByteArray := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [wordBytes, List.flatMap_cons, list_toByteArray_append,
      word_toBytesBE_toByteArray_eq_toByteArray, ih]

def returnMem (ws : List UInt256) : ByteArray :=
  (solcFreePtrMem ++ ByteArray.zeroes 32) ++ wordBytes ws

theorem returnMem_size (ws : List UInt256) : (returnMem ws).size = 128 + 32 * ws.length := by
  rw [returnMem, ByteArray.size_append, solcFreePtrMem_pad_size, wordBytes_size]

theorem returnMem_single (w : UInt256) : solcReturnMem w = returnMem [w] := by
  simpa only [returnMem, wordBytes, ByteArray.append_empty] using solcReturnMem_eq w

theorem returnMem_write (ws : List UInt256) (w : UInt256) :
    (UInt256.toByteArray w).write 0 (returnMem ws) (128 + 32 * ws.length) 32 =
      returnMem (ws ++ [w]) := by
  rw [← returnMem_size ws, write_at_end_eq _ _ 32 (by decide) (by rw [toByteArray_size]),
    toByteArray_extract_all]
  simp only [returnMem, wordBytes_append, wordBytes, ByteArray.append_empty,
    ByteArray.append_assoc]

theorem returnMem_read64 (ws : List UInt256) :
    (returnMem ws).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  rw [readWithPadding_eq_extract _ _ (by rw [returnMem_size]; omega), returnMem,
    extract_append_left _ _ _ _ (by rw [solcFreePtrMem_pad_size]; omega),
    extract_append_left _ _ _ _ (by rw [solcFreePtrMem_size]),
    ← readWithPadding_eq_extract _ _ (by rw [solcFreePtrMem_size]),
    solcFreePtrMem_read64]

theorem returnMem_read128 (ws : List UInt256) (hpos : 0 < ws.length)
    (hsize : 32 * ws.length < 2 ^ 64) :
    (returnMem ws).readWithPadding 128 (32 * ws.length) = wordBytes ws := by
  rw [readWithPadding_eq_extract' _ _ _ (by omega) hsize (by rw [returnMem_size])]
  exact extract_append_right' _ _ _ _ (by rw [solcFreePtrMem_pad_size])
    (by rw [solcFreePtrMem_pad_size, wordBytes_size])

def errorStringMem4 (len first second : UInt256) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray second).write 0 (solcErrorStringMem3 len first mem) 228 32

theorem errorStringMem4_size (len first second : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) : (errorStringMem4 len first second mem).size = 260 := by
  exact toByteArray_write32_size_of_ge _ second 228 228 260
    (solcErrorStringMem3_size len first hmem) (by decide)
    (lt_usize _ (by norm_num)) (by decide)

theorem errorStringMem4_read64 (len first second : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (errorStringMem4 len first second mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold errorStringMem4
  rw [toByteArray_write_read_below_of_gap second _ 228 64
    (by rw [solcErrorStringMem3_size len first hmem]; decide) (by decide)
    (by rw [solcErrorStringMem3_size len first hmem]; exact lt_usize _ (by norm_num))]
  exact solcErrorStringMem3_read64 len first hmem hread

theorem errorStringMem4_mload64 (len first second : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (errorStringMem4 len first second mem).size then ⟨0⟩ else
      UInt256.ofNat (fromByteArrayBigEndian
        ((errorStringMem4 len first second mem).readWithPadding 64 32))) = ⟨128⟩ := by
  exact mloadFreePtrValue (by rw [errorStringMem4_size len first second hmem]; decide)
    (errorStringMem4_read64 len first second hmem hread)

end Reasoning.Theory
