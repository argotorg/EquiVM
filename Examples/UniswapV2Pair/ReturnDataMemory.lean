import Examples.UniswapV2Pair.MemorySteps

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

-- GENERALIZES Reasoning.Memory.write0_read_back_gen to an arbitrary destination.
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

-- LIBRARY CANDIDATE: exact size for copying a whole byte array inside or at the end of memory.
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

-- LIBRARY CANDIDATES: Solidity's dynamic return-data allocation and copy.
noncomputable def solcReturnDataPtrMem (mem : ByteArray) (ptr : UInt256) (out : ByteArray) : ByteArray :=
  (ptr + UInt256.land (UInt256.ofNat out.size + ⟨63⟩) (UInt256.lnot ⟨31⟩)).toByteArray.write 0 mem 64 32

noncomputable def solcReturnDataSizeMem (mem : ByteArray) (ptr : UInt256) (out : ByteArray) : ByteArray :=
  (UInt256.ofNat out.size).toByteArray.write 0 (solcReturnDataPtrMem mem ptr out) ptr.toNat 32

noncomputable def solcReturnDataMem (mem : ByteArray) (ptr : UInt256) (out : ByteArray) : ByteArray :=
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
  have h := toByteArray_write32_size_of_le (solcReturnDataPtrMem mem ptr out) (UInt256.ofNat out.size)
    ptr.toNat mem.size mem.size hs (by rw [hs]; omega) (by omega)
  exact h

theorem solcReturnDataMem_size {mem : ByteArray} (ptr : UInt256) (out : ByteArray)
    (hin : 96 ≤ mem.size) (hptr : ptr.toNat + 32 ≤ mem.size) (hfit : ptr.toNat + 32 < UInt256.size) :
    (solcReturnDataMem mem ptr out).size = max mem.size (ptr.toNat + 32 + out.size) := by
  have h32 : (ptr + ⟨32⟩).toNat = ptr.toNat + 32 := uadd_word_ofNat_toNat ptr 32 hfit
  have hs := solcReturnDataSizeMem_size ptr out hin hptr
  have h := byteArray_write_all_size out (solcReturnDataSizeMem mem ptr out) (ptr + ⟨32⟩).toNat
    (by rw [h32, hs]; omega)
  change (solcReturnDataMem mem ptr out).size = _ at h
  rw [h32, hs] at h
  exact h

theorem solcReturnDataMem_read_size {mem : ByteArray} (ptr : UInt256) (out : ByteArray)
    (hin : 96 ≤ mem.size) (hptr : ptr.toNat + 32 ≤ mem.size) (hfit : ptr.toNat + 32 < UInt256.size) :
    (solcReturnDataMem mem ptr out).readWithPadding ptr.toNat 32 = (UInt256.ofNat out.size).toByteArray := by
  have h32 : (ptr + ⟨32⟩).toNat = ptr.toNat + 32 := uadd_word_ofNat_toNat ptr 32 hfit
  have hs := solcReturnDataSizeMem_size ptr out hin hptr
  have hsPtr := solcReturnDataPtrMem_size ptr out hin
  unfold solcReturnDataMem
  by_cases hz : out.size = 0
  · rw [hz, byteArray_write_len_zero]
    unfold solcReturnDataSizeMem
    have h := toByteArray_write32_read_back (solcReturnDataPtrMem mem ptr out) (UInt256.ofNat out.size)
      ptr.toNat (by rw [hsPtr]; omega)
    exact h.trans (congrArg (fun n => (UInt256.ofNat n).toByteArray) hz)
  · rw [write_read_below_gen_extend out _ (ptr + ⟨32⟩).toNat out.size ptr.toNat hz le_rfl
      (by rw [h32, hs]; omega) (by rw [h32])]
    unfold solcReturnDataSizeMem
    have h := toByteArray_write32_read_back (solcReturnDataPtrMem mem ptr out) (UInt256.ofNat out.size)
      ptr.toNat (by rw [hsPtr]; omega)
    exact h

theorem solcReturnDataMem_read_word {mem : ByteArray} (ptr : UInt256) (out : ByteArray)
    (hin : 96 ≤ mem.size) (hptr : ptr.toNat + 32 ≤ mem.size) (hfit : ptr.toNat + 32 < UInt256.size)
    (hout : 32 ≤ out.size) :
    (solcReturnDataMem mem ptr out).readWithPadding (ptr + ⟨32⟩).toNat 32 = out.extract 0 32 := by
  have h32 : (ptr + ⟨32⟩).toNat = ptr.toNat + 32 := uadd_word_ofNat_toNat ptr 32 hfit
  have hs := solcReturnDataSizeMem_size ptr out hin hptr
  have h := byteArray_write_prefix32 out (solcReturnDataSizeMem mem ptr out) (ptr + ⟨32⟩).toNat hout (by rw [h32, hs]; omega)
  exact h

theorem solcReturnDataActiveWords_bounds (aw ptr : UInt256) (out : ByteArray)
    (haw : aw.toNat * 32 < UInt256.size) (hfit : ptr.toNat + out.size + 95 < UInt256.size) :
    (solcReturnDataActiveWords aw ptr out).toNat * 32 < UInt256.size ∧
      aw.toNat ≤ (solcReturnDataActiveWords aw ptr out).toNat := by
  have h32 : (ptr + ⟨32⟩).toNat = ptr.toNat + 32 := uadd_word_ofNat_toNat ptr 32 (by omega)
  have hM := MachineState_M_mul32_lt_of_bounds haw (show (ptr + ⟨32⟩).toNat + out.size + 31 < UInt256.size by rw [h32]; omega)
  have hMlt : MachineState.M aw.toNat (ptr + ⟨32⟩).toNat out.size < UInt256.size := by omega
  change (UInt256.ofNat (MachineState.M aw.toNat (ptr + ⟨32⟩).toNat out.size)).toNat * 32 < UInt256.size ∧
    aw.toNat ≤ (UInt256.ofNat (MachineState.M aw.toNat (ptr + ⟨32⟩).toNat out.size)).toNat
  rw [UInt256.toNat_ofNat_of_lt hMlt]
  exact ⟨hM, MachineState_M_ge_left _ _ _⟩

theorem solcReturnDataMem_mload_size {mem : ByteArray} (aw ptr : UInt256) (out : ByteArray)
    (hin : 96 ≤ mem.size) (hptr : ptr.toNat + 32 ≤ mem.size)
    (hcover : ptr.toNat + 64 ≤ aw.toNat * 32)
    (haw : aw.toNat * 32 < UInt256.size) (hfit : ptr.toNat + out.size + 95 < UInt256.size) :
    memoryWordLoad (solcReturnDataMem mem ptr out) (solcReturnDataActiveWords aw ptr out) ptr = UInt256.ofNat out.size ∧
    memoryWordActiveWords (solcReturnDataActiveWords aw ptr out) ptr = solcReturnDataActiveWords aw ptr out := by
  obtain ⟨hb, hge⟩ := solcReturnDataActiveWords_bounds aw ptr out haw hfit
  have hc : ptr.toNat + 32 ≤ (solcReturnDataActiveWords aw ptr out).toNat * 32 := by omega
  constructor
  · apply mloadWordValue_of_readWithPadding
    · rw [solcReturnDataMem_size ptr out hin hptr (by omega)]
      omega
    · exact UInt256_mload_haw_of_cover _ _ hb hc
    · exact solcReturnDataMem_read_size ptr out hin hptr (by omega)
  · exact UInt256_M_same_of_cover _ _ hb hc

theorem solcReturnDataMem_mload_word {mem : ByteArray} (aw ptr : UInt256) (out : ByteArray)
    (hin : 96 ≤ mem.size) (hptr : ptr.toNat + 32 ≤ mem.size)
    (hcover : ptr.toNat + 64 ≤ aw.toNat * 32)
    (haw : aw.toNat * 32 < UInt256.size) (hfit : ptr.toNat + out.size + 95 < UInt256.size)
    (hout : 32 ≤ out.size) :
    memoryWordLoad (solcReturnDataMem mem ptr out) (solcReturnDataActiveWords aw ptr out) (ptr + ⟨32⟩) =
      UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)) ∧
    memoryWordActiveWords (solcReturnDataActiveWords aw ptr out) (ptr + ⟨32⟩) = solcReturnDataActiveWords aw ptr out := by
  have h32 : (ptr + ⟨32⟩).toNat = ptr.toNat + 32 := uadd_word_ofNat_toNat ptr 32 (by omega)
  obtain ⟨hb, hge⟩ := solcReturnDataActiveWords_bounds aw ptr out haw hfit
  have hc : (ptr + ⟨32⟩).toNat + 32 ≤ (solcReturnDataActiveWords aw ptr out).toNat * 32 := by rw [h32]; omega
  constructor
  · have hm := mloadValue_eq_readWithPadding_of_lt_size (solcReturnDataMem mem ptr out)
      (solcReturnDataActiveWords aw ptr out) (ptr + ⟨32⟩) _
      (solcReturnDataMem_size ptr out hin hptr (by omega)) (by rw [h32]; omega)
      (UInt256_mload_haw_of_cover _ _ hb hc)
    exact hm.trans (congrArg (fun bytes => UInt256.ofNat (fromByteArrayBigEndian bytes))
      (solcReturnDataMem_read_word ptr out hin hptr (by omega) hout))
  · exact UInt256_M_same_of_cover _ _ hb hc

-- LIBRARY CANDIDATE: the allocation size used by Solidity for return data.
theorem solcReturnDataRounded_toNat (size : Nat) (hfit : size + 63 < UInt256.size) :
    (UInt256.land (UInt256.ofNat size + ⟨63⟩) (UInt256.lnot ⟨31⟩)).toNat = (size + 63) / 32 * 32 := by
  rw [u256_land_comm]
  rw [show UInt256.lnot ⟨31⟩ = UInt256.ofNat (2 ^ 256 - 2 ^ 5) by native_decide,
    u256_land_high_mask_toNat _ 5 (by omega)]
  rw [uadd_toNat, UInt256.toNat_ofNat_of_lt (by omega)]
  change ((size + 63) % UInt256.size) / 32 * 32 = (size + 63) / 32 * 32
  rw [Nat.mod_eq_of_lt hfit]

theorem solcReturnDataMem_read_below_ptr {mem : ByteArray} (ptr : UInt256) (out : ByteArray) (read : Nat)
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
    · have h := write_read_below_gen_extend out (solcReturnDataSizeMem mem ptr out) (ptr + ⟨32⟩).toNat out.size read hz le_rfl
        (by rw [h32, hsSize]; omega) (by rw [h32]; omega)
      exact h
  rw [hcopy]
  unfold solcReturnDataSizeMem
  exact write32_read_below _ _ ptr.toNat read (by rw [toByteArray_size]) (by rw [hsPtr]; omega) hread

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

end UniswapV2Pair
