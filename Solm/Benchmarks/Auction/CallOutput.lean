import Solm.Benchmarks.Auction.CallBridge
import Solm.Benchmarks.Auction.HeapMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

-- LIBRARY CANDIDATE: CALL copies only min(output size, returndata size) bytes.
theorem callOutputLen32 {out : ByteArray} (hb : out.size < UInt256.size) :
    (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat = min 32 out.size := by
  have hn := ulit_toNat' out.size hb
  by_cases hs : 32 ≤ out.size
  · have hw : (⟨32⟩ : UInt256) ≤ UInt256.ofNat out.size := by
      change 32 ≤ (UInt256.ofNat out.size).toNat
      omega
    simp only [min, hw, if_true]
    change 32 = _
    exact (Nat.min_eq_left hs).symm
  · have hw : ¬ (⟨32⟩ : UInt256) ≤ UInt256.ofNat out.size := by
      change ¬ 32 ≤ (UInt256.ofNat out.size).toNat
      omega
    simp only [min, hw, if_false, hn]
    exact (Nat.min_eq_right (by omega)).symm

theorem callOutput32_size (mem out : ByteArray) (ptr : UInt256)
    (hb : out.size < UInt256.size) (hin : ptr.toNat + 32 ≤ mem.size) :
    (callOutputMem mem out ptr ⟨32⟩).size = mem.size := by
  unfold callOutputMem
  rw [callOutputLen32 hb]
  by_cases hz : min 32 out.size = 0
  · rw [hz, byteArray_write_len_zero]
  · rw [write_eq_gen out mem ptr.toNat (min 32 out.size) hz (Nat.min_le_right _ _)
      (by omega)]
    simp only [ByteArray.size_append, ByteArray.size_extract]
    omega

theorem callOutput32_read_below (mem out : ByteArray) (ptr : UInt256) (off : Nat)
    (hb : out.size < UInt256.size) (hin : ptr.toNat + 32 ≤ mem.size)
    (hbelow : off + 32 ≤ ptr.toNat) :
    (callOutputMem mem out ptr ⟨32⟩).readWithPadding off 32 =
      mem.readWithPadding off 32 := by
  unfold callOutputMem
  rw [callOutputLen32 hb]
  by_cases hz : min 32 out.size = 0
  · rw [hz, byteArray_write_len_zero]
  · exact write_read_below_gen_extend out mem ptr.toNat (min 32 out.size) off hz
      (Nat.min_le_right _ _) (by omega) hbelow

theorem callOutput32_prefix (mem out : ByteArray) (ptr : UInt256)
    (hb : out.size < UInt256.size) (hin : ptr.toNat + 32 ≤ mem.size) :
    MemoryPrefix mem (callOutputMem mem out ptr ⟨32⟩) ptr.toNat :=
  ⟨(callOutput32_size mem out ptr hb hin).ge,
    fun off _ hbelow _ => callOutput32_read_below mem out ptr off hb hin hbelow⟩

theorem callOutput32_heap {mem aw ptr} (h : HeapMemory mem aw ptr) (out : ByteArray)
    (hb : out.size < UInt256.size) (hin : ptr.toNat + 32 ≤ mem.size) :
    HeapMemory (callOutputMem mem out ptr ⟨32⟩) aw ptr := by
  have hs := callOutput32_size mem out ptr hb hin
  exact ⟨by rw [hs]; exact h.size,
    (callOutput32_read_below mem out ptr 64 hb hin (by have hp := h.lower; omega)).trans h.free,
    h.lower, by rw [hs]; exact h.gap, h.active⟩

-- LIBRARY CANDIDATE: the word decoder/encoder round trip at any in-bounds byte offset.
theorem calldataWord_bytes_at {out : ByteArray} {off : Nat} (hs : off + 32 ≤ out.size) :
    (calldataWord out off).toByteArray = out.extract off (off + 32) := by
  have hl : ((out.toList.drop off).take 32).length = 32 := by
    simp only [List.length_take, List.length_drop, byteArray_toList_eq, Array.length_toList]
    change min 32 (out.size - off) = 32
    omega
  have hw := toBytesBE_bytesToWord_of_length hl
  rw [decode_word_at_eq_any out off hs] at hw
  rw [toByteArray_eq_toBytesBE, hw]
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp [ByteArray.data_extract, Array.toList_extract, List.extract, byteArray_toList_eq]

theorem calldataWord_bytes {out : ByteArray} (hs : 32 ≤ out.size) :
    (calldataWord out 0).toByteArray = out.extract 0 32 :=
  calldataWord_bytes_at hs

theorem callOutput32_read_word (mem out : ByteArray) (ptr : UInt256)
    (hb : out.size < UInt256.size) (hs : 32 ≤ out.size) (hin : ptr.toNat ≤ mem.size) :
    (callOutputMem mem out ptr ⟨32⟩).readWithPadding ptr.toNat 32 =
      (calldataWord out 0).toByteArray := by
  unfold callOutputMem
  rw [callOutputLen32 hb, Nat.min_eq_left hs, write32_read_back out mem ptr.toNat hs hin,
    calldataWord_bytes hs]

theorem memoryWords_bounds (aw off size : Nat) (ha : aw ≤ 2 ^ 200)
    (hb : off + size ≤ 2 ^ 200) :
    aw ≤ MachineState.M aw off size ∧ MachineState.M aw off size ≤ 2 ^ 200 := by
  unfold MachineState.M
  split <;> omega

theorem callActiveWords_toNat {aw inOff inSize outOff outSize : UInt256} (ha : ActiveWords aw)
    (hi : inOff.toNat + inSize.toNat ≤ 2 ^ 200)
    (ho : outOff.toNat + outSize.toNat ≤ 2 ^ 200) :
    (callActiveWords aw inOff inSize outOff outSize).toNat =
      MachineState.M (MachineState.M aw.toNat inOff.toNat inSize.toNat)
        outOff.toNat outSize.toNat := by
  have hm1 := memoryWords_bounds aw.toNat inOff.toNat inSize.toNat ha.2 hi
  have hm2 := memoryWords_bounds (MachineState.M aw.toNat inOff.toNat inSize.toNat)
    outOff.toNat outSize.toNat hm1.2 ho
  apply ulit_toNat'
  change _ < 2 ^ 256
  omega

theorem callActiveWords_active {aw inOff inSize outOff outSize : UInt256} (ha : ActiveWords aw)
    (hi : inOff.toNat + inSize.toNat ≤ 2 ^ 200)
    (ho : outOff.toNat + outSize.toNat ≤ 2 ^ 200) :
    ActiveWords (callActiveWords aw inOff inSize outOff outSize) := by
  have hm1 := memoryWords_bounds aw.toNat inOff.toNat inSize.toNat ha.2 hi
  have hm2 := memoryWords_bounds (MachineState.M aw.toNat inOff.toNat inSize.toNat)
    outOff.toNat outSize.toNat hm1.2 ho
  unfold ActiveWords
  rw [callActiveWords_toNat ha hi ho]
  exact ⟨le_trans (le_trans ha.1 hm1.1) hm2.1, hm2.2⟩

theorem callActiveWords_cover32 {aw inOff inSize outOff : UInt256} (ha : ActiveWords aw)
    (hi : inOff.toNat + inSize.toNat ≤ 2 ^ 200) (ho : outOff.toNat + 32 ≤ 2 ^ 200) :
    outOff.toNat < (callActiveWords aw inOff inSize outOff ⟨32⟩).toNat * 32 := by
  rw [callActiveWords_toNat ha hi ho]
  change outOff.toNat < max _ ((outOff.toNat + 32 + 31) / 32) * 32
  omega

end Auction
