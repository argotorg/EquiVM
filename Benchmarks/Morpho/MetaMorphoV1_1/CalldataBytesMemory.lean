import Benchmarks.Morpho.MetaMorphoV1_1.CalldataBytesRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.StringBuffer

/-! Length, payload, and free-pointer facts after dynamic calldata copying. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false
set_option maxRecDepth 2000

theorem calldataBytesMemory_normalize (mem cd : ByteArray) (ptr start len : UInt256)
    (hp : ptr.toNat < 2 ^ 64) (hl : len.toNat < 2 ^ 64) :
    calldataBytesMemory mem cd ptr start len =
      writeWord
        (cd.write start.toNat
          (writeWord (writeWord mem 64 (bytesAllocPtr ptr len.toNat)) ptr.toNat len)
          (ptr.toNat + 32) len.toNat)
        (ptr.toNat + 32 + len.toNat) ⟨0⟩ := by
  have h32 : (ptr + (⟨32⟩ : UInt256)).toNat = ptr.toNat + 32 :=
    uadd_word_ofNat_toNat ptr 32 (by change _ < 2 ^ 256; omega)
  have hend : ((ptr + len) + (⟨32⟩ : UInt256)).toNat = ptr.toNat + 32 + len.toNat := by
    have ha : (ptr + len).toNat = ptr.toNat + len.toNat := by
      rw [uadd_toNat, Nat.mod_eq_of_lt (by change _ < 2 ^ 256; omega)]
    rw [uadd_toNat, ha]
    change (ptr.toNat + len.toNat + 32) % UInt256.size = _
    rw [Nat.mod_eq_of_lt (by change _ < 2 ^ 256; omega)]
    omega
  simp only [calldataBytesMemory, h32, hend]

theorem calldataBytesMemory_size (mem cd : ByteArray) (ptr start len : UInt256)
    (hp : ptr.toNat < 2 ^ 64) (hl : len.toNat < 2 ^ 64) (hlo : 96 ≤ ptr.toNat)
    (hsrc : start.toNat + len.toNat ≤ cd.size) :
    (calldataBytesMemory mem cd ptr start len).size =
      max mem.size (ptr.toNat + 64 + len.toNat) := by
  rw [calldataBytesMemory_normalize mem cd ptr start len hp hl, writeWord_sparse_size]
  by_cases hz : len.toNat = 0
  · rw [hz, byteArray_write_len_zero]
    simp only [writeWord_sparse_size]
    omega
  · rw [copyWindow_size _ _ _ _ _ hz hsrc
      (by simp only [writeWord_sparse_size]; omega)]
    simp only [writeWord_sparse_size]
    omega

-- LIBRARY CANDIDATE: a calldata copy and its final zero word preserve the preceding memory.
theorem calldataBytesMemory_read_before_data (mem cd : ByteArray) (ptr start len : UInt256)
    (hp : ptr.toNat < 2 ^ 64) (hl : len.toNat < 2 ^ 64)
    (hsrc : start.toNat + len.toNat ≤ cd.size) (read : Nat)
    (hread : read + 32 ≤ ptr.toNat + 32)
    (hin : read + 32 ≤
      (writeWord (writeWord mem 64 (bytesAllocPtr ptr len.toNat)) ptr.toNat len).size) :
    (calldataBytesMemory mem cd ptr start len).readWithPadding read 32 =
      (writeWord (writeWord mem 64 (bytesAllocPtr ptr len.toNat)) ptr.toNat len).readWithPadding
        read 32 := by
  rw [calldataBytesMemory_normalize mem cd ptr start len hp hl]
  by_cases hz : len.toNat = 0
  · simp only [hz] at hin
    rw [hz, byteArray_write_len_zero]
    exact writeWord_sparse_read_preserved _ _ _ _ (.inl ⟨by omega, hin⟩)
  · have hd : ptr.toNat + 32 ≤
        (writeWord (writeWord mem 64 (bytesAllocPtr ptr len.toNat)) ptr.toNat len).size := by
      simp only [writeWord_sparse_size]; omega
    rw [writeWord_sparse_read_preserved _ _ _ _ (.inl ⟨by omega, by
      rw [copyWindow_size _ _ _ _ _ hz hsrc hd]; omega⟩)]
    exact copyWindow_read_preserved _ _ _ _ _ _ hz hsrc hd hin (.inl hread)

theorem calldataBytesMemory_length (mem cd : ByteArray) (ptr start len : UInt256)
    (hp : ptr.toNat < 2 ^ 64) (hl : len.toNat < 2 ^ 64)
    (hsrc : start.toNat + len.toNat ≤ cd.size) :
    memLoad ptr (calldataBytesMemory mem cd ptr start len) = len := by
  apply mloadWordValue_of_readWithPadding
  · rw [calldataBytesMemory_normalize mem cd ptr start len hp hl, writeWord_sparse_size]
    omega
  · rw [calldataBytesMemory_read_before_data mem cd ptr start len hp hl hsrc ptr.toNat
      (by omega) (by simp only [writeWord_sparse_size]; omega)]
    exact writeWord_sparse_read_back _ _ _

theorem calldataBytesMemory_free (mem cd : ByteArray) (ptr start len : UInt256)
    (hp : ptr.toNat < 2 ^ 64) (hl : len.toNat < 2 ^ 64) (hlo : 96 ≤ ptr.toNat)
    (hsrc : start.toNat + len.toNat ≤ cd.size) :
    memLoad ⟨64⟩ (calldataBytesMemory mem cd ptr start len) = bytesAllocPtr ptr len.toNat := by
  apply mloadWordValue_of_readWithPadding
  · rw [calldataBytesMemory_size mem cd ptr start len hp hl hlo hsrc]
    change 64 < _
    omega
  · change ByteArray.readWithPadding _ 64 32 = _
    rw [calldataBytesMemory_read_before_data mem cd ptr start len hp hl hsrc 64
      (by omega) (by simp only [writeWord_sparse_size]; omega)]
    rw [writeWord_sparse_read_preserved _ ptr.toNat 64 _
      (.inl ⟨hlo, by rw [writeWord_sparse_size]; omega⟩)]
    exact writeWord_sparse_read_back _ _ _

theorem calldataBytesMemory_data (mem cd : ByteArray) (ptr start len : UInt256)
    (hp : ptr.toNat < 2 ^ 64) (hl : len.toNat < 2 ^ 64)
    (hsrc : start.toNat + len.toNat ≤ cd.size) :
    (calldataBytesMemory mem cd ptr start len).readWithPadding (ptr.toNat + 32) len.toNat =
      cd.extract start.toNat (start.toNat + len.toNat) := by
  by_cases hz : len.toNat = 0
  · rw [hz, byteArray_readWithPadding_zero]
    exact (byteArray_extract_empty_of_le cd (by omega)).symm
  rw [calldataBytesMemory_normalize mem cd ptr start len hp hl]
  have hd : ptr.toNat + 32 ≤
      (writeWord (writeWord mem 64 (bytesAllocPtr ptr len.toNat)) ptr.toNat len).size := by
    simp only [writeWord_sparse_size]; omega
  have hc := copyWindow_size cd
    (writeWord (writeWord mem 64 (bytesAllocPtr ptr len.toNat)) ptr.toNat len)
    start.toNat (ptr.toNat + 32) len.toNat hz hsrc hd
  rw [writeWord_read_preserved_len _ _ _ _ _
    (by rw [hc, Nat.sub_eq_zero_of_le (Nat.le_max_right _ _)]; exact lt_usize 0 (by decide))
    (.inl ⟨by omega, by rw [hc]; omega⟩) (by omega) hl]
  rw [readWithPadding_eq_extract_unbounded _ _ _ (by omega) (by rw [hc]; omega)]
  simpa only [Nat.add_zero] using copyWindow_extract cd
    (writeWord (writeWord mem 64 (bytesAllocPtr ptr len.toNat)) ptr.toNat len)
    start.toNat (ptr.toNat + 32) len.toNat 0 len.toNat hz hsrc hd (by omega)

theorem calldataBytesMemory_buffer (mem cd : ByteArray) (ptr start len : UInt256)
    (hp : ptr.toNat < 2 ^ 64) (hl : len.toNat < 2 ^ 64) (hlo : 96 ≤ ptr.toNat)
    (hsrc : start.toNat + len.toNat ≤ cd.size) :
    StringBuffer (calldataBytesMemory mem cd ptr start len) ptr.toNat
      (cd.extract start.toNat (start.toNat + len.toNat)) := by
  have hs : (cd.extract start.toNat (start.toNat + len.toNat)).size = len.toNat := by
    rw [ByteArray.size_extract]; omega
  refine ⟨?_, ?_, ?_⟩
  · rw [hs, calldataBytesMemory_size mem cd ptr start len hp hl hlo hsrc]
    unfold paddedSize
    omega
  · simp only [hs, u256_ofNat_toNat]
    exact calldataBytesMemory_length mem cd ptr start len hp hl hsrc
  · rw [hs]
    exact calldataBytesMemory_data mem cd ptr start len hp hl hsrc

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
