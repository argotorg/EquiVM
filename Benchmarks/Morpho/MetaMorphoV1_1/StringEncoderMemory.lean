import Benchmarks.Morpho.MetaMorphoV1_1.StringMemoryRead

/-! A dynamic ABI string tail: length, payload copy, and zero padding. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1

-- LIBRARY CANDIDATE: the dynamic tail of a string in a composite ABI return value.
def stringPayloadBytes (bytes : ByteArray) : ByteArray :=
  (UInt256.ofNat bytes.size).toByteArray ++
    (bytes ++ ByteArray.zeroes (paddedSize bytes.size - bytes.size))

def stringPayloadCopy (mem : ByteArray) (src dest : Nat) (len : UInt256) : ByteArray :=
  let header := writeWord mem dest len
  header.write src header (dest + 32) len.toNat

def stringPayloadMemory (mem : ByteArray) (src dest : Nat) (len : UInt256) : ByteArray :=
  writeWord (stringPayloadCopy mem src dest len) (dest + 32 + len.toNat) ⟨0⟩

theorem stringPayloadCopy_size (mem : ByteArray) (src dest : Nat) (len : UInt256)
    (hin : src + len.toNat ≤ mem.size) :
    (stringPayloadCopy mem src dest len).size = max mem.size (dest + 32 + len.toNat) := by
  unfold stringPayloadCopy
  by_cases hz : len.toNat = 0
  · rw [hz, byteArray_write_len_zero, writeWord_sparse_size, Nat.add_zero]
  · rw [copyWindow_size _ _ _ _ _ hz (by rw [writeWord_sparse_size]; omega)
      (by rw [writeWord_sparse_size]; omega), writeWord_sparse_size]
    omega

theorem stringPayloadCopy_read (mem : ByteArray) (src dest : Nat) (len : UInt256)
    (hin : src + len.toNat ≤ mem.size) (hbelow : src + len.toNat ≤ dest) :
    (stringPayloadCopy mem src dest len).readWithPadding (dest + 32) len.toNat =
      mem.readWithPadding src len.toNat := by
  by_cases hz : len.toNat = 0
  · simp only [hz, byteArray_readWithPadding_zero]
  · have hh : src + len.toNat ≤ (writeWord mem dest len).size := by
      rw [writeWord_sparse_size]; omega
    rw [readWithPadding_eq_extract_unbounded _ _ _ (by omega)
      (by rw [stringPayloadCopy_size _ _ _ _ hin]; omega)]
    unfold stringPayloadCopy
    have hc := copyWindow_extract (writeWord mem dest len) (writeWord mem dest len)
      src (dest + 32) len.toNat 0 len.toNat hz hh
      (by rw [writeWord_sparse_size]; omega) (by omega)
    simp only [Nat.add_zero] at hc
    rw [hc, ← readWithPadding_eq_extract_unbounded _ _ _ (by omega) hh,
      writeWord_sparse_read_preserved_unbounded _ _ _ _ _ hin (.inl hbelow)]

theorem stringPayloadCopy_word (mem : ByteArray) (src dest read : Nat) (len : UInt256)
    (hin : src + len.toNat ≤ mem.size) (hread : read + 32 ≤ dest + 32) :
    (stringPayloadCopy mem src dest len).readWithPadding read 32 =
      (writeWord mem dest len).readWithPadding read 32 := by
  unfold stringPayloadCopy
  by_cases hz : len.toNat = 0
  · rw [hz, byteArray_write_len_zero]
  · exact copyWindow_read_preserved _ _ _ _ _ _ hz
      (by rw [writeWord_sparse_size]; omega) (by rw [writeWord_sparse_size]; omega)
      (by rw [writeWord_sparse_size]; omega) (.inl hread)

theorem stringPayloadMemory_size (mem : ByteArray) (src dest : Nat) (len : UInt256)
    (hin : src + len.toNat ≤ mem.size) :
    (stringPayloadMemory mem src dest len).size =
      max mem.size (dest + 32 + len.toNat + 32) := by
  rw [stringPayloadMemory, writeWord_sparse_size, stringPayloadCopy_size _ _ _ _ hin]
  omega

theorem stringPayloadMemory_prefix (mem : ByteArray) (src dest : Nat) (len : UInt256)
    (hin : src + len.toNat ≤ mem.size) :
    MemoryPrefix mem (stringPayloadMemory mem src dest len) dest := by
  refine ⟨by rw [stringPayloadMemory_size _ _ _ _ hin]; omega, ?_⟩
  intro read hlo hhi hmem
  rw [stringPayloadMemory, writeWord_sparse_read_preserved _ _ _ _
    (.inl ⟨by omega, by rw [stringPayloadCopy_size _ _ _ _ hin]; omega⟩),
    stringPayloadCopy_word _ _ _ _ _ hin (by omega),
    writeWord_sparse_read_preserved _ _ _ _ (.inl ⟨hhi, hmem⟩)]

theorem stringPayloadMemory_read (mem bytes : ByteArray) (src dest : Nat) (len : UInt256)
    (hsize : bytes.size = len.toNat) (hin : src + len.toNat ≤ mem.size)
    (hbelow : src + len.toNat ≤ dest) (hread : mem.readWithPadding src len.toNat = bytes) :
    (stringPayloadMemory mem src dest len).readWithPadding dest (32 + paddedSize len.toNat) =
      stringPayloadBytes bytes := by
  have hpad : paddedSize len.toNat - len.toNat ≤ 31 := by unfold paddedSize; omega
  have hlen : len.toNat ≤ paddedSize len.toNat := by unfold paddedSize; omega
  have hmem : dest + 32 + len.toNat + 32 ≤ (stringPayloadMemory mem src dest len).size := by
    rw [stringPayloadMemory_size _ _ _ _ hin]
    exact Nat.le_max_right _ _
  have hlength : (stringPayloadMemory mem src dest len).readWithPadding dest 32 =
      len.toByteArray := by
    rw [stringPayloadMemory, writeWord_sparse_read_preserved _ _ _ _
      (.inl ⟨by omega, by rw [stringPayloadCopy_size _ _ _ _ hin]; omega⟩),
      stringPayloadCopy_word _ _ _ _ _ hin (by omega), writeWord_sparse_read_back]
  have hdata : (stringPayloadMemory mem src dest len).readWithPadding
      (dest + 32) len.toNat = bytes := by
    rw [stringPayloadMemory, writeWord_sparse_read_preserved_unbounded _ _ _ _ _
      (by rw [stringPayloadCopy_size _ _ _ _ hin]; omega) (.inl (by omega)),
      stringPayloadCopy_read _ _ _ _ hin hbelow, hread]
  have hzero : (stringPayloadMemory mem src dest len).readWithPadding (dest + 32 + len.toNat)
      (paddedSize len.toNat - len.toNat) = ByteArray.zeroes (paddedSize len.toNat - len.toNat) := by
    by_cases hz : paddedSize len.toNat - len.toNat = 0
    · rw [hz, byteArray_readWithPadding_zero]
      exact (zeroes_zero (by rfl)).symm
    · have hr := writeWord_sparse_read_window (stringPayloadCopy mem src dest len)
        (dest + 32 + len.toNat) 0 (paddedSize len.toNat - len.toNat) ⟨0⟩
        (by omega) (by omega) (by omega)
      simpa only [Nat.add_zero, Nat.zero_add, zero_toByteArray_eq_zeroes32,
        zeroes32_extract_zeroes (paddedSize len.toNat - len.toNat) (by omega)] using hr
  rw [show 32 + paddedSize len.toNat =
    32 + (len.toNat + (paddedSize len.toNat - len.toNat)) by omega,
    readWithPadding_split _ _ _ _ (by omega), hlength,
    readWithPadding_split _ _ _ _ (by omega), hdata, hzero]
  simp only [stringPayloadBytes, hsize, u256_ofNat_toNat]

end Benchmarks.Morpho.MetaMorphoV1_1
