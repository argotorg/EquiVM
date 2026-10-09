import Benchmarks.Safe.CalldataBufferMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Safe

-- GENERALIZES calldataBufferMemory to ABI tails without updating the free-memory pointer.
def calldataBytesEncodedInto (cd mem : ByteArray) (src dst len : Nat) : ByteArray :=
  writeWord (cd.write src (writeWord mem dst (UInt256.ofNat len)) (dst + 32) len)
    (dst + 32 + len) ⟨0⟩

theorem calldataBytesEncodedInto_size (cd mem : ByteArray) (src dst len : Nat)
    (hs : src + len ≤ cd.size) :
    (calldataBytesEncodedInto cd mem src dst len).size = max mem.size (dst + 64 + len) := by
  rw [calldataBytesEncodedInto, writeWord_sparse_size]
  by_cases hz : len = 0
  · rw [hz, byteArray_write_zero_length, writeWord_sparse_size]; omega
  · rw [copyWindow_size _ _ _ _ _ hz hs (by rw [writeWord_sparse_size]; omega),
      writeWord_sparse_size]
    omega

theorem calldataBytesEncodedInto_preserves (cd mem : ByteArray) (src dst len : Nat)
    (hs : src + len ≤ cd.size) :
    MemoryPreserves mem (calldataBytesEncodedInto cd mem src dst len) 0 dst := by
  refine ⟨by rw [calldataBytesEncodedInto_size _ _ _ _ _ hs]; omega, ?_⟩
  intro off count _ hb hin
  have hh := writeWord_sparse_size mem dst (UInt256.ofNat len)
  have hc := byteArray_write_size_ge_base cd (writeWord mem dst (UInt256.ofNat len))
    src (dst + 32) len
  rw [calldataBytesEncodedInto, writeWordReadBelow _ _ _ _ _ (by omega) (by omega),
    copyWindowReadBelow _ _ _ _ _ _ _ hs (by omega) (by omega),
    writeWordReadBelow _ _ _ _ _ hin hb]

theorem calldataBytesEncodedInto_header (cd mem : ByteArray) (src dst len : Nat)
    (hs : src + len ≤ cd.size) :
    (calldataBytesEncodedInto cd mem src dst len).readWithPadding dst 32 =
      (UInt256.ofNat len).toByteArray := by
  have hh := writeWord_sparse_size mem dst (UInt256.ofNat len)
  have hc := byteArray_write_size_ge_base cd (writeWord mem dst (UInt256.ofNat len))
    src (dst + 32) len
  rw [calldataBytesEncodedInto, writeWordReadBelow _ _ _ _ _ (by omega) (by omega),
    copyWindowReadBelow _ _ _ _ _ _ _ hs (by omega) (by omega),
    writeWord_sparse_read_back]

theorem calldataBytesEncodedInto_payload (cd mem : ByteArray) (src dst len : Nat)
    (hs : src + len ≤ cd.size) :
    (calldataBytesEncodedInto cd mem src dst len).readWithPadding (dst + 32)
      (ABI.paddedSize len) =
      cd.extract src (src + len) ++ ByteArray.zeroes (ABI.paddedSize len - len) := by
  have hh : dst + 32 ≤ (writeWord mem dst (UInt256.ofNat len)).size := by
    rw [writeWord_sparse_size]; omega
  have hc : dst + 32 + len ≤
      (cd.write src (writeWord mem dst (UInt256.ofNat len)) (dst + 32) len).size := by
    by_cases hz : len = 0
    · rw [hz, byteArray_write_zero_length, writeWord_sparse_size]; omega
    · rw [copyWindow_size _ _ _ _ _ hz hs hh]; omega
  rw [calldataBytesEncodedInto, zeroTailRead _ _ _ _ hc
    (by unfold ABI.paddedSize; omega) (by unfold ABI.paddedSize; omega),
    copySlice_read _ _ _ _ _ hs hh]

theorem calldataBytesEncodedInto_read (cd mem : ByteArray) (src dst len : Nat)
    (hs : src + len ≤ cd.size) :
    (calldataBytesEncodedInto cd mem src dst len).readWithPadding dst
      (32 + ABI.paddedSize len) =
      (UInt256.ofNat len).toByteArray ++ cd.extract src (src + len) ++
        ByteArray.zeroes (ABI.paddedSize len - len) := by
  by_cases hz : len = 0
  · rw [hz]
    simp only [ABI.paddedSize, Nat.zero_add, Nat.reduceDiv, Nat.mul_zero, Nat.add_zero,
      Nat.sub_self, calldataBytesEncodedInto_header _ _ _ _ _ (by omega)]
    have he : cd.extract src src = ByteArray.empty := by apply ByteArray.ext; simp
    rw [he, zeroes_zero rfl, ByteArray.append_empty, ByteArray.append_empty]
    exact calldataBytesEncodedInto_header _ _ _ _ _ (by omega)
  · rw [byteArray_readWithPadding_split_unbounded _ _ _ _ (by decide)
      (by unfold ABI.paddedSize; omega)
      (by rw [calldataBytesEncodedInto_size _ _ _ _ _ hs]; unfold ABI.paddedSize; omega),
      calldataBytesEncodedInto_header _ _ _ _ _ hs,
      calldataBytesEncodedInto_payload _ _ _ _ _ hs, ByteArray.append_assoc]

end Benchmarks.Safe
