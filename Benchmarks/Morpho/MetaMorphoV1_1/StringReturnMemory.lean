import Benchmarks.Morpho.MetaMorphoV1_1.StringEncoderMemory

/-! Dynamic string ABI encoding by two header stores, MCOPY, and a trailing zero store. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1

-- LIBRARY CANDIDATE: the byte-array form of the ABI encoding of a dynamic string.
def stringReturnBytes (bytes : ByteArray) : ByteArray :=
  (UInt256.ofNat 32).toByteArray ++ ((UInt256.ofNat bytes.size).toByteArray ++
    (bytes ++ ByteArray.zeroes (ABI.paddedSize bytes.size - bytes.size)))

theorem stringReturnEncoding (bytes : ByteArray) :
    encodeReturnValue? .string (.bytes bytes) = some (stringReturnBytes bytes) := by
  simp only [encodeReturnValue?, encodeReturnValues?, encodeABIValues?, encodeABIValuesFrom?,
    abiTupleHeadSize?, encodeABIValue?, isDynamicABIType, staticABIEncodedSize?,
    Option.bind, bind, if_true, List.nil_append, List.append_nil, Nat.add_zero, List.length_nil]
  rw [mk_toArray_eq, List.toByteArray_append, List.toByteArray_append, natBytes_toByteArray,
    natBytes_toByteArray, padRightToWord_toByteArray]
  rfl

-- LIBRARY CANDIDATE: a memory copy with an ABI offset/length header and zeroed final padding.
def stringReturnHeader (mem : ByteArray) (dest : Nat) (len : UInt256) : ByteArray :=
  writeWord (writeWord mem dest ⟨32⟩) (dest + 32) len

def stringReturnCopy (mem : ByteArray) (src dest : Nat) (len : UInt256) : ByteArray :=
  let header := stringReturnHeader mem dest len
  header.write src header (dest + 64) len.toNat

def stringReturnMemory (mem : ByteArray) (src dest : Nat) (len : UInt256) : ByteArray :=
  writeWord (stringReturnCopy mem src dest len) (dest + 64 + len.toNat) ⟨0⟩

theorem stringReturnHeader_size (mem : ByteArray) (dest : Nat) (len : UInt256) :
    (stringReturnHeader mem dest len).size = max mem.size (dest + 64) := by
  simp only [stringReturnHeader, writeWord_sparse_size]
  omega

theorem stringReturnHeader_read (mem : ByteArray) (src dest : Nat) (len : UInt256)
    (hin : src + len.toNat ≤ mem.size) (hbelow : src + len.toNat ≤ dest) :
    (stringReturnHeader mem dest len).readWithPadding src len.toNat =
      mem.readWithPadding src len.toNat := by
  rw [stringReturnHeader, writeWord_sparse_read_preserved_unbounded _ _ _ _ _
    (by rw [writeWord_sparse_size]; omega) (.inl (by omega)),
    writeWord_sparse_read_preserved_unbounded _ _ _ _ _ hin (.inl hbelow)]

theorem stringReturnCopy_size (mem : ByteArray) (src dest : Nat) (len : UInt256)
    (hin : src + len.toNat ≤ mem.size) :
    (stringReturnCopy mem src dest len).size = max mem.size (dest + 64 + len.toNat) := by
  change (stringPayloadCopy (writeWord mem dest ⟨32⟩) src (dest + 32) len).size = _
  rw [stringPayloadCopy_size _ _ _ _ (by rw [writeWord_sparse_size]; omega),
    writeWord_sparse_size]
  omega

theorem stringReturnCopy_read (mem : ByteArray) (src dest : Nat) (len : UInt256)
    (hin : src + len.toNat ≤ mem.size) (hbelow : src + len.toNat ≤ dest) :
    (stringReturnCopy mem src dest len).readWithPadding (dest + 64) len.toNat =
      mem.readWithPadding src len.toNat := by
  change (stringPayloadCopy (writeWord mem dest ⟨32⟩) src (dest + 32) len).readWithPadding
    (dest + 32 + 32) len.toNat = _
  rw [stringPayloadCopy_read _ _ _ _ (by rw [writeWord_sparse_size]; omega) (by omega),
    writeWord_sparse_read_preserved_unbounded _ _ _ _ _ hin (.inl hbelow)]

theorem stringReturnCopy_word (mem : ByteArray) (src dest read : Nat) (len : UInt256)
    (hin : src + len.toNat ≤ mem.size) (hread : read + 32 ≤ dest + 64) :
    (stringReturnCopy mem src dest len).readWithPadding read 32 =
      (stringReturnHeader mem dest len).readWithPadding read 32 := by
  exact stringPayloadCopy_word (writeWord mem dest ⟨32⟩) src (dest + 32) read len
    (by rw [writeWord_sparse_size]; omega) hread

theorem stringReturnMemory_read (mem bytes : ByteArray) (src dest : Nat) (len : UInt256)
    (hsize : bytes.size = len.toNat) (hin : src + len.toNat ≤ mem.size)
    (hbelow : src + len.toNat ≤ dest) (hread : mem.readWithPadding src len.toNat = bytes) :
    (stringReturnMemory mem src dest len).readWithPadding dest (64 + ABI.paddedSize len.toNat) =
      stringReturnBytes bytes := by
  have hpad : ABI.paddedSize len.toNat - len.toNat ≤ 31 := by
    unfold ABI.paddedSize
    omega
  have hlen : len.toNat ≤ ABI.paddedSize len.toNat := by
    unfold ABI.paddedSize
    omega
  have hmem : dest + 64 + len.toNat + 32 ≤ (stringReturnMemory mem src dest len).size := by
    rw [stringReturnMemory, writeWord_sparse_size]
    exact Nat.le_max_right _ _
  have hoffset : (stringReturnMemory mem src dest len).readWithPadding dest 32 =
      (UInt256.ofNat 32).toByteArray := by
    rw [stringReturnMemory, writeWord_sparse_read_preserved _ _ _ _
      (.inl ⟨by omega, by rw [stringReturnCopy_size _ _ _ _ hin]; omega⟩),
      stringReturnCopy_word _ _ _ _ _ hin (by omega), stringReturnHeader,
      writeWord_sparse_read_preserved _ _ _ _
        (.inl ⟨by omega, by rw [writeWord_sparse_size]; omega⟩), writeWord_sparse_read_back]
    rfl
  have htail : (stringReturnMemory mem src dest len).readWithPadding (dest + 32)
      (32 + paddedSize len.toNat) = stringPayloadBytes bytes := by
    exact stringPayloadMemory_read (writeWord mem dest ⟨32⟩) bytes src (dest + 32) len
      hsize (by rw [writeWord_sparse_size]; omega) (by omega) (by
        rw [writeWord_sparse_read_preserved_unbounded _ _ _ _ _ hin (.inl hbelow), hread])
  rw [show 64 + ABI.paddedSize len.toNat = 32 + (32 + ABI.paddedSize len.toNat) by omega,
    readWithPadding_split _ _ _ _ (by omega), hoffset, htail]
  rfl

end Benchmarks.Morpho.MetaMorphoV1_1
