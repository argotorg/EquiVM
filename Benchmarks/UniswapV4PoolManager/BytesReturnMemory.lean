import Benchmarks.UniswapV4PoolManager.BytesObjectMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: the ABI tuple encoding of one memory bytes object.
def bytesReturnHeader (mem : ByteArray) (dest : UInt256) (data : ByteArray) : ByteArray :=
  writeWord (writeWord mem dest.toNat ⟨32⟩) (dest.toNat+32) (UInt256.ofNat data.size)

def bytesReturnMemory (mem : ByteArray) (ptr dest : UInt256) (data : ByteArray) : ByteArray :=
  copyZeroMemory (bytesReturnHeader mem dest data) (bytesReturnHeader mem dest data)
    (ptr.toNat+32) (dest.toNat+64) data.size

theorem bytesReturnHeader_view {mem data : ByteArray} {ptr dest : UInt256}
    (hv : BytesObjectView mem ptr data) (hbefore : ptr.toNat+32+data.size ≤ dest.toNat) :
    BytesObjectView (bytesReturnHeader mem dest data) ptr data := by
  exact (hv.writeWord_after dest.toNat ⟨32⟩ hbefore).writeWord_after
    (dest.toNat+32) (UInt256.ofNat data.size) (by omega)

theorem bytesReturnHeader_size (mem : ByteArray) (dest : UInt256) (data : ByteArray) :
    (bytesReturnHeader mem dest data).size = max mem.size (dest.toNat+64) := by
  rw [bytesReturnHeader, writeWord_sparse_size, writeWord_sparse_size]
  omega

theorem bytesReturnHeader_read (mem : ByteArray) (dest : UInt256) (data : ByteArray) :
    (bytesReturnHeader mem dest data).readWithPadding dest.toNat 64 =
      (⟨32⟩ : UInt256).toByteArray ++ (UInt256.ofNat data.size).toByteArray := by
  simpa only [wordSequenceMemory, wordBytes, bytesReturnHeader, List.length_cons,
    List.length_nil, ByteArray.append_empty] using
    wordSequenceMemory_read mem dest.toNat [⟨32⟩, UInt256.ofNat data.size]

theorem bytesReturnMemory_read {mem data : ByteArray} {ptr dest : UInt256}
    (hv : BytesObjectView mem ptr data) (hbefore : ptr.toNat+32+data.size ≤ dest.toNat) :
    (bytesReturnMemory mem ptr dest data).readWithPadding dest.toNat (64+paddedSize data.size) =
      bytesReturnEncoding data := by
  have hh := bytesReturnHeader_view hv hbefore
  rw [bytesReturnMemory, copyZeroMemory_read_prefix _ _ _ _ _ _ _ hh.inBounds
      (by rw [bytesReturnHeader_size]; omega) rfl,
    bytesReturnHeader_read, hh.payload, bytesReturnEncoding, bytesValueEncoding,
    ByteArray.append_assoc, ByteArray.append_assoc]

end Benchmarks.UniswapV4PoolManager
