import Benchmarks.UniswapV4PoolManager.Bytes4
import Benchmarks.UniswapV4PoolManager.BytesObjectMemory
import Benchmarks.UniswapV4PoolManager.MemorySlice

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: a subwindow of a bytes-object payload.
theorem BytesObjectView.read {mem data : ByteArray} {ptr : UInt256}
    (h : BytesObjectView mem ptr data) (off count : Nat) (hw : off+count ≤ data.size) :
    mem.readWithPadding (ptr.toNat+32+off) count = data.extract off (off+count) :=
  (MemorySlice.mk h.payload h.inBounds).read_window off count hw

-- LIBRARY CANDIDATE: a high-four-byte mask compares precisely the byte prefixes.
theorem bytes4Mask_eq_iff (a b : UInt256) :
    UInt256.land bytes4Mask a = UInt256.land bytes4Mask b ↔
      a.toByteArray.extract 0 4 = b.toByteArray.extract 0 4 := by
  have ha := bytesBE_extract_high a 4 (by decide)
  have hb := bytesBE_extract_high b 4 (by decide)
  change fromBytesBigEndian (a.toByteArray.extract 0 4).toList = a.toNat/2^224 at ha
  change fromBytesBigEndian (b.toByteArray.extract 0 4).toList = b.toNat/2^224 at hb
  simp only [byteArray_toList_eq] at ha hb
  constructor
  · intro he
    have hn := congrArg UInt256.toNat he
    simp only [u256_land_comm bytes4Mask, bytes4Mask_toNat] at hn
    apply ByteArray.ext
    apply Array.toList_inj.mp
    apply fromBytesBigEndian_inj4
    · rw [Array.length_toList]
      change (a.toByteArray.extract 0 4).size = 4
      rw [ByteArray.size_extract, toByteArray_size]; rfl
    · rw [Array.length_toList]
      change (b.toByteArray.extract 0 4).size = 4
      rw [ByteArray.size_extract, toByteArray_size]; rfl
    · rw [ha, hb]; omega
  · intro he
    have hn := congrArg (fun x : ByteArray => fromBytesBigEndian x.toList) he
    simp only [byteArray_toList_eq, ha, hb] at hn
    apply u256_inj
    simp only [u256_land_comm bytes4Mask, bytes4Mask_toNat, hn]

-- LIBRARY CANDIDATE: a word load exposes the corresponding selector bytes.
theorem memLoad_prefix4 (mem : ByteArray) (ptr : UInt256)
    (hin : ptr.toNat+32 ≤ mem.size) :
    (memLoad ptr mem).toByteArray.extract 0 4 = mem.readWithPadding ptr.toNat 4 := by
  rw [memLoad, if_neg (by omega)]
  simpa only [Nat.add_zero, Nat.zero_add] using
    toByteArray_readWord_extract mem ptr.toNat 0 4 hin (by decide) (by decide)

end Benchmarks.UniswapV4PoolManager
