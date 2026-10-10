import Benchmarks.UniswapV4PoolManager.BytesMemory
import Benchmarks.UniswapV4PoolManager.TwoWordCallMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: an ABI call carrying a bytes slice copied from calldata.
def bytesCallMemory (src base : ByteArray) (off srcAddr : Nat) (selector len : UInt256) : ByteArray :=
  copyPadMemory src (twoWordCallMemory base off selector ⟨32⟩ len) srcAddr len.toNat

theorem bytesCallMemory_size (src base : ByteArray) (off srcAddr : Nat) (selector len : UInt256)
    (hb : base.size ≤ off+68) (hgap : off-base.size < USize.size)
    (hs : srcAddr+len.toNat ≤ src.size) :
    (bytesCallMemory src base off srcAddr selector len).size = off+100+len.toNat := by
  rw [bytesCallMemory, copyPadMemory_size _ _ _ _ hs, twoWordCallMemory_size _ _ _ _ _ hgap,
    Nat.max_eq_right hb]
  omega

theorem bytesCallMemory_read (src base : ByteArray) (off srcAddr : Nat) (selector len : UInt256)
    (hb : base.size ≤ off+68) (hgap : off-base.size < USize.size)
    (hs : srcAddr+len.toNat ≤ src.size) :
    (bytesCallMemory src base off srcAddr selector len).readWithPadding off (68+paddedSize len.toNat) =
      selector.toByteArray.extract 0 4 ++ bytesReturnEncoding (src.extract srcAddr (srcAddr+len.toNat)) := by
  have hlen : (src.extract srcAddr (srcAddr+len.toNat)).size = len.toNat := by
    rw [ByteArray.size_extract]; omega
  rw [bytesCallMemory, copyPadMemory_read _ _ _ _ _ _
      (by rw [twoWordCallMemory_size _ _ _ _ _ hgap, Nat.max_eq_right hb]) hs,
    twoWordCallMemory_read _ _ _ _ _ hgap,
    bytesReturnEncoding, bytesValueEncoding, hlen, u256_ofNat_toNat]
  simp only [ByteArray.append_assoc]

theorem bytesCallMemory_load_below (src base : ByteArray) (off srcAddr : Nat)
    (selector len read : UInt256) (hread : read.toNat+32 ≤ base.size)
    (hbefore : read.toNat+32 ≤ off) (hgap : off-base.size < USize.size)
    (hs : srcAddr+len.toNat ≤ src.size) :
    memLoad read (bytesCallMemory src base off srcAddr selector len) = memLoad read base := by
  rw [bytesCallMemory, copyPadMemory_load_below _ _ _ _ _ hs
      (by rw [twoWordCallMemory_size _ _ _ _ _ hgap]; omega),
    twoWordCallMemory_load_below _ _ _ _ _ _ hread hbefore hgap]

end Benchmarks.UniswapV4PoolManager
