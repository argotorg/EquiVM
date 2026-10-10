import Benchmarks.UniswapV4PoolManager.WordBytesCallAllocation
import Benchmarks.UniswapV4PoolManager.DonateHookSource
import Benchmarks.UniswapV4PoolManager.PoolKeyPreservation

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def donateHookSelectorWord (after : Bool) : UInt256 :=
  if after then UInt256.ofNat 102089634039300134962802909115238314461027419237443557584673670268305811701760
  else UInt256.ofNat 82618990196380953178201528318524402311480446822369150104943134852608851705856

theorem donateHookSelectorWord_bytes (after : Bool) :
    (donateHookSelectorWord after).toByteArray.extract 0 4 = donateHookSelector after := by
  cases after <;> decide +kernel

def donateHookAllocationSize (len : UInt256) : UInt256 := UInt256.ofNat (356+paddedSize len.toNat)
def donateHookFree (ptr len : UInt256) : UInt256 := allocationEnd ptr (donateHookAllocationSize len)
def donateHookMemory (after : Bool) (src mem : ByteArray) (srcOff : Nat) (ptr len : UInt256)
    (sender : AccountAddress) (key : PoolKeyWords) (amount0 amount1 : UInt256) : ByteArray :=
  wordBytesCallAllocatedMemory src mem srcOff ptr (donateHookSelectorWord after)
    (donateHookHeadWords sender key amount0 amount1) len

theorem donateHookFree_toNat (ptr len : UInt256)
    (hf : ptr.toNat+len.toNat+448 < UInt256.size) :
    (donateHookFree ptr len).toNat = ptr.toNat+384+paddedSize len.toNat := by
  exact wordBytesCallAllocation_end_toNat ptr len (List.replicate 9 ⟨0⟩)
    (by simp only [List.length_replicate]; omega)

theorem donateHookMemory_object (after : Bool) (src mem : ByteArray) (srcOff : Nat) (ptr len : UInt256)
    (sender : AccountAddress) (key : PoolKeyWords) (amount0 amount1 : UInt256)
    (hs : srcOff+len.toNat ≤ src.size) (hptr : 96 ≤ ptr.toNat) :
    BytesObjectView (donateHookMemory after src mem srcOff ptr len sender key amount0 amount1) ptr
      (donateHookPayload after sender key amount0 amount1 (src.extract srcOff (srcOff+len.toNat))) := by
  have hv := (wordBytesCallObjectMemory_view src mem srcOff ptr (donateHookSelectorWord after)
    (donateHookHeadWords sender key amount0 amount1) len hs).writeWord_before 64
      (donateHookFree ptr len) hptr
  simpa only [donateHookSelectorWord_bytes, donateHookPayload] using hv

theorem donateHookMemory_free (after : Bool) (src mem : ByteArray) (srcOff : Nat) (ptr len : UInt256)
    (sender : AccountAddress) (key : PoolKeyWords) (amount0 amount1 : UInt256) :
    memLoad (UInt256.ofNat 64) (donateHookMemory after src mem srcOff ptr len sender key amount0 amount1) =
      donateHookFree ptr len := writeWord_sparse_load_back _ (UInt256.ofNat 64) _

theorem MemorySlice.donateHook {mem data : ByteArray} {base : Nat}
    (h : MemorySlice mem base data) (after : Bool) (src : ByteArray) (srcOff : Nat) (ptr len : UInt256)
    (sender : AccountAddress) (key : PoolKeyWords) (amount0 amount1 : UInt256)
    (hs : srcOff+len.toNat ≤ src.size) (hlo : 96 ≤ base) (hb : base+data.size ≤ ptr.toNat) :
    MemorySlice (donateHookMemory after src mem srcOff ptr len sender key amount0 amount1) base data :=
  (h.wordBytesCallObject src srcOff ptr _ _ len hs hb).writeWord 64 _ (.inr hlo)

end Benchmarks.UniswapV4PoolManager
