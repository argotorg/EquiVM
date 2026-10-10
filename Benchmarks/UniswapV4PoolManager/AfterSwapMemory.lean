import Benchmarks.UniswapV4PoolManager.WordBytesCallAllocation
import Benchmarks.UniswapV4PoolManager.AfterSwapBranchSource
import Benchmarks.UniswapV4PoolManager.PoolKeyPreservation

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def afterSwapSelectorWord : UInt256 :=
  UInt256.ofNat 81633964087944550421898347516412261609448132923240477519941993112300444188672
theorem afterSwapSelectorWord_bytes :
    afterSwapSelectorWord.toByteArray.extract 0 4 = swapHookSelector true := by decide +kernel
def afterSwapAllocationSize (len : UInt256) : UInt256 := UInt256.ofNat (420+paddedSize len.toNat)
def afterSwapFree (ptr len : UInt256) : UInt256 := allocationEnd ptr (afterSwapAllocationSize len)
def afterSwapMemory (src mem : ByteArray) (srcOff : Nat) (ptr len : UInt256)
    (sender : AccountAddress) (key : PoolKeyWords) (p : SwapParamsWords) (delta : UInt256) : ByteArray :=
  wordBytesCallAllocatedMemory src mem srcOff ptr afterSwapSelectorWord
    (swapHookHeadWords true sender key p delta) len

theorem afterSwapFree_toNat (ptr len : UInt256)
    (hf : ptr.toNat+len.toNat+512 < UInt256.size) :
    (afterSwapFree ptr len).toNat = ptr.toNat+448+paddedSize len.toNat := by
  exact wordBytesCallAllocation_end_toNat ptr len (List.replicate 11 ⟨0⟩)
    (by simp only [List.length_replicate]; omega)

theorem afterSwapMemory_object (src mem : ByteArray) (srcOff : Nat) (ptr len : UInt256)
    (sender : AccountAddress) (key : PoolKeyWords) (p : SwapParamsWords) (delta : UInt256)
    (hs : srcOff+len.toNat ≤ src.size) (hptr : 96 ≤ ptr.toNat) :
    BytesObjectView (afterSwapMemory src mem srcOff ptr len sender key p delta) ptr
      (afterSwapPayload sender key p delta (src.extract srcOff (srcOff+len.toNat))) := by
  have hv := (wordBytesCallObjectMemory_view src mem srcOff ptr afterSwapSelectorWord
    (swapHookHeadWords true sender key p delta) len hs).writeWord_before 64 (afterSwapFree ptr len) hptr
  simpa only [afterSwapSelectorWord_bytes, afterSwapPayload, swapHookPayload] using hv

theorem afterSwapMemory_free (src mem : ByteArray) (srcOff : Nat) (ptr len : UInt256)
    (sender : AccountAddress) (key : PoolKeyWords) (p : SwapParamsWords) (delta : UInt256) :
    memLoad (UInt256.ofNat 64) (afterSwapMemory src mem srcOff ptr len sender key p delta) =
      afterSwapFree ptr len := writeWord_sparse_load_back _ (UInt256.ofNat 64) _

theorem MemorySlice.afterSwap {mem data : ByteArray} {base : Nat}
    (h : MemorySlice mem base data) (src : ByteArray) (srcOff : Nat) (ptr len : UInt256)
    (sender : AccountAddress) (key : PoolKeyWords) (p : SwapParamsWords) (delta : UInt256)
    (hs : srcOff+len.toNat ≤ src.size) (hlo : 96 ≤ base) (hb : base+data.size ≤ ptr.toNat) :
    MemorySlice (afterSwapMemory src mem srcOff ptr len sender key p delta) base data :=
  (h.wordBytesCallObject src srcOff ptr _ _ len hs hb).writeWord 64 _ (.inr hlo)

end Benchmarks.UniswapV4PoolManager
