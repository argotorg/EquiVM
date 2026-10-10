import Benchmarks.UniswapV4PoolManager.WordBytesCallAllocation
import Benchmarks.UniswapV4PoolManager.BeforeSwapBranchSource
import Benchmarks.UniswapV4PoolManager.PoolKeyPreservation

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def beforeSwapSelectorWord : UInt256 :=
  UInt256.ofNat 39517554766492228462871542592889873161447314332129087808566876747632635543552

theorem beforeSwapSelectorWord_bytes :
    beforeSwapSelectorWord.toByteArray.extract 0 4 = swapHookSelector false := by
  decide +kernel

def beforeSwapAllocationSize (len : UInt256) : UInt256 := UInt256.ofNat (388+paddedSize len.toNat)
def beforeSwapFree (ptr len : UInt256) : UInt256 := allocationEnd ptr (beforeSwapAllocationSize len)
def beforeSwapMemory (src mem : ByteArray) (srcOff : Nat) (ptr len : UInt256)
    (sender : AccountAddress) (key : PoolKeyWords) (p : SwapParamsWords) : ByteArray :=
  wordBytesCallAllocatedMemory src mem srcOff ptr beforeSwapSelectorWord
    (swapHookHeadWords false sender key p ⟨0⟩) len

theorem beforeSwapFree_toNat (ptr len : UInt256)
    (hf : ptr.toNat+len.toNat+480 < UInt256.size) :
    (beforeSwapFree ptr len).toNat = ptr.toNat+416+paddedSize len.toNat := by
  exact wordBytesCallAllocation_end_toNat ptr len (List.replicate 10 ⟨0⟩)
    (by simp only [List.length_replicate]; omega)

theorem beforeSwapMemory_object (src mem : ByteArray) (srcOff : Nat) (ptr len : UInt256)
    (sender : AccountAddress) (key : PoolKeyWords) (p : SwapParamsWords)
    (hs : srcOff+len.toNat ≤ src.size) (hptr : 96 ≤ ptr.toNat) :
    BytesObjectView (beforeSwapMemory src mem srcOff ptr len sender key p) ptr
      (beforeSwapPayload sender key p (src.extract srcOff (srcOff+len.toNat))) := by
  have hv := (wordBytesCallObjectMemory_view src mem srcOff ptr beforeSwapSelectorWord
    (swapHookHeadWords false sender key p ⟨0⟩) len hs).writeWord_before 64
      (beforeSwapFree ptr len) hptr
  simpa only [beforeSwapSelectorWord_bytes, beforeSwapPayload, swapHookPayload] using hv

theorem beforeSwapMemory_free (src mem : ByteArray) (srcOff : Nat) (ptr len : UInt256)
    (sender : AccountAddress) (key : PoolKeyWords) (p : SwapParamsWords) :
    memLoad (UInt256.ofNat 64) (beforeSwapMemory src mem srcOff ptr len sender key p) =
      beforeSwapFree ptr len := writeWord_sparse_load_back _ (UInt256.ofNat 64) _

theorem MemorySlice.beforeSwap {mem data : ByteArray} {base : Nat}
    (h : MemorySlice mem base data) (src : ByteArray) (srcOff : Nat) (ptr len : UInt256)
    (sender : AccountAddress) (key : PoolKeyWords) (p : SwapParamsWords)
    (hs : srcOff+len.toNat ≤ src.size) (hlo : 96 ≤ base) (hb : base+data.size ≤ ptr.toNat) :
    MemorySlice (beforeSwapMemory src mem srcOff ptr len sender key p) base data :=
  (h.wordBytesCallObject src srcOff ptr _ _ len hs hb).writeWord 64 _ (.inr hlo)

end Benchmarks.UniswapV4PoolManager
