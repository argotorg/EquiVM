import Benchmarks.UniswapV4PoolManager.WordBytesCallTailAllocation
import Benchmarks.UniswapV4PoolManager.AfterLiquiditySource
import Benchmarks.UniswapV4PoolManager.PoolKeyPreservation

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def afterLiquiditySelectorWord (add : Bool) : UInt256 :=
  if add then UInt256.ofNat 71928778709308087194252090466195475883861851167123116829321273769234209439744
  else UInt256.ofNat 48927076799537410738591317824729890221088287177367674182903010818651347484672

theorem afterLiquiditySelectorWord_bytes (add : Bool) :
    (afterLiquiditySelectorWord add).toByteArray.extract 0 4 = liquidityHookSelector true add := by
  cases add <;> decide +kernel

def afterLiquidityAllocationSize (len : UInt256) : UInt256 := UInt256.ofNat (484+paddedSize len.toNat)
def afterLiquidityFree (ptr len : UInt256) : UInt256 := allocationEnd ptr (afterLiquidityAllocationSize len)
def afterLiquidityMemory (add : Bool) (src mem : ByteArray) (srcOff : Nat) (ptr len : UInt256)
    (sender : AccountAddress) (key : PoolKeyWords) (p : ModifyLiquidityWords) (delta fees : UInt256) : ByteArray :=
  wordBytesCallAllocatedMemory src mem srcOff ptr (afterLiquiditySelectorWord add)
    (liquidityHookHeadWords true sender key p delta fees) len

theorem afterLiquidityFree_toNat (ptr len : UInt256)
    (hf : ptr.toNat+len.toNat+576 < UInt256.size) :
    (afterLiquidityFree ptr len).toNat = ptr.toNat+512+paddedSize len.toNat :=
  wordBytesCallAllocation_end_toNat ptr len (List.replicate 13 ⟨0⟩)
    (by simp only [List.length_replicate]; omega)

theorem afterLiquidityMemory_object (add : Bool) (src mem : ByteArray) (srcOff : Nat) (ptr len : UInt256)
    (sender : AccountAddress) (key : PoolKeyWords) (p : ModifyLiquidityWords) (delta fees : UInt256)
    (hs : srcOff+len.toNat ≤ src.size) (hptr : 96 ≤ ptr.toNat) :
    BytesObjectView (afterLiquidityMemory add src mem srcOff ptr len sender key p delta fees) ptr
      (afterLiquidityPayload add sender key p delta fees (src.extract srcOff (srcOff+len.toNat))) := by
  have hv := (wordBytesCallObjectMemory_view src mem srcOff ptr (afterLiquiditySelectorWord add)
    (liquidityHookHeadWords true sender key p delta fees) len hs).writeWord_before 64
      (afterLiquidityFree ptr len) hptr
  simpa only [afterLiquiditySelectorWord_bytes, afterLiquidityPayload, liquidityHookPayload] using hv

theorem afterLiquidityMemory_free (add : Bool) (src mem : ByteArray) (srcOff : Nat) (ptr len : UInt256)
    (sender : AccountAddress) (key : PoolKeyWords) (p : ModifyLiquidityWords) (delta fees : UInt256) :
    memLoad (UInt256.ofNat 64) (afterLiquidityMemory add src mem srcOff ptr len sender key p delta fees) =
      afterLiquidityFree ptr len := writeWord_sparse_load_back _ (UInt256.ofNat 64) _

theorem MemorySlice.afterLiquidity {mem data : ByteArray} {base : Nat}
    (h : MemorySlice mem base data) (add : Bool) (src : ByteArray) (srcOff : Nat) (ptr len : UInt256)
    (sender : AccountAddress) (key : PoolKeyWords) (p : ModifyLiquidityWords) (delta fees : UInt256)
    (hs : srcOff+len.toNat ≤ src.size) (hlo : 96 ≤ base) (hb : base+data.size ≤ ptr.toNat) :
    MemorySlice (afterLiquidityMemory add src mem srcOff ptr len sender key p delta fees) base data :=
  (h.wordBytesCallObject src srcOff ptr _ _ len hs hb).writeWord 64 _ (.inr hlo)

end Benchmarks.UniswapV4PoolManager
