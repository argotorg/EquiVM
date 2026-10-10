import Benchmarks.UniswapV4PoolManager.WordBytesCallAllocation
import Benchmarks.UniswapV4PoolManager.BeforeLiquiditySource
import Benchmarks.UniswapV4PoolManager.PoolKeyPreservation

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def beforeLiquiditySelectorWord (add : Bool) : UInt256 :=
  if add then UInt256.ofNat 17006806399344818723028117941659141655643775414500287383963728988317306322944
  else UInt256.ofNat 15295473827866257631926089641031614351259019422650909578044869842758528925696

theorem beforeLiquiditySelectorWord_bytes (add : Bool) :
    (beforeLiquiditySelectorWord add).toByteArray.extract 0 4 = liquidityHookSelector false add := by
  cases add <;> decide +kernel

def beforeLiquidityAllocationSize (len : UInt256) : UInt256 := UInt256.ofNat (420+paddedSize len.toNat)
def beforeLiquidityFree (ptr len : UInt256) : UInt256 := allocationEnd ptr (beforeLiquidityAllocationSize len)
def beforeLiquidityMemory (add : Bool) (src mem : ByteArray) (srcOff : Nat) (ptr len : UInt256)
    (sender : AccountAddress) (key : PoolKeyWords) (p : ModifyLiquidityWords) : ByteArray :=
  wordBytesCallAllocatedMemory src mem srcOff ptr (beforeLiquiditySelectorWord add)
    (liquidityHookHeadWords false sender key p ⟨0⟩ ⟨0⟩) len

theorem beforeLiquidityFree_toNat (ptr len : UInt256)
    (hf : ptr.toNat+len.toNat+512 < UInt256.size) :
    (beforeLiquidityFree ptr len).toNat = ptr.toNat+448+paddedSize len.toNat := by
  exact wordBytesCallAllocation_end_toNat ptr len (List.replicate 11 ⟨0⟩)
    (by simp only [List.length_replicate]; omega)

theorem beforeLiquidityMemory_object (add : Bool) (src mem : ByteArray) (srcOff : Nat) (ptr len : UInt256)
    (sender : AccountAddress) (key : PoolKeyWords) (p : ModifyLiquidityWords)
    (hs : srcOff+len.toNat ≤ src.size) (hptr : 96 ≤ ptr.toNat) :
    BytesObjectView (beforeLiquidityMemory add src mem srcOff ptr len sender key p) ptr
      (beforeLiquidityPayload add sender key p (src.extract srcOff (srcOff+len.toNat))) := by
  have hv := (wordBytesCallObjectMemory_view src mem srcOff ptr (beforeLiquiditySelectorWord add)
    (liquidityHookHeadWords false sender key p ⟨0⟩ ⟨0⟩) len hs).writeWord_before 64
      (beforeLiquidityFree ptr len) hptr
  simpa only [beforeLiquiditySelectorWord_bytes, beforeLiquidityPayload, liquidityHookPayload] using hv

theorem beforeLiquidityMemory_free (add : Bool) (src mem : ByteArray) (srcOff : Nat) (ptr len : UInt256)
    (sender : AccountAddress) (key : PoolKeyWords) (p : ModifyLiquidityWords) :
    memLoad (UInt256.ofNat 64) (beforeLiquidityMemory add src mem srcOff ptr len sender key p) =
      beforeLiquidityFree ptr len := writeWord_sparse_load_back _ (UInt256.ofNat 64) _

theorem MemorySlice.beforeLiquidity {mem data : ByteArray} {base : Nat}
    (h : MemorySlice mem base data) (add : Bool) (src : ByteArray) (srcOff : Nat) (ptr len : UInt256)
    (sender : AccountAddress) (key : PoolKeyWords) (p : ModifyLiquidityWords)
    (hs : srcOff+len.toNat ≤ src.size) (hlo : 96 ≤ base) (hb : base+data.size ≤ ptr.toNat) :
    MemorySlice (beforeLiquidityMemory add src mem srcOff ptr len sender key p) base data :=
  (h.wordBytesCallObject src srcOff ptr _ _ len hs hb).writeWord 64 _ (.inr hlo)

end Benchmarks.UniswapV4PoolManager
