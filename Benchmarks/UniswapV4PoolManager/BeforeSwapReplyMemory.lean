import Benchmarks.UniswapV4PoolManager.BeforeSwapMemory
import Benchmarks.UniswapV4PoolManager.ReturnDataAllocation

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

def beforeSwapReplyMemory (src mem : ByteArray) (srcOff : Nat) (ptr len : UInt256)
    (sender : AccountAddress) (key : PoolKeyWords) (p : SwapParamsWords) (out : ByteArray) : ByteArray :=
  solcReturnDataMem (beforeSwapMemory src mem srcOff ptr len sender key p) (beforeSwapFree ptr len) out

def beforeSwapReplyFree (free len : UInt256) (out : ByteArray) : UInt256 :=
  returnDataEnd (beforeSwapFree free len) out

theorem MemorySlice.beforeSwapReply {mem data : ByteArray} {base : Nat}
    (h : MemorySlice mem base data) (src : ByteArray) (srcOff : Nat) (ptr len : UInt256)
    (sender : AccountAddress) (key : PoolKeyWords) (p : SwapParamsWords) (out : ByteArray)
    (hs : srcOff+len.toNat ≤ src.size) (hlo : 96 ≤ base) (hb : base+data.size ≤ ptr.toNat)
    (hf : ptr.toNat+len.toNat+480 < UInt256.size) :
    MemorySlice (beforeSwapReplyMemory src mem srcOff ptr len sender key p out) base data := by
  have he := beforeSwapFree_toNat ptr len hf
  have hpad := paddedSize_le_add31 len.toNat
  exact (h.beforeSwap src srcOff ptr len sender key p hs hlo hb).returnData
    (beforeSwapFree ptr len) out hlo (by rw [he]; omega) (by rw [he]; omega)

theorem beforeSwapReplyMemory_free (src mem : ByteArray) (srcOff : Nat)
    (ptr len : UInt256) (sender : AccountAddress) (key : PoolKeyWords) (p : SwapParamsWords)
    (out : ByteArray) (hlo : 96 ≤ ptr.toNat) (hf : ptr.toNat+len.toNat+480 < UInt256.size) :
    memLoad (UInt256.ofNat 64) (beforeSwapReplyMemory src mem srcOff ptr len sender key p out) =
      beforeSwapReplyFree ptr len out := by
  have he := beforeSwapFree_toNat ptr len hf
  have hpad := paddedSize_le_add31 len.toNat
  exact returnDataMemory_free _ _ _ (by rw [he]; omega) (by rw [he]; omega)

theorem beforeSwapReplyFree_bounds (free len : UInt256) (out : ByteArray)
    (hf : free.toNat+len.toNat+480 < UInt256.size)
    (ho : (beforeSwapFree free len).toNat+out.size+4096 ≤ solcMaxU64) :
    free.toNat ≤ (beforeSwapReplyFree free len out).toNat ∧
      (beforeSwapReplyFree free len out).toNat+4000 ≤ solcMaxU64 := by
  have he := beforeSwapFree_toNat free len hf
  have hb := returnDataEnd_bounds (beforeSwapFree free len) out
    (by change _ ≤ 2^64-1 at ho; change _ < 2^256; omega)
  change free.toNat ≤ (returnDataEnd (beforeSwapFree free len) out).toNat ∧
    (returnDataEnd (beforeSwapFree free len) out).toNat+4000 ≤ solcMaxU64
  omega

end Benchmarks.UniswapV4PoolManager
