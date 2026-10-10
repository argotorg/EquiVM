import Benchmarks.UniswapV4PoolManager.AfterSwapMemory
import Benchmarks.UniswapV4PoolManager.ReturnDataAllocation

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

def afterSwapReplyMemory (src mem : ByteArray) (srcOff : Nat) (ptr len : UInt256)
    (sender : AccountAddress) (key : PoolKeyWords) (p : SwapParamsWords) (delta : UInt256)
    (out : ByteArray) : ByteArray :=
  solcReturnDataMem (afterSwapMemory src mem srcOff ptr len sender key p delta) (afterSwapFree ptr len) out

def afterSwapReplyFree (free len : UInt256) (out : ByteArray) : UInt256 :=
  returnDataEnd (afterSwapFree free len) out

theorem MemorySlice.afterSwapReply {mem data : ByteArray} {base : Nat}
    (h : MemorySlice mem base data) (src : ByteArray) (srcOff : Nat) (ptr len : UInt256)
    (sender : AccountAddress) (key : PoolKeyWords) (p : SwapParamsWords) (delta : UInt256) (out : ByteArray)
    (hs : srcOff+len.toNat ≤ src.size) (hlo : 96 ≤ base) (hb : base+data.size ≤ ptr.toNat)
    (hf : ptr.toNat+len.toNat+512 < UInt256.size) :
    MemorySlice (afterSwapReplyMemory src mem srcOff ptr len sender key p delta out) base data := by
  have he := afterSwapFree_toNat ptr len hf
  have hpad := paddedSize_le_add31 len.toNat
  exact (h.afterSwap src srcOff ptr len sender key p delta hs hlo hb).returnData
    (afterSwapFree ptr len) out hlo (by rw [he]; omega) (by rw [he]; omega)

theorem afterSwapReplyMemory_free (src mem : ByteArray) (srcOff : Nat)
    (ptr len : UInt256) (sender : AccountAddress) (key : PoolKeyWords) (p : SwapParamsWords)
    (delta : UInt256) (out : ByteArray) (hlo : 96 ≤ ptr.toNat)
    (hf : ptr.toNat+len.toNat+512 < UInt256.size) :
    memLoad (UInt256.ofNat 64) (afterSwapReplyMemory src mem srcOff ptr len sender key p delta out) =
      afterSwapReplyFree ptr len out := by
  have he := afterSwapFree_toNat ptr len hf
  have hpad := paddedSize_le_add31 len.toNat
  exact returnDataMemory_free _ _ _ (by rw [he]; omega) (by rw [he]; omega)

theorem afterSwapReplyFree_bounds (free len : UInt256) (out : ByteArray)
    (hf : free.toNat+len.toNat+512 < UInt256.size)
    (ho : (afterSwapFree free len).toNat+out.size+4096 ≤ solcMaxU64) :
    free.toNat ≤ (afterSwapReplyFree free len out).toNat ∧
      (afterSwapReplyFree free len out).toNat+4000 ≤ solcMaxU64 := by
  have he := afterSwapFree_toNat free len hf
  have hb := returnDataEnd_bounds (afterSwapFree free len) out
    (by change _ ≤ 2^64-1 at ho; change _ < 2^256; omega)
  change free.toNat ≤ (returnDataEnd (afterSwapFree free len) out).toNat ∧
    (returnDataEnd (afterSwapFree free len) out).toNat+4000 ≤ solcMaxU64
  omega

end Benchmarks.UniswapV4PoolManager
