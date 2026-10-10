import Benchmarks.UniswapV4PoolManager.BeforeLiquidityMemory
import Benchmarks.UniswapV4PoolManager.ReturnDataAllocation

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

def beforeLiquidityReplyMemory (add : Bool) (src mem : ByteArray) (srcOff : Nat) (ptr len : UInt256)
    (sender : AccountAddress) (key : PoolKeyWords) (p : ModifyLiquidityWords) (out : ByteArray) : ByteArray :=
  solcReturnDataMem (beforeLiquidityMemory add src mem srcOff ptr len sender key p) (beforeLiquidityFree ptr len) out

def beforeLiquidityReplyFree (free len : UInt256) (out : ByteArray) : UInt256 :=
  returnDataEnd (beforeLiquidityFree free len) out

theorem MemorySlice.beforeLiquidityReply {mem data : ByteArray} {base : Nat}
    (h : MemorySlice mem base data) (add : Bool) (src : ByteArray) (srcOff : Nat) (ptr len : UInt256)
    (sender : AccountAddress) (key : PoolKeyWords) (p : ModifyLiquidityWords) (out : ByteArray)
    (hs : srcOff+len.toNat ≤ src.size) (hlo : 96 ≤ base) (hb : base+data.size ≤ ptr.toNat)
    (hf : ptr.toNat+len.toNat+512 < UInt256.size) :
    MemorySlice (beforeLiquidityReplyMemory add src mem srcOff ptr len sender key p out) base data := by
  have he := beforeLiquidityFree_toNat ptr len hf
  have hpad := paddedSize_le_add31 len.toNat
  exact (h.beforeLiquidity add src srcOff ptr len sender key p hs hlo hb).returnData
    (beforeLiquidityFree ptr len) out hlo (by rw [he]; omega) (by rw [he]; omega)

theorem beforeLiquidityReplyMemory_free (add : Bool) (src mem : ByteArray) (srcOff : Nat)
    (ptr len : UInt256) (sender : AccountAddress) (key : PoolKeyWords) (p : ModifyLiquidityWords)
    (out : ByteArray) (hlo : 96 ≤ ptr.toNat) (hf : ptr.toNat+len.toNat+512 < UInt256.size) :
    memLoad (UInt256.ofNat 64) (beforeLiquidityReplyMemory add src mem srcOff ptr len sender key p out) =
      beforeLiquidityReplyFree ptr len out := by
  have he := beforeLiquidityFree_toNat ptr len hf
  have hpad := paddedSize_le_add31 len.toNat
  exact returnDataMemory_free _ _ _ (by rw [he]; omega) (by rw [he]; omega)

theorem beforeLiquidityReplyFree_bounds (free len : UInt256) (out : ByteArray)
    (hf : free.toNat+len.toNat+512 < UInt256.size)
    (ho : (beforeLiquidityFree free len).toNat+out.size+4096 ≤ solcMaxU64) :
    free.toNat ≤ (beforeLiquidityReplyFree free len out).toNat ∧
      (beforeLiquidityReplyFree free len out).toNat+4000 ≤ solcMaxU64 := by
  have he := beforeLiquidityFree_toNat free len hf
  have hb := returnDataEnd_bounds (beforeLiquidityFree free len) out
    (by change _ ≤ 2^64-1 at ho; change _ < 2^256; omega)
  change free.toNat ≤ (returnDataEnd (beforeLiquidityFree free len) out).toNat ∧
    (returnDataEnd (beforeLiquidityFree free len) out).toNat+4000 ≤ solcMaxU64
  omega

end Benchmarks.UniswapV4PoolManager
