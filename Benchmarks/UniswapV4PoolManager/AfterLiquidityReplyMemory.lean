import Benchmarks.UniswapV4PoolManager.AfterLiquidityActiveTrace
import Benchmarks.UniswapV4PoolManager.ReturnDataAllocation

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

def afterLiquidityReplyFree (free len : UInt256) (out : ByteArray) : UInt256 :=
  returnDataEnd (afterLiquidityFree free len) out

theorem MemorySlice.afterLiquidityReply {mem data : ByteArray} {base : Nat}
    (h : MemorySlice mem base data) (add : Bool) (src : ByteArray) (srcOff : Nat) (ptr len : UInt256)
    (sender : AccountAddress) (key : PoolKeyWords) (p : ModifyLiquidityWords) (delta fees : UInt256) (out : ByteArray)
    (hs : srcOff+len.toNat ≤ src.size) (hlo : 96 ≤ base) (hb : base+data.size ≤ ptr.toNat)
    (hf : ptr.toNat+len.toNat+576 < UInt256.size) :
    MemorySlice (afterLiquidityReplyMemory add src mem srcOff ptr len sender key p delta fees out) base data := by
  have he := afterLiquidityFree_toNat ptr len hf
  have hpad := paddedSize_le_add31 len.toNat
  exact (h.afterLiquidity add src srcOff ptr len sender key p delta fees hs hlo hb).returnData
    (afterLiquidityFree ptr len) out hlo (by rw [he]; omega) (by rw [he]; omega)

theorem afterLiquidityReplyMemory_free (add : Bool) (src mem : ByteArray) (srcOff : Nat)
    (ptr len : UInt256) (sender : AccountAddress) (key : PoolKeyWords) (p : ModifyLiquidityWords)
    (delta fees : UInt256) (out : ByteArray) (hlo : 96 ≤ ptr.toNat)
    (hf : ptr.toNat+len.toNat+576 < UInt256.size) :
    memLoad (UInt256.ofNat 64) (afterLiquidityReplyMemory add src mem srcOff ptr len sender key p delta fees out) =
      afterLiquidityReplyFree ptr len out := by
  have he := afterLiquidityFree_toNat ptr len hf
  have hpad := paddedSize_le_add31 len.toNat
  exact returnDataMemory_free _ _ _ (by rw [he]; omega) (by rw [he]; omega)

theorem afterLiquidityReplyFree_bounds (free len : UInt256) (out : ByteArray)
    (hf : free.toNat+len.toNat+out.size+768 < UInt256.size) :
    free.toNat ≤ (afterLiquidityReplyFree free len out).toNat ∧
      (afterLiquidityReplyFree free len out).toNat+64 < UInt256.size := by
  have he := afterLiquidityFree_toNat free len (by omega)
  have hpad := paddedSize_le_add31 len.toNat
  have hb := returnDataEnd_bounds (afterLiquidityFree free len) out (by rw [he]; omega)
  change free.toNat ≤ (returnDataEnd (afterLiquidityFree free len) out).toNat ∧
    (returnDataEnd (afterLiquidityFree free len) out).toNat+64 < UInt256.size
  omega

end Benchmarks.UniswapV4PoolManager
