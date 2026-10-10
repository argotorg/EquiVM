import Benchmarks.UniswapV4PoolManager.DonateHookMemory
import Benchmarks.UniswapV4PoolManager.ReturnDataAllocation

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

def donateHookReplyMemory (after : Bool) (src mem : ByteArray) (srcOff : Nat) (ptr len : UInt256)
    (sender : AccountAddress) (key : PoolKeyWords) (amount0 amount1 : UInt256) (out : ByteArray) : ByteArray :=
  solcReturnDataMem (donateHookMemory after src mem srcOff ptr len sender key amount0 amount1) (donateHookFree ptr len) out

def donateHookReplyFree (free len : UInt256) (out : ByteArray) : UInt256 :=
  returnDataEnd (donateHookFree free len) out

theorem MemorySlice.donateHookReply {mem data : ByteArray} {base : Nat}
    (h : MemorySlice mem base data) (after : Bool) (src : ByteArray) (srcOff : Nat) (ptr len : UInt256)
    (sender : AccountAddress) (key : PoolKeyWords) (amount0 amount1 : UInt256) (out : ByteArray)
    (hs : srcOff+len.toNat ≤ src.size) (hlo : 96 ≤ base) (hb : base+data.size ≤ ptr.toNat)
    (hf : ptr.toNat+len.toNat+448 < UInt256.size) :
    MemorySlice (donateHookReplyMemory after src mem srcOff ptr len sender key amount0 amount1 out) base data := by
  have he := donateHookFree_toNat ptr len hf
  have hpad := paddedSize_le_add31 len.toNat
  exact (h.donateHook after src srcOff ptr len sender key amount0 amount1 hs hlo hb).returnData
    (donateHookFree ptr len) out hlo (by rw [he]; omega) (by rw [he]; omega)

theorem donateHookReplyMemory_free (after : Bool) (src mem : ByteArray) (srcOff : Nat)
    (ptr len : UInt256) (sender : AccountAddress) (key : PoolKeyWords) (amount0 amount1 : UInt256)
    (out : ByteArray) (hlo : 96 ≤ ptr.toNat) (hf : ptr.toNat+len.toNat+448 < UInt256.size) :
    memLoad (UInt256.ofNat 64) (donateHookReplyMemory after src mem srcOff ptr len sender key amount0 amount1 out) =
      donateHookReplyFree ptr len out := by
  have he := donateHookFree_toNat ptr len hf
  have hpad := paddedSize_le_add31 len.toNat
  exact returnDataMemory_free _ _ _ (by rw [he]; omega) (by rw [he]; omega)

theorem donateHookReplyFree_bounds (free len : UInt256) (out : ByteArray)
    (hf : free.toNat+len.toNat+448 < UInt256.size)
    (ho : (donateHookFree free len).toNat+out.size+4096 ≤ solcMaxU64) :
    free.toNat ≤ (donateHookReplyFree free len out).toNat ∧
      (donateHookReplyFree free len out).toNat+4000 ≤ solcMaxU64 := by
  have he := donateHookFree_toNat free len hf
  have hb := returnDataEnd_bounds (donateHookFree free len) out
    (by change _ ≤ 2^64-1 at ho; change _ < 2^256; omega)
  change free.toNat ≤ (returnDataEnd (donateHookFree free len) out).toNat ∧
    (returnDataEnd (donateHookFree free len) out).toNat+4000 ≤ solcMaxU64
  omega

end Benchmarks.UniswapV4PoolManager
