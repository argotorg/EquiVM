import Benchmarks.UniswapV4PoolManager.InitializeHookMemory
import Benchmarks.UniswapV4PoolManager.PoolKeyPreservation
import Benchmarks.UniswapV4PoolManager.ReturnDataAllocation

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

def beforeInitializeReplyMemory (mem : ByteArray) (free : UInt256) (sender : AccountAddress)
    (key : PoolKeyWords) (price : UInt256) (out : ByteArray) : ByteArray :=
  solcReturnDataMem (beforeInitializeMemory mem free sender key price) (free+⟨288⟩) out

def beforeInitializeReplyFree (free : UInt256) (out : ByteArray) : UInt256 :=
  returnDataEnd (free+⟨288⟩) out

theorem beforeInitializeReplyMemory_key {mem : ByteArray} {free keyPtr : UInt256} {key : PoolKeyWords}
    (hv : PoolKeyView mem keyPtr key) (hb : keyPtr.toNat+160 ≤ free.toNat) (hl : 96 ≤ keyPtr.toNat)
    (hf : free.toNat+320 < UInt256.size) (sender : AccountAddress) (price : UInt256) (out : ByteArray) :
    PoolKeyView (beforeInitializeReplyMemory mem free sender key price out) keyPtr key := by
  have h288 : (free+⟨288⟩).toNat = free.toNat+288 := uadd_word_ofNat_toNat free 288 (by omega)
  exact (beforeInitializeMemory_key hv hb hl sender price).returnData _ out hl
    (by rw [h288]; omega) (by rw [h288]; omega)

theorem beforeInitializeReplyMemory_free (mem : ByteArray) (free : UInt256) (sender : AccountAddress)
    (key : PoolKeyWords) (price : UInt256) (out : ByteArray)
    (hf : free.toNat+320 < UInt256.size) :
    memLoad (UInt256.ofNat 64) (beforeInitializeReplyMemory mem free sender key price out) =
      beforeInitializeReplyFree free out := by
  have h288 : (free+⟨288⟩).toNat = free.toNat+288 := uadd_word_ofNat_toNat free 288 (by omega)
  exact returnDataMemory_free _ _ _ (by rw [h288]; omega) (by rw [h288]; omega)

theorem beforeInitializeReplyFree_bounds (free : UInt256) (out : ByteArray)
    (hs : free.toNat ≤ 1024) (ho : out.size+4096 ≤ solcMaxU64) :
    free.toNat ≤ (beforeInitializeReplyFree free out).toNat ∧
      (beforeInitializeReplyFree free out).toNat+323 ≤ solcMaxU64 := by
  have hfit : free.toNat+out.size+1024 < UInt256.size := by
    change _ ≤ 2^64-1 at ho
    change _ < 2^256
    omega
  have h288 : (free+⟨288⟩).toNat = free.toNat+288 := uadd_word_ofNat_toNat free 288 (by omega)
  have hb := returnDataEnd_bounds (free+⟨288⟩) out (by rw [h288]; omega)
  rw [h288] at hb
  change free.toNat ≤ (returnDataEnd (free+⟨288⟩) out).toNat ∧
    (returnDataEnd (free+⟨288⟩) out).toNat+323 ≤ solcMaxU64
  omega

end Benchmarks.UniswapV4PoolManager
