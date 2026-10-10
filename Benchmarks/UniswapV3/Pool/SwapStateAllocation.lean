import Benchmarks.UniswapV3.Pool.SwapStateMiddleTrace
import Benchmarks.UniswapV3.Pool.SwapStateTailTrace
import Benchmarks.UniswapV3.Pool.SwapInitStack

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

def swapStateInitWords (remaining price tick growth liquidity : UInt256) : List UInt256 :=
  [remaining, ⟨0⟩, price, tick, growth, ⟨0⟩, liquidity]

theorem swapStateAllocation_eq (mem : ByteArray) (p remaining price tick growth liquidity : UInt256)
    (hb : p.toNat + 224 < UInt256.size) :
    swapStateTailMem
      (swapStateMiddleMem (swapStateHeadMem mem p remaining) (p + UInt256.ofNat 64) price tick)
      (p + UInt256.ofNat 128) growth liquidity =
      wordArrayAllocMem mem p (swapStateInitWords remaining price tick growth liquidity) := by
  have h32 := uadd_word_ofNat_toNat p 32 (by omega)
  have h64 := uadd_word_ofNat_toNat p 64 (by omega)
  have h96 := uadd_word_ofNat_toNat p 96 (by omega)
  have h128 := uadd_word_ofNat_toNat p 128 (by omega)
  have h160 := uadd_word_ofNat_toNat p 160 (by omega)
  have h192 := uadd_word_ofNat_toNat p 192 (by omega)
  have h96w : UInt256.ofNat 32 + (p + UInt256.ofNat 64) = p + UInt256.ofNat 96 := by
    rw [u256_add_comm (UInt256.ofNat 32), u256_add_assoc]; rfl
  have h160w : UInt256.ofNat 32 + (p + UInt256.ofNat 128) = p + UInt256.ofNat 160 := by
    rw [u256_add_comm (UInt256.ofNat 32), u256_add_assoc]; rfl
  have h192w : UInt256.ofNat 32 + (UInt256.ofNat 32 + (p + UInt256.ofNat 128)) =
      p + UInt256.ofNat 192 := by
    rw [h160w, u256_add_comm (UInt256.ofNat 32), u256_add_assoc]; rfl
  unfold swapStateTailMem swapStateMiddleMem swapStateHeadMem
  rw [h192w, h160w, h96w, u256_add_comm (UInt256.ofNat 32) p]
  simp only [wordArrayAllocMem, swapStateInitWords, writeWordArray,
    List.length_cons, List.length_nil, h32, h64, h96, h128, h160, h192]

theorem swapStateMiddleMem_prefix (mem : ByteArray) (cursor price tick : UInt256)
    (hb : cursor.toNat + 32 < UInt256.size) :
    MemoryPrefix mem (swapStateMiddleMem mem cursor price tick) cursor.toNat := by
  have h32 : (UInt256.ofNat 32 + cursor).toNat = cursor.toNat + 32 := by
    rw [u256_add_comm]
    exact uadd_word_ofNat_toNat cursor 32 hb
  exact (memoryPrefix_sparse_writeWord mem cursor.toNat cursor.toNat price
    (Or.inl (by omega))).trans
    (memoryPrefix_sparse_writeWord _ (UInt256.ofNat 32 + cursor).toNat cursor.toNat tick
      (Or.inl (by rw [h32]; omega)))

end Benchmarks.UniswapV3.Pool
