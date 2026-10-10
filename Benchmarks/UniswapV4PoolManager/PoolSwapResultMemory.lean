import Benchmarks.UniswapV4PoolManager.PoolSwapPreludeMemory
import Benchmarks.UniswapV4PoolManager.WordStructInitMemory
import Benchmarks.UniswapV4PoolManager.PoolSwapMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

theorem poolSwapResultZeroMem_eq (mem : ByteArray) (state : UInt256) (hf : state.toNat+96 < UInt256.size) :
    poolSwapResultZeroMem mem state = wordSequenceMemory mem state.toNat [⟨0⟩, ⟨0⟩, ⟨0⟩] := by
  have h32 := uadd_word_ofNat_toNat state 32 (by omega)
  have h64 := uadd_word_ofNat_toNat state 64 (by omega)
  simp only [poolSwapResultZeroMem, wordSequenceMemory, h32, h64, Nat.add_assoc]

theorem poolSwapResultInitMem_eq (mem : ByteArray) (state packed liquidity : UInt256)
    (hf : state.toNat+96 < UInt256.size) :
    poolSwapResultInitMem mem state packed liquidity = wordSequenceMemory mem state.toNat
      (poolSwapResultWordList (poolSwapInitialResult packed liquidity)) := by
  have h32 := uadd_word_ofNat_toNat state 32 (by omega)
  have h64 := uadd_word_ofNat_toNat state 64 (by omega)
  simp only [poolSwapResultInitMem, poolSwapResultWordList, poolSwapInitialResult, wordSequenceMemory,
    h32, h64, Nat.add_assoc]

theorem poolSwapResultInitMem_view (mem : ByteArray) (state packed liquidity : UInt256)
    (hf : state.toNat+96 < UInt256.size) :
    WordStructView (poolSwapResultInitMem mem state packed liquidity) state
      (poolSwapResultWordList (poolSwapInitialResult packed liquidity)) := by
  rw [poolSwapResultInitMem_eq mem state packed liquidity hf]
  exact wordStructView_sequence _ _ _ (by intro hh; cases hh) hf

theorem poolSwapResultZeroMem_preserves {mem : ByteArray} {ptr state : UInt256} {words : List UInt256}
    (h : WordStructView mem ptr words) (hf : state.toNat+96 < UInt256.size)
    (hb : ptr.toNat+32*words.length ≤ state.toNat) :
    WordStructView (poolSwapResultZeroMem mem state) ptr words := by
  rw [poolSwapResultZeroMem_eq mem state hf]
  exact h.write_sequence _ _ (.inl hb)

theorem poolSwapResultInitMem_preserves {mem : ByteArray} {ptr state : UInt256} {words : List UInt256}
    (h : WordStructView mem ptr words) (packed liquidity : UInt256) (hf : state.toNat+96 < UInt256.size)
    (hb : ptr.toNat+32*words.length ≤ state.toNat) :
    WordStructView (poolSwapResultInitMem mem state packed liquidity) ptr words := by
  rw [poolSwapResultInitMem_eq mem state packed liquidity hf]
  exact h.write_sequence _ _ (.inl hb)

theorem poolSwapResultZeroMem_free (mem : ByteArray) (state : UInt256)
    (hi : 96 ≤ mem.size) (hl : 96 ≤ state.toNat) (hf : state.toNat+96 < UInt256.size) :
    memLoad (UInt256.ofNat 64) (poolSwapResultZeroMem mem state) = memLoad (UInt256.ofNat 64) mem := by
  rw [poolSwapResultZeroMem_eq mem state hf]
  exact wordSequenceMemory_load_before _ _ _ _ hi hl

theorem poolSwapResultInitMem_free (mem : ByteArray) (state packed liquidity : UInt256)
    (hi : 96 ≤ mem.size) (hl : 96 ≤ state.toNat) (hf : state.toNat+96 < UInt256.size) :
    memLoad (UInt256.ofNat 64) (poolSwapResultInitMem mem state packed liquidity) = memLoad (UInt256.ofNat 64) mem := by
  rw [poolSwapResultInitMem_eq mem state packed liquidity hf]
  exact wordSequenceMemory_load_before _ _ _ _ hi hl

end Benchmarks.UniswapV4PoolManager
