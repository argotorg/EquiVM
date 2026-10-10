import Benchmarks.UniswapV4PoolManager.PoolKeyMemory
import Benchmarks.UniswapV4PoolManager.MemorySlice

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

structure PoolKeyView (mem : ByteArray) (ptr : UInt256) (key : PoolKeyWords) : Prop where
  slice : MemorySlice mem ptr.toNat (wordBytes (poolKeyWordList key))
  fits : ptr.toNat+160 < UInt256.size

theorem PoolKeyView.inBounds {mem ptr key} (h : PoolKeyView mem ptr key) : ptr.toNat+160 ≤ mem.size := by
  have hi := h.slice.inBounds
  simpa only [wordBytes_size, poolKeyWordList, List.length_cons, List.length_nil] using hi

theorem PoolKeyView.load {mem ptr key} (h : PoolKeyView mem ptr key) {i : Nat} {word : UInt256}
    (hi : (poolKeyWordList key)[i]? = some word) :
    memLoad (ptr+UInt256.ofNat (32*i)) mem = word := by
  have hib : i < 5 := by
    have hn := (List.getElem?_eq_some_iff.mp hi).1
    simpa only [poolKeyWordList, List.length_cons, List.length_nil] using hn
  exact h.slice.word_load hi (uadd_word_ofNat_toNat ptr (32*i) (by have := h.fits; omega))

theorem PoolKeyView.hash {mem ptr key} (h : PoolKeyView mem ptr key) :
    keccakWord ptr ⟨160⟩ mem = poolKeyId key := by
  have hr := h.slice.bytes
  rw [wordBytes_size] at hr
  change mem.readWithPadding ptr.toNat 160 = wordBytes (poolKeyWordList key) at hr
  change UInt256.ofNat (fromByteArrayBigEndian (KEC (mem.readWithPadding ptr.toNat 160))) = _
  rw [hr]
  exact keccakSlot_eq _

theorem PoolKeyView.writeWord {mem ptr key} (h : PoolKeyView mem ptr key) (off : Nat) (word : UInt256)
    (hd : ptr.toNat+160 ≤ off ∨ off+32 ≤ ptr.toNat) : PoolKeyView (writeWord mem off word) ptr key := by
  refine ⟨h.slice.writeWord off word ?_, h.fits⟩
  simpa only [wordBytes_size, poolKeyWordList, List.length_cons, List.length_nil] using hd

theorem poolKeyMemory_view (key : PoolKeyWords) : PoolKeyView (poolKeyMemory key) ⟨160⟩ key := by
  refine ⟨⟨?_, ?_⟩, by decide⟩
  · rw [wordBytes_size]
    exact poolKeyMemory_read key
  · rw [wordBytes_size, poolKeyMemory_size]; rfl

end Benchmarks.UniswapV4PoolManager
