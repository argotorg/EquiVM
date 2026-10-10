import Benchmarks.UniswapV4PoolManager.PoolInitializeTrace
import Benchmarks.UniswapV4PoolManager.PoolKeyPreservation

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

def initializeEventWords (mem : ByteArray) (feePtr hooksPtr spacingPtr price tick : UInt256) : List UInt256 :=
  [UInt256.land (memLoad feePtr mem) (UInt256.ofNat 16777215),
    UInt256.signextend (UInt256.ofNat 2) (memLoad spacingPtr mem),
    UInt256.land (memLoad hooksPtr mem) solcAddrMask, price,
    UInt256.signextend (UInt256.ofNat 2) tick]

theorem initializeEventMemory_sequence (mem : ByteArray) (free feePtr hooksPtr spacingPtr price tick : UInt256)
    (hf : free.toNat+128 < UInt256.size) (hfree : memLoad (UInt256.ofNat 64) mem = free) :
    initializeEventMemory mem feePtr hooksPtr spacingPtr price tick =
      wordSequenceMemory mem free.toNat (initializeEventWords mem feePtr hooksPtr spacingPtr price tick) := by
  have h32 := uadd_word_ofNat_toNat free 32 (by omega : free.toNat+32 < UInt256.size)
  have h64 := uadd_word_ofNat_toNat free 64 (by omega : free.toNat+64 < UInt256.size)
  have h96 := uadd_word_ofNat_toNat free 96 (by omega : free.toNat+96 < UInt256.size)
  have h128 := uadd_word_ofNat_toNat free 128 hf
  simp only [initializeEventMemory, poolManagerBlocks.poolManager_block_4418_memory,
    hfree, h32, h64, h96, h128, initializeEventWords, wordSequenceMemory, Nat.add_assoc]
  rfl

theorem initializeEventMemory_key {mem : ByteArray} {free keyPtr : UInt256} {key : PoolKeyWords}
    (hv : PoolKeyView mem keyPtr key) (hb : keyPtr.toNat+160 ≤ free.toNat)
    (hf : free.toNat+128 < UInt256.size) (hfree : memLoad (UInt256.ofNat 64) mem = free)
    (feePtr hooksPtr spacingPtr price tick : UInt256) :
    PoolKeyView (initializeEventMemory mem feePtr hooksPtr spacingPtr price tick) keyPtr key := by
  rw [initializeEventMemory_sequence _ _ _ _ _ _ _ hf hfree]
  refine ⟨hv.slice.wordSequence _ _ ?_, hv.fits⟩
  simpa only [wordBytes_size, poolKeyWordList, List.length_cons, List.length_nil] using hb

theorem initializeEventMemory_free {mem : ByteArray} {free : UInt256}
    (hm : 96 ≤ mem.size) (hl : 96 ≤ free.toNat) (hf : free.toNat+128 < UInt256.size)
    (hfree : memLoad (UInt256.ofNat 64) mem = free) (feePtr hooksPtr spacingPtr price tick : UInt256) :
    memLoad (UInt256.ofNat 64) (initializeEventMemory mem feePtr hooksPtr spacingPtr price tick) = free := by
  rw [initializeEventMemory_sequence _ _ _ _ _ _ _ hf hfree]
  have hs := (wordSequenceMemory_prefix mem free.toNat
    (initializeEventWords mem feePtr hooksPtr spacingPtr price tick)).size
  rw [memLoad, if_neg (by change ¬64 ≥ _; omega),
    wordSequenceMemory_read_below _ _ _ _ (by change 64+32 ≤ _; omega) (by change 64+32 ≤ _; omega)]
  have hn : ¬(UInt256.ofNat 64).toNat ≥ mem.size := by change ¬64 ≥ mem.size; omega
  simpa only [memLoad, if_neg hn] using hfree

end Benchmarks.UniswapV4PoolManager
