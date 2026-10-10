import Benchmarks.UniswapV4PoolManager.PoolKeyABI
import Benchmarks.UniswapV4PoolManager.WordArrayMemory
import Benchmarks.UniswapV4PoolManager.MappingMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 3000

def poolKeyWordList (key : PoolKeyWords) : List UInt256 :=
  [key.currency0, key.currency1, key.fee, key.tickSpacing, key.hooks]

def poolKeyAllocationMemory : ByteArray := writeWord entryMemory 64 ⟨320⟩
def poolKeyMemory (key : PoolKeyWords) : ByteArray :=
  wordSequenceMemory poolKeyAllocationMemory 160 (poolKeyWordList key)
def poolKeyId (key : PoolKeyWords) : UInt256 := uInt256OfByteArray (KEC (wordBytes (poolKeyWordList key)))
def poolKeySlot (key : PoolKeyWords) : UInt256 := mappingSlotWord (poolKeyId key) ⟨6⟩

-- LIBRARY CANDIDATE: any indexed word can be recovered from sequential stores.
theorem wordSequenceMemory_read_word (mem : ByteArray) (off : Nat) (words : List UInt256)
    {i : Nat} {word : UInt256} (hi : words[i]? = some word) :
    (wordSequenceMemory mem off words).readWithPadding (off+32*i) 32 = word.toByteArray := by
  induction words generalizing mem off i with
  | nil => simp at hi
  | cons first rest ih =>
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
          subst word
          rw [Nat.mul_zero, Nat.add_zero, wordSequenceMemory,
            wordSequenceMemory_read_below _ _ _ _ (by rw [writeWord_sparse_size]; omega) (le_refl _),
            writeWord_sparse_read_back]
      | succ i =>
          rw [wordSequenceMemory, show off+32*(i+1) = (off+32)+32*i by omega]
          exact ih _ _ hi

theorem poolKeyAllocationMemory_size : poolKeyAllocationMemory.size = 96 := by native_decide

theorem poolKeyMemory_size (key : PoolKeyWords) : (poolKeyMemory key).size = 320 := by
  simp only [poolKeyMemory, poolKeyWordList, wordSequenceMemory, writeWord_sparse_size,
    poolKeyAllocationMemory_size]
  decide

theorem poolKeyMemory_read (key : PoolKeyWords) :
    (poolKeyMemory key).readWithPadding 160 160 = wordBytes (poolKeyWordList key) :=
  wordSequenceMemory_read poolKeyAllocationMemory 160 (poolKeyWordList key)

theorem poolKeyMemory_load (key : PoolKeyWords) {i : Nat} {word : UInt256}
    (hi : (poolKeyWordList key)[i]? = some word) :
    memLoad (UInt256.ofNat (160+32*i)) (poolKeyMemory key) = word := by
  have hib : i < 5 := by
    have hh := (List.getElem?_eq_some_iff.mp hi).1
    simpa only [poolKeyWordList, List.length_cons, List.length_nil] using hh
  have hf : 160+32*i < UInt256.size := by norm_num [UInt256.size]; omega
  apply loadedWord_of_read
  · rw [UInt256.toNat_ofNat_of_lt hf, poolKeyMemory_size]; omega
  · rw [UInt256.toNat_ofNat_of_lt hf]
    exact wordSequenceMemory_read_word _ _ _ hi

theorem poolKeyMemory_load64 (key : PoolKeyWords) : memLoad ⟨64⟩ (poolKeyMemory key) = ⟨320⟩ := by
  apply loadedWord_of_read
  · rw [poolKeyMemory_size]; decide
  · change (wordSequenceMemory poolKeyAllocationMemory 160 (poolKeyWordList key)).readWithPadding 64 32 = _
    rw [wordSequenceMemory_read_below _ _ _ _ (by rw [poolKeyAllocationMemory_size]) (by decide)]
    native_decide

theorem poolKeyMemory_hash (key : PoolKeyWords) :
    keccakWord ⟨160⟩ ⟨160⟩ (poolKeyMemory key) = poolKeyId key := by
  change UInt256.ofNat (fromByteArrayBigEndian ((KEC ((poolKeyMemory key).readWithPadding 160 160)))) = _
  rw [poolKeyMemory_read]
  exact keccakSlot_eq _

end Benchmarks.UniswapV4PoolManager
