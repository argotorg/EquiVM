import Benchmarks.UniswapV4PoolManager.PoolModifyValues
import Benchmarks.UniswapV4PoolManager.PoolKeyMemory
import Benchmarks.UniswapV4PoolManager.WordStoreMemory
import Benchmarks.UniswapV4PoolManager.Signed128Range
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_017

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

def poolModifyParamsWords (p : PoolModifyParams) : List UInt256 :=
  [accountWord p.owner, p.lower, p.upper, EVM.wordOfInt p.delta, p.spacing, p.salt]
def poolModifyParamsMemory (mem : ByteArray) (params ptr : UInt256) (p : PoolModifyParams) : ByteArray :=
  wordSequenceMemory (writeWord mem 64 ptr) params.toNat (poolModifyParamsWords p)

theorem poolModifyParamsMemory_eq (I : ExecutionEnv) (mem : ByteArray) (params ptr : UInt256) (p : PoolModifyParams)
    (ho : p.owner = I.source) (hf : params.toNat+192 < UInt256.size) (hd : signedFits ⟨128, by decide⟩ p.delta) :
    poolManagerBlocks.poolManager_block_5584_fallthrough_memory (ee := I) (mem := mem)
      (x0 := ptr) (x1 := p.spacing) (x2 := p.salt) (x7 := p.upper) (x8 := EVM.wordOfInt p.delta)
      (x9 := p.lower) (x11 := params) = poolModifyParamsMemory mem params ptr p := by
  have h32 := uadd_word_ofNat_toNat params 32 (by omega)
  have h64 := uadd_word_ofNat_toNat params 64 (by omega)
  have h96 := uadd_word_ofNat_toNat params 96 (by omega)
  have h128 := uadd_word_ofNat_toNat params 128 (by omega)
  have h160 := uadd_word_ofNat_toNat params 160 (by omega)
  have hs : UInt256.signextend (UInt256.ofNat 15) (EVM.wordOfInt p.delta) = EVM.wordOfInt p.delta :=
    signextend128_wordOfInt hd.1 hd.2
  simp only [poolManagerBlocks.poolManager_block_5584_fallthrough_memory, poolModifyParamsMemory,
    poolModifyParamsWords, wordSequenceMemory, Reasoning.Theory.writeWord, h32, h64, h96, h128, h160,
    hs, ho, accountWord, Nat.add_assoc]
  rfl

theorem poolModifyParamsMemory_size (mem : ByteArray) (params ptr : UInt256) (p : PoolModifyParams) :
    (poolModifyParamsMemory mem params ptr p).size = max mem.size (params.toNat+192) := by
  simp only [poolModifyParamsMemory, poolModifyParamsWords, wordSequenceMemory, writeWord_sparse_size]
  omega

theorem poolModifyParamsMemory_load (mem : ByteArray) (params ptr : UInt256) (p : PoolModifyParams)
    {i : Nat} {word : UInt256} (hi : (poolModifyParamsWords p)[i]? = some word)
    (hf : params.toNat+192 < UInt256.size) :
    memLoad (params+UInt256.ofNat (32*i)) (poolModifyParamsMemory mem params ptr p) = word := by
  have hib : i < 6 := by
    have hh := (List.getElem?_eq_some_iff.mp hi).1
    simpa only [poolModifyParamsWords, List.length_cons, List.length_nil] using hh
  have hp := uadd_word_ofNat_toNat params (32*i) (by omega)
  apply loadedWord_of_read
  · rw [hp, poolModifyParamsMemory_size]; omega
  · rw [hp]
    exact wordSequenceMemory_read_word _ _ _ hi

theorem poolModifyParamsMemory_free (mem : ByteArray) (params ptr : UInt256) (p : PoolModifyParams)
    (hp : 96 ≤ params.toNat) : memLoad (UInt256.ofNat 64) (poolModifyParamsMemory mem params ptr p) = ptr := by
  apply loadedWord_of_read
  · rw [poolModifyParamsMemory_size]; change 96 ≤ _; omega
  · change (poolModifyParamsMemory mem params ptr p).readWithPadding 64 32 = ptr.toByteArray
    rw [poolModifyParamsMemory, wordSequenceMemory_read_below (writeWord mem 64 ptr) params.toNat
      (poolModifyParamsWords p) 64 (by rw [writeWord_sparse_size]; omega) hp]
    exact writeWord_sparse_read_back _ _ _

theorem poolModifyParamsMemory_pool (mem : ByteArray) (params ptr : UInt256) (p : PoolModifyParams)
    (hp : 160 ≤ params.toNat) (hm : 160 ≤ mem.size) :
    memLoad (UInt256.ofNat 128) (poolModifyParamsMemory mem params ptr p) = memLoad (UInt256.ofNat 128) mem := by
  have hr : (poolModifyParamsMemory mem params ptr p).readWithPadding 128 32 = mem.readWithPadding 128 32 := by
    rw [poolModifyParamsMemory, wordSequenceMemory_read_below (writeWord mem 64 ptr) params.toNat
      (poolModifyParamsWords p) 128 (by rw [writeWord_sparse_size]; omega) hp]
    exact writeWord_sparse_read_preserved _ _ _ _ (Or.inr ⟨by decide, hm⟩)
  rw [memLoad, memLoad]
  simp only [show (UInt256.ofNat 128).toNat = 128 from rfl]
  rw [if_neg (by rw [poolModifyParamsMemory_size]; omega), if_neg (by omega), hr]

end Benchmarks.UniswapV4PoolManager
