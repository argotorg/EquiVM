import Benchmarks.UniswapV4PoolManager.WordArrayABI
import Benchmarks.UniswapV4PoolManager.WordArrayDecodeTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

def arrayHeaderMemory (n : Nat) : ByteArray :=
  writeWord (writeWord entryMemory 160 (UInt256.ofNat 32)) 192 (UInt256.ofNat n)

theorem arrayHeaderMemory_size (n : Nat) : (arrayHeaderMemory n).size = 224 := by
  simp only [arrayHeaderMemory, writeWord_sparse_size, show entryMemory.size = 96 by native_decide]
  decide

theorem arrayPayloadMemory_read (n : Nat) (words : List UInt256) (hlen : words.length = n) :
    (wordSequenceMemory (arrayHeaderMemory n) 224 words).readWithPadding 160 (64+32*n) =
      wordBytes ([UInt256.ofNat 32, UInt256.ofNat n] ++ words) := by
  have hr := wordSequenceMemory_read entryMemory 160 ([UInt256.ofNat 32, UInt256.ofNat n] ++ words)
  have hl : 32 * ([UInt256.ofNat 32, UInt256.ofNat n] ++ words).length = 64+32*n := by
    simp only [List.length_append, List.length_cons, List.length_nil, hlen]; omega
  rw [hl] at hr
  exact hr

theorem emptyArrayExtraWrite_read (word : UInt256) :
    (writeWord (arrayHeaderMemory 0) 224 word).readWithPadding 160 64 =
      wordBytes [UInt256.ofNat 32, UInt256.ofNat 0] := by
  rw [writeWord_sparse_read_preserved_unbounded _ _ _ _ _
    (by rw [arrayHeaderMemory_size]) (.inl (by decide))]
  exact arrayPayloadMemory_read 0 [] rfl

-- LIBRARY CANDIDATE: ABI bytes32-array return length when its byte span fits an EVM word.
theorem wordArrayReturnSpan_of_fit (n : Nat) (hfit : 224+32*n < UInt256.size) :
    (UInt256.sub (UInt256.ofNat (160+32*n)) (UInt256.ofNat 160) + UInt256.ofNat 64).toNat = 64+32*n := by
  have hs : UInt256.sub (UInt256.ofNat (160+32*n)) (UInt256.ofNat 160) = UInt256.ofNat (32*n) := by
    apply u256_inj
    rw [usub_ofNat_lit_toNat (by omega) (by omega), UInt256.toNat_ofNat_of_lt (by omega)]
    omega
  rw [hs, ofNat_add_words, UInt256.toNat_ofNat_of_lt (by omega)]
  omega

theorem wordArrayReturnSpan (n : Nat) (hn : n ≤ solcMaxU64) :
    (UInt256.sub (UInt256.ofNat (160+32*n)) (UInt256.ofNat 160) + UInt256.ofNat 64).toNat = 64+32*n :=
  wordArrayReturnSpan_of_fit n (by norm_num [solcMaxU64, UInt256.size] at hn ⊢; omega)

end Benchmarks.UniswapV4PoolManager
