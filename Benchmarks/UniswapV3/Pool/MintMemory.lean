import Benchmarks.UniswapV3.Pool.MintModel
import Benchmarks.UniswapV3.Pool.ModifyPositionMemory
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_021

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def mintCastMemory (mem : ByteArray) (p : UInt256) (a : MintArgs) : ByteArray :=
  writeWordArray (writeWord mem 64 (p + UInt256.ofNat 128)) p.toNat
    [EVM.word a.recipient.val, EVM.wordOfInt a.lower, EVM.wordOfInt a.upper]

theorem mintCastMemory_eq {mem : ByteArray} {aw p : UInt256}
    (a : MintArgs) (ha : a.Fits) (hm : HeapMemory mem aw p)
    (hb : p.toNat + 128 ≤ 2 ^ 200) :
    uniswapV3Pool_block_5837_memory (mem := mem) (x5 := EVM.wordOfInt a.upper)
      (x6 := EVM.wordOfInt a.lower) (x7 := EVM.word a.recipient.val) =
      mintCastMemory mem p a := by
  have hadd (n : Nat) (hn : n ≤ 128) : (p + UInt256.ofNat n).toNat = p.toNat + n :=
    uadd_word_ofNat_toNat p n (by change _ < 2 ^ 256; omega)
  have hload : memLoad (UInt256.ofNat 64) mem = p := hm.load64
  have haddr : UInt256.land
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1)) (EVM.word a.recipient.val) = EVM.word a.recipient.val := by
    rw [u256_land_comm]
    apply u256LandMaskCleanOfToNat _ _ (bits := 160) (by native_decide)
    exact addressWord_val_canonical a.recipient
  rw [uniswapV3Pool_block_5837_memory, hload, haddr,
    signextend_wordOfInt ⟨24, by decide⟩ (UInt256.ofNat 2) a.lower (by decide) (by decide),
    signextend_wordOfInt ⟨24, by decide⟩ (UInt256.ofNat 2) a.upper (by decide) (by decide),
    normalizeSint_eq_self ⟨24, by decide⟩ _ ha.1.1 ha.1.2,
    normalizeSint_eq_self ⟨24, by decide⟩ _ ha.2.1.1 ha.2.1.2,
    u256_add_comm (UInt256.ofNat 128) p, u256_add_comm (UInt256.ofNat 32) p,
    u256_add_comm (UInt256.ofNat 32) (p + UInt256.ofNat 32), u256_add_assoc,
    show UInt256.ofNat 32 + UInt256.ofNat 32 = UInt256.ofNat 64 from by decide,
    hadd 32 (by decide), hadd 64 (by decide)]
  simp only [mintCastMemory, writeWordArray, Reasoning.Theory.writeWord, Nat.add_assoc]
  rfl

theorem mintModifyMemory_eq (mem : ByteArray) (p : UInt256) (a : MintArgs)
    (hv : safeCast128Valid (Int.ofNat a.amount.toNat)) (hb : p.toNat + 128 ≤ 2 ^ 200) :
    uniswapV3Pool_block_5905_memory (mem := mintCastMemory mem p a)
      (x0 := a.amount) (x1 := p + UInt256.ofNat 96) =
      wordArrayAllocMem mem p (mintModifyArgs a).words := by
  have hp96 := uadd_word_ofNat_toNat p 96
    (show p.toNat + 96 < UInt256.size by change _ < 2 ^ 256; omega)
  have hc : UInt256.signextend (UInt256.ofNat 15) a.amount = a.amount := by
    rw [← wordOfInt_ofNat_toNat a.amount,
      signextend_wordOfInt ⟨128, by decide⟩ (UInt256.ofNat 15) _ (by decide) (by decide),
      normalizeSint_eq_self ⟨128, by decide⟩ _ ((safeCast128Valid_iff _).mp hv).1
        ((safeCast128Valid_iff _).mp hv).2, wordOfInt_ofNat_toNat]
  simp only [uniswapV3Pool_block_5905_memory, hc, hp96, mintCastMemory,
    wordArrayAllocMem, ModifyPositionArgs.words, mintModifyArgs, wordOfInt_ofNat_toNat,
    writeWordArray, Reasoning.Theory.writeWord, List.length_cons, List.length_nil, Nat.add_assoc]

end Benchmarks.UniswapV3.Pool
