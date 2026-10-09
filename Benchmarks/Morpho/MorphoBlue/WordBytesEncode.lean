import Benchmarks.Morpho.MorphoBlue.WordBytesCallMemory
import Benchmarks.EAS.Attester.WordHelpers

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

theorem morphoWordBytesEncode {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem out : ByteArray} {aw ptr value srcOff len ret : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (selector : UInt256)
    (hstack : R.length + 11 ≤ 1024) (hptr : ptr.toNat < 2 ^ 64)
    (hlen : len.toNat ≤ solcMaxU64)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 12700)
      ((ptr + UInt256.ofNat 4) :: value :: srcOff :: len :: ret :: R)
      (writeWord mem ptr.toNat selector) aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ret
      ((ptr + UInt256.ofNat (100 + paddedSize len.toNat)) :: R)
      (wordBytesCallMem selector value ee.calldata mem srcOff.toNat ptr.toNat len.toNat) aw' out σ k' C' := by
  obtain ⟨a1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_12700_packed
    (immWords := wordsOf (immStore v)) hstack hvalid h
  have hp (n : Nat) (hn : n ≤ 132) : (ptr + UInt256.ofNat n).toNat = ptr.toNat + n :=
    uadd_word_ofNat_toNat ptr n (by change _ < 2 ^ 256; omega)
  have hadd (n : Nat) : (ptr + UInt256.ofNat 4) + UInt256.ofNat n = ptr + UInt256.ofNat (4 + n) := by
    rw [u256_add_assoc ptr, ofNat_add_words]
  have hlfit : len.toNat + 31 < UInt256.size := by
    norm_num [solcMaxU64, UInt256.size] at hlen ⊢; omega
  have hr : UInt256.land (len + UInt256.ofNat 31)
      (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904) =
      UInt256.ofNat (paddedSize len.toNat) := by
    have hn := nat_le_paddedSize len.toNat
    have hb := paddedSize_le_add31 len.toNat
    conv_lhs => rw [← u256_ofNat_toNat len, returnReserveSize_solc]
    apply u256_inj
    rw [returnReserveSize_toNat hlfit, UInt256.toNat_ofNat_of_lt (by omega)]
    exact Nat.mul_comm _ _
  have hend : (UInt256.ofNat (paddedSize len.toNat) + (ptr + UInt256.ofNat 4)) + UInt256.ofNat 96 =
      ptr + UInt256.ofNat (100 + paddedSize len.toNat) := by
    rw [u256_add_comm (UInt256.ofNat (paddedSize len.toNat)), u256_add_assoc ptr,
      ofNat_add_words, u256_add_assoc ptr, ofNat_add_words]
    congr 2
    omega
  have hpadd : ((ptr + UInt256.ofNat 4) + len + UInt256.ofNat 96).toNat = ptr.toNat + 100 + len.toNat := by
    have h4 := hp 4 (by decide)
    have hl : ((ptr + UInt256.ofNat 4) + len).toNat = ptr.toNat + 4 + len.toNat := by
      rw [uadd_toNat, h4, Nat.mod_eq_of_lt (by norm_num [solcMaxU64, UInt256.size] at hlen ⊢; omega)]
    rw [uadd_word_ofNat_toNat _ 96 (by rw [hl]; norm_num [solcMaxU64, UInt256.size] at hlen ⊢; omega), hl]
    omega
  dsimp only [morphoBlocks.morpho_block_12700_stack, morphoBlocks.morpho_block_12700_memory] at rd1
  rw [hr, hend, hpadd, hadd 96, hp 100 (by decide), hadd 64, hp 68 (by decide), hadd 32,
    hp 36 (by decide), hp 4 (by decide)] at rd1
  refine ⟨a1, k1, C1, ?_⟩
  simpa only [wordBytesCallMem, copyWithZeroWord, staticWordCallMem, returnWordWrites,
    writeCascade, Reasoning.Theory.writeWord, u256_ofNat_toNat, Nat.add_assoc, Nat.reduceAdd] using rd1

end Benchmarks.Morpho.MorphoBlue
