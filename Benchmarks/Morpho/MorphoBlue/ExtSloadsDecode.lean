import Benchmarks.Morpho.MorphoBlue.WordArrayABI
import Benchmarks.Morpho.MorphoBlue.Dispatch
import Benchmarks.Morpho.MorphoBlue.RuntimeBlocks_019
import Benchmarks.Morpho.MorphoBlue.RuntimeBlocks_020
import Benchmarks.EAS.Attester.WordHelpers

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

-- GENERALIZES array_end_bound_of_ugt_zero to expose the non-wrapping address itself.
theorem wordArrayEnd_toNat {off len : UInt256}
    (ho : off.toNat ≤ solcMaxU64) (hn : len.toNat ≤ solcMaxU64) :
    ((off + UInt256.shiftLeft len (UInt256.ofNat 5)) + UInt256.ofNat 36).toNat =
      off.toNat + 32 * len.toNat + 36 := by
  have hfit : off.toNat + 32 * len.toNat + 36 < UInt256.size := by
    norm_num [solcMaxU64, UInt256.size] at ho hn ⊢; omega
  have hs : UInt256.shiftLeft len (UInt256.ofNat 5) = UInt256.ofNat (32 * len.toNat) := by
    simpa only [u256_ofNat_toNat] using (shiftLeft5_ofNat_eq (n := len.toNat) (by omega))
  have he : (off + UInt256.shiftLeft len (UInt256.ofNat 5)) + UInt256.ofNat 36 =
      UInt256.ofNat (off.toNat + 32 * len.toNat + 36) := by
    conv_lhs => rw [← u256_ofNat_toNat off, hs, ofNat_add_words, ofNat_add_words]
  rw [he, UInt256.toNat_ofNat_of_lt hfit]

theorem morphoExtSloadsDecode {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {σ : AccountMap} {k C : Nat}
    (hs : 4 ≤ ee.calldata.size) (hsize : ee.calldata.size < UInt256.size)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 6767) [UInt256.ofNat 0]
      mem aw rdata σ k C) :
    (¬ WordArrayBounds ee.calldata ∧ RDrev (deployedRuntime v) g s0) ∨
    (WordArrayBounds ee.calldata ∧ ∃ aw' k' C',
      RD (deployedRuntime v) ee g s0 (UInt256.ofNat 6873)
        [calldataWord ee.calldata (4 + (calldataWord ee.calldata 4).toNat), UInt256.ofNat 5,
         UInt256.ofNat 32, UInt256.ofNat 36, calldataWord ee.calldata 4, UInt256.ofNat 0]
        mem aw' rdata σ k' C') := by
  by_cases hshort : ee.calldata.size < 36
  · have hc := solcCalldataStaticLenCheckShort (words := 1) hs hshort hsize (by decide)
    have rd := morphoBlocks.morpho_block_6767_taken (immWords := wordsOf (immStore v))
      (by decide) (by simpa only [wordAddNegFour, hc] using (show (⟨1⟩ : UInt256) ≠ ⟨0⟩ by decide))
      (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
    exact .inl ⟨by intro hb; exact (Nat.not_lt_of_ge hb.1) hshort,
      morphoBlocks.morpho_block_1249 (immWords := wordsOf (immStore v)) (by decide) rd⟩
  by_cases hhuge : 2 ^ 255 + 4 ≤ ee.calldata.size
  · have hc := solcCalldataStaticLenCheckHuge (words := 1) hhuge hsize (by decide)
    have rd := morphoBlocks.morpho_block_6767_taken (immWords := wordsOf (immStore v))
      (by decide) (by simpa only [wordAddNegFour, hc] using (show (⟨1⟩ : UInt256) ≠ ⟨0⟩ by decide))
      (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
    exact .inl ⟨by intro hb; have := hb.2.1; omega,
      morphoBlocks.morpho_block_1249 (immWords := wordsOf (immStore v)) (by decide) rd⟩
  have hc := solcCalldataStaticLenCheckOk (words := 1) (by omega) (by omega) hsize
  have rd0 := morphoBlocks.morpho_block_6767_fallthrough (immWords := wordsOf (immStore v))
    (by decide) (by simpa only [wordAddNegFour] using hc) h
  change RD _ _ _ _ _ [UInt256.ofNat 32, UInt256.ofNat 0] _ _ _ _ _ _ at rd0
  let off := calldataWord ee.calldata 4
  let len := calldataWord ee.calldata (4 + off.toNat)
  by_cases ho : off.toNat ≤ solcMaxU64
  swap
  · have rd := morphoBlocks.morpho_block_6810_taken (immWords := wordsOf (immStore v))
      (by decide) (by
        change UInt256.gt off (UInt256.ofNat 18446744073709551615) ≠ UInt256.ofNat 0
        rw [ugt_one (show (UInt256.ofNat 18446744073709551615).toNat < off.toNat from Nat.lt_of_not_ge ho)]
        decide)
      (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd0
    exact .inl ⟨by intro hb; exact ho hb.2.2.1,
      morphoBlocks.morpho_block_6705 (immWords := wordsOf (immStore v)) (by decide) rd⟩
  have rd1 := morphoBlocks.morpho_block_6810_fallthrough (immWords := wordsOf (immStore v))
    (by decide) (ugt_zero ho) rd0
  change RD _ _ _ _ _ [UInt256.ofNat 32, UInt256.ofNat 18446744073709551615, off, UInt256.ofNat 0]
    _ _ _ _ _ _ at rd1
  have hof : (off + UInt256.ofNat 35).toNat = off.toNat + 35 :=
    uadd_word_ofNat_toNat off 35 (by norm_num [solcMaxU64, UInt256.size] at ho ⊢; omega)
  have hos : (off + UInt256.ofNat 35).toNat < 2 ^ 255 := by
    rw [hof]; norm_num [solcMaxU64] at ho; omega
  by_cases hh : ee.calldata.size < 2 ^ 255
  swap
  · have hz := slt_zero_low_high hos (by rw [UInt256.toNat_ofNat_of_lt hsize]; omega)
    have rd := morphoBlocks.morpho_block_6831_taken (immWords := wordsOf (immStore v))
      (by decide) (by rw [hz]; decide)
      (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd1
    exact .inl ⟨fun hb ↦ hh hb.2.1, morphoBlocks.morpho_block_6705 (immWords := wordsOf (immStore v)) (by decide) rd⟩
  by_cases hlw : 4 + off.toNat + 32 ≤ ee.calldata.size
  swap
  · have hz := slt_lit_zero hh (by rw [hof]; omega) hos
    have rd := morphoBlocks.morpho_block_6831_taken (immWords := wordsOf (immStore v))
      (by decide) (by rw [hz]; decide)
      (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd1
    exact .inl ⟨fun hb ↦ hlw hb.2.2.2.1, morphoBlocks.morpho_block_6705 (immWords := wordsOf (immStore v)) (by decide) rd⟩
  have hone := slt_lit_one_low hh (by rw [hof]; omega)
  have rd2 := morphoBlocks.morpho_block_6831_fallthrough (immWords := wordsOf (immStore v))
    (by decide) (by rw [hone]; rfl) rd1
  have hload : uInt256OfByteArray (ee.calldata.readBytes ((UInt256.ofNat 4) + off).toNat 32) =
      len := by
        have haddr : ((UInt256.ofNat 4) + off).toNat = 4 + off.toNat := add4_word_toNat off ho
        rw [haddr]
  by_cases hn : len.toNat ≤ solcMaxU64
  swap
  · have rd := morphoBlocks.morpho_block_6842_taken (immWords := wordsOf (immStore v))
      (by decide) (by rw [hload, ugt_one (show (UInt256.ofNat 18446744073709551615).toNat < len.toNat from Nat.lt_of_not_ge hn)]; decide)
      (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd2
    exact .inl ⟨fun hb ↦ hn hb.2.2.2.2.1, morphoBlocks.morpho_block_6705 (immWords := wordsOf (immStore v)) (by decide) rd⟩
  have rd3 := morphoBlocks.morpho_block_6842_fallthrough (immWords := wordsOf (immStore v))
    (by decide) (by rw [hload]; exact ugt_zero hn) rd2
  change RD _ _ _ _ _ [UInt256.ofNat 32,
    uInt256OfByteArray (ee.calldata.readBytes ((UInt256.ofNat 4) + off).toNat 32), off, UInt256.ofNat 0]
    _ _ _ _ _ _ at rd3
  rw [hload] at rd3
  have hend := wordArrayEnd_toNat ho hn
  by_cases hp : 4 + off.toNat + 32 + 32 * len.toNat ≤ ee.calldata.size
  swap
  · have rd := morphoBlocks.morpho_block_6854_taken (immWords := wordsOf (immStore v))
      (by decide) (by rw [ugt_one (by rw [hend, UInt256.toNat_ofNat_of_lt hsize]; omega)]; decide)
      (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd3
    exact .inl ⟨fun hb ↦ hp hb.2.2.2.2.2, morphoBlocks.morpho_block_7120 (immWords := wordsOf (immStore v)) (by decide) rd⟩
  have rd4 := morphoBlocks.morpho_block_6854_fallthrough (immWords := wordsOf (immStore v))
    (by decide) (ugt_zero (by rw [hend, UInt256.toNat_ofNat_of_lt hsize]; omega)) rd3
  exact .inr ⟨⟨by omega, hh, ho, hlw, hn, hp⟩, _, _, _, rd4⟩

end Benchmarks.Morpho.MorphoBlue
