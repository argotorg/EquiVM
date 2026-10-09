import Benchmarks.Morpho.MorphoBlue.AddressWordBytesABI
import Benchmarks.Morpho.MorphoBlue.CalldataBytesDecode
import Benchmarks.Morpho.MorphoBlue.Routines

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def flashLoanDecodeStack (cd : ByteArray) (R : List UInt256) : List UInt256 :=
  [calldataWord cd (4 + (calldataWord cd 68).toNat),
    (UInt256.ofNat 4 + calldataWord cd 68) + UInt256.ofNat 32,
    solcAddrMask, UInt256.ofNat 0, calldataWord cd 36, calldataWord cd 4, UInt256.ofNat 0] ++ R

theorem morphoFlashLoanDecode {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem out : ByteArray} {aw : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (hstack : R.length + 16 ≤ 1024) (hs : 4 ≤ ee.calldata.size)
    (hsize : ee.calldata.size < UInt256.size)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 927) (UInt256.ofNat 0 :: R) mem aw out σ k C) :
    (¬ AddressWordBytesBounds ee.calldata ∧ RDrev (deployedRuntime v) g s0) ∨
    (AddressWordBytesBounds ee.calldata ∧ ∃ k' C',
      RD (deployedRuntime v) ee g s0 (UInt256.ofNat 1033)
        (flashLoanDecodeStack ee.calldata R) mem aw out σ k' C') := by
  have hbad (hc : UInt256.slt (UInt256.sub (UInt256.ofNat ee.calldata.size) ⟨4⟩)
      (UInt256.ofNat 96) = ⟨1⟩) : RDrev (deployedRuntime v) g s0 := by
    have rd := morphoBlocks.morpho_block_927_taken (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega)
      (by rw [wordAddNegFour, hc]; decide)
      (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
    exact morphoBlocks.morpho_block_440 (immWords := wordsOf (immStore v)) (by simp; omega) rd
  by_cases hl : 100 ≤ ee.calldata.size
  swap
  · exact .inl ⟨fun hb => hl hb.1,
      hbad (solcCalldataStaticLenCheckShort (words := 3) hs (by omega) hsize (by decide))⟩
  by_cases hh : ee.calldata.size < 2 ^ 255 + 4
  swap
  · exact .inl ⟨fun hb => by have := hb.2.1; omega,
      hbad (solcCalldataStaticLenCheckHuge (words := 3) (by omega) hsize (by decide))⟩
  have rd0 := morphoBlocks.morpho_block_927_fallthrough (immWords := wordsOf (immStore v))
    (by simp; omega) (by rw [wordAddNegFour]; exact solcCalldataStaticLenCheckOk (words := 3) hl hh hsize) h
  have rd1 := morphoBlocks.morpho_block_969 (immWords := wordsOf (immStore v))
    (by simp; omega) (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd0
  by_cases ha : (calldataWord ee.calldata 4).toNat < EVM.addressModulus
  swap
  · exact .inl ⟨fun hb => ha hb.2.2.1, morphoDecodeAddress4Revert (v := v)
      (by change R.length + 1 + 4 ≤ 1024; omega) ha rd1⟩
  obtain ⟨k2, C2, rd2⟩ := morphoDecodeAddress4Ok (v := v)
    (by change R.length + 1 + 4 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) ha rd1
  change RD _ _ _ _ (UInt256.ofNat 976) (calldataWord ee.calldata 4 :: UInt256.ofNat 0 :: R)
    _ _ _ _ _ _ at rd2
  let off := calldataWord ee.calldata 68
  by_cases ho : off.toNat ≤ solcMaxU64
  swap
  · have rd := morphoBlocks.morpho_block_976_taken (immWords := wordsOf (immStore v))
      (by omega) (by
        change UInt256.gt off (UInt256.ofNat solcMaxU64) ≠ UInt256.ofNat 0
        rw [ugt_one (by change solcMaxU64 < off.toNat; omega)]; decide)
      (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd2
    exact .inl ⟨fun hb => ho hb.2.2.2.1,
      morphoBlocks.morpho_block_1249 (immWords := wordsOf (immStore v))
        (by change R.length + 3 + 2 ≤ 1024; omega) rd⟩
  have rd3 := morphoBlocks.morpho_block_976_fallthrough (immWords := wordsOf (immStore v))
    (by omega) (ugt_zero ho) rd2
  have rd4 := morphoBlocks.morpho_block_999 (immWords := wordsOf (immStore v))
    (by change R.length + 4 + 5 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd3
  have hstart : (UInt256.ofNat 4 + off).toNat = 4 + off.toNat := add4_word_toNat off ho
  rcases morphoDecodeCalldataBytes (v := v) (start := UInt256.ofNat 4 + off)
      (by change R.length + 5 + 8 ≤ 1024; omega)
      (by rw [hstart]; norm_num [solcMaxU64] at ho; omega) hsize
      (by rw [morphoPatchedValidJumps v]; jump_dest) rd4 with
    ⟨hb, hr⟩ | ⟨hh', hb, k5, C5, rd5⟩
  · rw [hstart] at hb
    exact .inl ⟨fun h => hb ⟨h.2.1, h.2.2.2.2⟩, hr⟩
  · rw [hstart] at hb rd5
    exact .inr ⟨⟨hl, hh', ha, ho, hb⟩, _, _, rd5⟩

end Benchmarks.Morpho.MorphoBlue
