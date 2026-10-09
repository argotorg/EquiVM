import Benchmarks.Morpho.MorphoBlue.CalldataBytesABI
import Benchmarks.Morpho.MorphoBlue.Dispatch
import Benchmarks.Morpho.MorphoBlue.RuntimeBlocks_031
import Benchmarks.EAS.Attester.WordHelpers

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

theorem morphoDecodeCalldataBytes {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem out : ByteArray} {aw start ret : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024) (hstart : start.toNat < 2 ^ 65)
    (hsize : ee.calldata.size < UInt256.size)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 11752)
      (start :: UInt256.ofNat ee.calldata.size :: ret :: R) mem aw out σ k C) :
    (¬ (ee.calldata.size < 2 ^ 255 ∧ CalldataBytesBounds ee.calldata start.toNat) ∧
      RDrev (deployedRuntime v) g s0) ∨
    (ee.calldata.size < 2 ^ 255 ∧ CalldataBytesBounds ee.calldata start.toNat ∧ ∃ k' C',
      RD (deployedRuntime v) ee g s0 ret
        (calldataWord ee.calldata start.toNat :: (start + UInt256.ofNat 32) :: R) mem aw out σ k' C') := by
  have h31 : (start + UInt256.ofNat 31).toNat = start.toNat + 31 :=
    uadd_word_ofNat_toNat start 31 (by norm_num [UInt256.size] at hstart ⊢; omega)
  have hlow : (start + UInt256.ofNat 31).toNat < 2 ^ 255 := by rw [h31]; omega
  have hbad (hc : UInt256.isZero (UInt256.slt (start + UInt256.ofNat 31)
      (UInt256.ofNat ee.calldata.size)) ≠ UInt256.ofNat 0) : RDrev (deployedRuntime v) g s0 := by
    have rd := morphoBlocks.morpho_block_11752_taken (immWords := wordsOf (immStore v))
      (by omega) hc (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
    exact morphoBlocks.morpho_block_712 (immWords := wordsOf (immStore v))
      (by change R.length + 3 + 2 ≤ 1024; omega) rd
  by_cases hh : ee.calldata.size < 2 ^ 255
  swap
  · refine .inl ⟨fun hb => hh hb.1, hbad ?_⟩
    rw [slt_zero_low_high hlow (by rw [UInt256.toNat_ofNat_of_lt hsize]; omega)]
    decide
  by_cases hr : start.toNat + 32 ≤ ee.calldata.size
  swap
  · refine .inl ⟨fun hb => hr hb.2.1, hbad ?_⟩
    rw [slt_lit_zero hh (by rw [h31]; omega) hlow]
    decide
  have rd0 := morphoBlocks.morpho_block_11752_fallthrough (immWords := wordsOf (immStore v))
    (by omega) (by rw [slt_lit_one_low hh (by rw [h31]; omega)]; rfl) h
  change RD _ _ _ _ _ (ret :: UInt256.ofNat ee.calldata.size :: start :: R) _ _ _ _ _ _ at rd0
  let len := calldataWord ee.calldata start.toNat
  by_cases hn : len.toNat ≤ solcMaxU64
  swap
  · have rd := morphoBlocks.morpho_block_11765_taken (immWords := wordsOf (immStore v))
      (by omega) (by
        change UInt256.gt len (UInt256.ofNat solcMaxU64) ≠ UInt256.ofNat 0
        rw [ugt_one (by change solcMaxU64 < len.toNat; omega)]; decide)
      (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd0
    exact .inl ⟨fun hb => hn hb.2.2.1,
      morphoBlocks.morpho_block_712 (immWords := wordsOf (immStore v))
        (by change R.length + 4 + 2 ≤ 1024; omega) rd⟩
  have rd1 := morphoBlocks.morpho_block_11765_fallthrough (immWords := wordsOf (immStore v))
    (by omega) (ugt_zero hn) rd0
  change RD _ _ _ _ _ (UInt256.ofNat ee.calldata.size :: ret :: len :: start :: R) _ _ _ _ _ _ at rd1
  have hend : ((start + len) + UInt256.ofNat 32).toNat = start.toNat + len.toNat + 32 := by
    have hb : start.toNat + len.toNat + 32 < UInt256.size := by
      norm_num [solcMaxU64, UInt256.size] at hn ⊢; omega
    have hs : (start + len).toNat = start.toNat + len.toNat := addWord_toNat start len (by omega)
    rw [uadd_word_ofNat_toNat (start + len) 32 (by rw [hs]; exact hb), hs]
  by_cases hp : start.toNat + 32 + len.toNat ≤ ee.calldata.size
  swap
  · have rd := morphoBlocks.morpho_block_11783_taken (immWords := wordsOf (immStore v))
      (by omega) (by rw [ugt_one (by rw [hend, UInt256.toNat_ofNat_of_lt hsize]; omega)]; decide)
      (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd1
    exact .inl ⟨fun hb => hp hb.2.2.2,
      morphoBlocks.morpho_block_712 (immWords := wordsOf (immStore v))
        (by change R.length + 3 + 2 ≤ 1024; omega) rd⟩
  have rd2 := morphoBlocks.morpho_block_11783_fallthrough (immWords := wordsOf (immStore v))
    (by omega) (ugt_zero (by rw [hend, UInt256.toNat_ofNat_of_lt hsize]; omega)) rd1
  have rd3 := morphoBlocks.morpho_block_11797 (immWords := wordsOf (immStore v))
    (by change R.length + 2 + 1 ≤ 1024; omega) hvalid rd2
  exact .inr ⟨hh, ⟨hr, hn, hp⟩, _, _, rd3⟩

end Benchmarks.Morpho.MorphoBlue
