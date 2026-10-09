import Benchmarks.Morpho.MorphoBlue.ReturnData
import Reasoning.ABIComposite

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

theorem morphoReturnBoolDecodeOk {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem out rdata : ByteArray} {aw first last ret : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (hb : out.size < 2 ^ 255) (hv : BoolReturnValid out)
    (hspan : UInt256.sub last first = UInt256.ofNat out.size)
    (hword : memLoad first mem = calldataWord out 0) (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 14642)
      (first :: last :: ret :: R) mem aw rdata σ k C) :
    ABI.decodeReturnValue? abiBool out = some (.bool (decide (calldataWord out 0 ≠ ⟨0⟩))) ∧
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ret
      (calldataWord out 0 :: R) mem aw' rdata σ k' C' := by
  refine ⟨decodeReturnBool_valid hv hb, ?_⟩
  have rd1 := morphoBlocks.morpho_block_14642_fallthrough
    (immWords := wordsOf (immStore v)) (by change R.length + 1 + 4 ≤ 1024; omega)
    (by rw [hspan]; exact slt_ofNat_lit_zero (by decide) hv.1 hb) h
  obtain ⟨aw2, k2, C2, rd2⟩ := morphoBlocks.morpho_block_14654_fallthrough_packed
    (immWords := wordsOf (immStore v)) (by change R.length + 1 + 3 ≤ 1024; omega)
    (by rw [hword, (boolWordClean_iff _).mpr hv.2, u256_sub_self]; rfl) rd1
  obtain ⟨aw3, k3, C3, rd3⟩ := morphoBlocks.morpho_block_14664_packed
    (immWords := wordsOf (immStore v)) (by omega) hvalid rd2
  dsimp only [morphoBlocks.morpho_block_14664_stack,
    morphoBlocks.morpho_block_14654_fallthrough_stack] at rd3
  rw [hword] at rd3
  exact ⟨aw3, k3, C3, rd3⟩

theorem morphoReturnBoolDecodeRevert {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem out rdata : ByteArray} {aw first last ret : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (hb : out.size < 2 ^ 255) (hv : ¬ BoolReturnValid out)
    (hspan : UInt256.sub last first = UInt256.ofNat out.size)
    (hword : 32 ≤ out.size → memLoad first mem = calldataWord out 0)
    (hstack : R.length + 5 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 14642)
      (first :: last :: ret :: R) mem aw rdata σ k C) :
    ABI.decodeReturnValue? abiBool out = none ∧ RDrev (deployedRuntime v) g s0 := by
  refine ⟨decodeReturnBool_invalid hv hb, ?_⟩
  by_cases hl : 32 ≤ out.size
  · have rd1 := morphoBlocks.morpho_block_14642_fallthrough
      (immWords := wordsOf (immStore v)) (by change R.length + 1 + 4 ≤ 1024; omega)
      (by rw [hspan]; exact slt_ofNat_lit_zero (by decide) hl hb) h
    obtain ⟨aw2, k2, C2, rd2⟩ := morphoBlocks.morpho_block_14654_taken_packed
      (immWords := wordsOf (immStore v)) (by change R.length + 1 + 3 ≤ 1024; omega)
      (by rw [hword hl]; apply u256_sub_ne_zero_of_ne; intro he
          exact hv ⟨hl, (boolWordClean_iff _).mp he.symm⟩)
      (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd1
    exact morphoBlocks.morpho_block_712 (immWords := wordsOf (immStore v))
      (by change R.length + 2 + 2 ≤ 1024; omega) rd2
  · have rd1 := morphoBlocks.morpho_block_14642_taken
      (immWords := wordsOf (immStore v)) (by change R.length + 1 + 4 ≤ 1024; omega)
      (by rw [hspan, slt_ofNat_lit_one_low (by decide) (by omega)]; decide)
      (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
    exact morphoBlocks.morpho_block_712 (immWords := wordsOf (immStore v))
      (by change R.length + 2 + 2 ≤ 1024; omega) rd1

end Benchmarks.Morpho.MorphoBlue
