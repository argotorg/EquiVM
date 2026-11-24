import Benchmarks.EAS.EAS.SchemaHead

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem easSchemaTextHead {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {src off ending : UInt256} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length+5 ≤ 1024)
    (hsrc : src.toNat+off.toNat+31 < 2^255) (hend : ending.toNat < 2^255)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨7467⟩ (src::off::ending::R) mem aw out σ k C) :
    if src.toNat+off.toNat+32 ≤ ending.toNat then
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨7479⟩ ((src+off)::ending::R) mem aw' out σ k' C'
    else RDrev fork (deployedRuntime v) g s0 := by
  have hsum : (src+off).toNat = src.toNat+off.toNat := by
    rw [uadd_toNat, Nat.mod_eq_of_lt (by change src.toNat+off.toNat < 2^256; omega)]
  have hn : ((src+off)+UInt256.ofNat 31).toNat = src.toNat+off.toNat+31 := by
    rw [uadd_word_ofNat_toNat _ 31 (by rw [hsum]; change _ < 2^256; omega),hsum]
  have he : ending = UInt256.ofNat ending.toNat := (u256_ofNat_toNat ending).symm
  by_cases hh : src.toNat+off.toNat+32 ≤ ending.toNat
  · rw [if_pos hh]
    have hc : UInt256.isZero (UInt256.slt ((src+off)+UInt256.ofNat 31) ending) = ⟨0⟩ := by
      conv_lhs => rw [he]
      rw [slt_lit_one_low hend (by rw [hn]; omega)]
      rfl
    exact easBlocks.eas_block_7467_fallthrough_packed (immWords := wordsOf (immStore v)) hstack hc rd
  · rw [if_neg hh]
    have hc : UInt256.isZero (UInt256.slt ((src+off)+UInt256.ofNat 31) ending) ≠ ⟨0⟩ := by
      conv_lhs => rw [he]
      rw [slt_lit_zero hend (by rw [hn]; omega) (by rw [hn]; exact hsrc)]
      decide
    obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_7467_taken_packed (immWords := wordsOf (immStore v))
      hstack hc (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    exact easBlocks.eas_block_402 (immWords := wordsOf (immStore v))
      (by simp only [easBlocks.eas_block_7467_taken_stack,List.length_cons]; omega) rd1

end Benchmarks.EAS.EAS
