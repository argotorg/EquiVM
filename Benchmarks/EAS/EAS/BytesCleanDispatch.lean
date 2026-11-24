import Benchmarks.EAS.EAS.RecordBytesEntry
import Benchmarks.EAS.EAS.RuntimeBlocks_032
import Benchmarks.EAS.EAS.RuntimeBlocks_037

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS

def recordBytesCleanPC : UIDSite → UInt256
  | .single .. => UInt256.ofNat 8997
  | .many .. => UInt256.ofNat 11288
def bytesClearSetupPC : UIDSite → UInt256
  | .single .. => UInt256.ofNat 9568
  | .many .. => UInt256.ofNat 11818
def bytesClearSetupSaved (site : UIDSite) (word src t1 t2 t3 t4 : UInt256) (R : List UInt256) : List UInt256 :=
  match site with
  | .single .. => recordBytesSaved site word src t1 t2 t3 t4 R
  | .many s1 s2 s3 s4 s5 s6 => s6::word::t2::src::t1::s5::t3::t4::s1::s2::s3::s4::R

set_option maxRecDepth 10000 in
theorem easBytesCleanDispatch {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {src dataPtr slot word len old t1 t2 t3 t4 : UInt256} {R : List UInt256}
    (v : EASImmutables) (site : UIDSite) (hstack : R.length+24 ≤ 1024)
    (rd : RD fork (deployedRuntime v) ee g s0 (recordBytesDecodedPC site)
      (old::dataPtr::len::slot::recordBytesSaved site word src t1 t2 t3 t4 R) mem aw rdata σ k C) :
    if old.toNat < 32 ∨ old.toNat ≤ len.toNat then
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 (recordBytesCleanPC site)
        (old::dataPtr::len::slot::recordBytesSaved site word src t1 t2 t3 t4 R) mem aw' rdata σ k' C'
    else
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 (bytesClearSetupPC site)
        (old::dataPtr::len::slot::bytesClearSetupSaved site word src t1 t2 t3 t4 R) mem aw' rdata σ k' C' := by
  by_cases ho : old.toNat < 32
  · rw [if_pos (Or.inl ho)]
    have hc : UInt256.gt old (UInt256.ofNat 31) = ⟨0⟩ := ugt_zero (by change old.toNat ≤ 31; omega)
    cases site with
    | single s1 s2 s3 s4 s5 s6 s7 s8 =>
      exact easBlocks.eas_block_8988_fallthrough_packed (immWords := wordsOf (immStore v))
        (by simp only [recordBytesSaved,List.length_cons]; omega) hc rd
    | many s1 s2 s3 s4 s5 s6 =>
      exact easBlocks.eas_block_11279_fallthrough_packed (immWords := wordsOf (immStore v))
        (by simp only [recordBytesSaved,List.length_cons]; omega) hc rd
  · have hc : UInt256.gt old (UInt256.ofNat 31) ≠ ⟨0⟩ := by
      rw [ugt_one (by change 31 < old.toNat; omega)]
      decide
    by_cases hn : old.toNat ≤ len.toNat
    · rw [if_pos (Or.inr hn)]
      have hz : UInt256.gt old len = ⟨0⟩ := ugt_zero hn
      cases site with
      | single s1 s2 s3 s4 s5 s6 s7 s8 =>
        have hr1 := easBlocks.eas_block_8988_taken (immWords := wordsOf (immStore v))
          (by simp only [recordBytesSaved,List.length_cons]; omega) hc
          (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
        exact easBlocks.eas_block_9559_taken_packed (immWords := wordsOf (immStore v))
          (by simp only [recordBytesSaved,List.length_cons]; omega) (by rw [hz]; decide)
          (by rw [easPatchedValidJumpsRuntime v]; jump_dest) hr1
      | many s1 s2 s3 s4 s5 s6 =>
        have hr1 := easBlocks.eas_block_11279_taken (immWords := wordsOf (immStore v))
          (by simp only [recordBytesSaved,List.length_cons]; omega) hc
          (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
        have hr2 := easBlocks.eas_block_11791_fallthrough (immWords := wordsOf (immStore v))
          (by simp only [List.length_cons]; omega) hz hr1
        exact easBlocks.eas_block_11806_packed (immWords := wordsOf (immStore v))
          (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) hr2
    · rw [if_neg (fun h => h.elim ho hn)]
      have hz : UInt256.gt old len = ⟨1⟩ := ugt_one (by omega)
      cases site with
      | single s1 s2 s3 s4 s5 s6 s7 s8 =>
        have hr1 := easBlocks.eas_block_8988_taken (immWords := wordsOf (immStore v))
          (by simp only [recordBytesSaved,List.length_cons]; omega) hc
          (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
        exact easBlocks.eas_block_9559_fallthrough_packed (immWords := wordsOf (immStore v))
          (by simp only [bytesClearSetupSaved,recordBytesSaved,List.length_cons]; omega) (by rw [hz]; decide) hr1
      | many s1 s2 s3 s4 s5 s6 =>
        have hr1 := easBlocks.eas_block_11279_taken (immWords := wordsOf (immStore v))
          (by simp only [recordBytesSaved,List.length_cons]; omega) hc
          (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
        exact easBlocks.eas_block_11791_taken_packed (immWords := wordsOf (immStore v))
          (by simp only [List.length_cons]; omega) (by rw [hz]; decide)
          (by rw [easPatchedValidJumpsRuntime v]; jump_dest) hr1

end Benchmarks.EAS.EAS
