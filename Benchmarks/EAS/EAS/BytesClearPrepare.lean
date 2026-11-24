import Benchmarks.EAS.EAS.BytesCleanDispatch
import Benchmarks.EAS.EAS.BytesClearLoop
import Benchmarks.EAS.EAS.BytesWriteArithmetic
import Benchmarks.EAS.EAS.BytesDataHash

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS

def bytesClearLoopSaved (site : UIDSite) (word src t1 t2 t3 t4 : UInt256) (R : List UInt256) : List UInt256 :=
  match site with
  | .single .. => recordBytesSaved site word src t1 t2 t3 t4 R
  | .many s1 s2 s3 s4 s5 s6 => s6::word::t2::src::t1::s5::t4::s1::s2::s3::s4::t3::R

set_option maxRecDepth 10000 in
theorem easBytesClearPrepare {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {src dataPtr slot word len old t1 t2 t3 t4 : UInt256} {R : List UInt256}
    (v : EASImmutables) (site : UIDSite) (hstack : R.length+24 ≤ 1024) (hb : len.toNat+31 < UInt256.size)
    (rd : RD fork (deployedRuntime v) ee g s0 (bytesClearSetupPC site)
      (old::dataPtr::len::slot::bytesClearSetupSaved site word src t1 t2 t3 t4 R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 (bytesClearPC site)
      (⟨0⟩::solidityBytesDataBaseSlot (slot+⟨6⟩)::UInt256.ofNat (bytesFirstClear len.toNat)::old::dataPtr::len::slot::
        bytesClearLoopSaved site word src t1 t2 t3 t4 R)
      (Reasoning.Theory.writeWord mem 0 (slot+⟨6⟩)) aw' rdata σ k' C' := by
  have hh : keccakWord (UInt256.ofNat 0) (UInt256.ofNat 32)
      ((slot+UInt256.ofNat 6).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) = solidityBytesDataBaseSlot (slot+⟨6⟩) :=
    (bytesDataHash (slot+UInt256.ofNat 6) mem).trans
      (congrArg solidityBytesDataBaseSlot (show slot+UInt256.ofNat 6 = slot+⟨6⟩ from rfl))
  have hn := bytesWordCount_word len hb
  by_cases hs : len.toNat < 32
  · have hc : UInt256.lt len (UInt256.ofNat 32) ≠ ⟨0⟩ := by rw [ult_one hs]; decide
    cases site with
    | single s1 s2 s3 s4 s5 s6 s7 s8 =>
      have hr1 := easBlocks.eas_block_9568_taken (immWords := wordsOf (immStore v))
        (by simp only [bytesClearSetupSaved,recordBytesSaved,List.length_cons]; omega) hc
        (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
      simp only [easBlocks.eas_block_9568_taken_stack,bytesClearSetupSaved,recordBytesSaved] at hr1
      have hr2 := easBlocks.eas_block_9638 (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) hr1
      simp only [easBlocks.eas_block_9638_stack] at hr2
      obtain ⟨aw',k',C',hr3⟩ := easBlocks.eas_block_9596_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) hr2
      refine ⟨aw',k',C',?_⟩
      simpa only [easBlocks.eas_block_9596_stack,easBlocks.eas_block_9638_stack,
        easBlocks.eas_block_9568_taken_stack,easBlocks.eas_block_9568_taken_memory,
        bytesClearPC,bytesClearLoopSaved,bytesFirstClear,if_pos hs,hh] using hr3
    | many s1 s2 s3 s4 s5 s6 =>
      have hr1 := easBlocks.eas_block_11818_taken (immWords := wordsOf (immStore v))
        (by omega) hc (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
      simp only [easBlocks.eas_block_11818_taken_stack] at hr1
      have hr2 := easBlocks.eas_block_11903 (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) hr1
      simp only [easBlocks.eas_block_11903_stack] at hr2
      obtain ⟨aw',k',C',hr3⟩ := easBlocks.eas_block_11854_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) hr2
      refine ⟨aw',k',C',?_⟩
      simpa only [easBlocks.eas_block_11854_stack,easBlocks.eas_block_11903_stack,
        easBlocks.eas_block_11818_taken_stack,easBlocks.eas_block_11818_taken_memory,
        bytesClearPC,bytesClearLoopSaved,bytesFirstClear,if_pos hs,hh] using hr3
  · have hc : UInt256.lt len (UInt256.ofNat 32) = ⟨0⟩ := ult_zero (by change 32 ≤ len.toNat; omega)
    cases site with
    | single s1 s2 s3 s4 s5 s6 s7 s8 =>
      have hr1 := easBlocks.eas_block_9568_fallthrough (immWords := wordsOf (immStore v))
        (by simp only [bytesClearSetupSaved,recordBytesSaved,List.length_cons]; omega) hc rd
      simp only [easBlocks.eas_block_9568_fallthrough_stack,bytesClearSetupSaved,recordBytesSaved] at hr1
      obtain ⟨aw',k',C',hr2⟩ := easBlocks.eas_block_9596_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) hr1
      refine ⟨aw',k',C',?_⟩
      simpa only [easBlocks.eas_block_9596_stack,easBlocks.eas_block_9568_fallthrough_stack,
        easBlocks.eas_block_9568_fallthrough_memory,bytesClearPC,bytesClearLoopSaved,
        bytesFirstClear,if_neg hs,hh,hn] using hr2
    | many s1 s2 s3 s4 s5 s6 =>
      have hr1 := easBlocks.eas_block_11818_fallthrough (immWords := wordsOf (immStore v))
        (by omega) hc rd
      simp only [easBlocks.eas_block_11818_fallthrough_stack] at hr1
      obtain ⟨aw',k',C',hr2⟩ := easBlocks.eas_block_11854_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) hr1
      refine ⟨aw',k',C',?_⟩
      simpa only [easBlocks.eas_block_11854_stack,easBlocks.eas_block_11818_fallthrough_stack,
        easBlocks.eas_block_11818_fallthrough_memory,bytesClearPC,bytesClearLoopSaved,
        bytesFirstClear,if_neg hs,hh,hn] using hr2

set_option maxRecDepth 10000 in
theorem easBytesClearFinish {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {src dataPtr slot word len old base first idx t1 t2 t3 t4 : UInt256} {R : List UInt256}
    (v : EASImmutables) (site : UIDSite) (hstack : R.length+24 ≤ 1024)
    (rd : RD fork (deployedRuntime v) ee g s0 (bytesClearEndPC site)
      (idx::base::first::old::dataPtr::len::slot::bytesClearLoopSaved site word src t1 t2 t3 t4 R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 (recordBytesCleanPC site)
      (old::dataPtr::len::slot::recordBytesSaved site word src t1 t2 t3 t4 R) mem aw' rdata σ k' C' := by
  cases site with
  | single s1 s2 s3 s4 s5 s6 s7 s8 =>
    exact easBlocks.eas_block_9615_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons,recordBytesSaved]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
  | many s1 s2 s3 s4 s5 s6 =>
    have hr := easBlocks.eas_block_11873 (immWords := wordsOf (immStore v))
      (by omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    exact easBlocks.eas_block_11806_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) hr

end Benchmarks.EAS.EAS
