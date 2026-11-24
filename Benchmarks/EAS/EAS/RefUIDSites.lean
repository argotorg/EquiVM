import Benchmarks.EAS.EAS.BytesWriteDispatch

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS

def refUIDPtr (site : UIDSite) (t3 : UInt256) : UInt256 :=
  match site with
  | .single .. => t3
  | .many _ _ _ _ _ s6 => s6

def refUIDReadyPC : UIDSite → UInt256
  | .single .. => UInt256.ofNat 9099
  | .many .. => UInt256.ofNat 11378

def refUIDReadPC : UIDSite → UInt256
  | .single .. => UInt256.ofNat 9257
  | .many .. => UInt256.ofNat 11538

def refUIDRequirePC : UIDSite → UInt256
  | .single .. => UInt256.ofNat 9286
  | .many .. => UInt256.ofNat 11563

def refUIDRequireNextPC : UIDSite → UInt256
  | .single .. => UInt256.ofNat 9292
  | .many .. => UInt256.ofNat 11569

def refUIDReadyStack (site : UIDSite) (dummy word src t1 t2 t3 t4 : UInt256) (R : List UInt256) : List UInt256 :=
  match site with
  | .single _ _ _ _ _ s6 s7 _ =>
      dummy::t4::s6::s7::bytesWriteSaved site word src t1 t2 t3 t4 R
  | .many .. => dummy::bytesWriteSaved site word src t1 t2 t3 t4 R

def refUIDReadSaved (site : UIDSite) (word src t1 t2 t3 t4 : UInt256) (R : List UInt256) : List UInt256 :=
  match site with
  | .single s1 s2 s3 s4 s5 s6 s7 s8 => word::t3::t2::src::s5::s8::t1::s1::s2::t4::s6::s3::s7::s4::R
  | .many s1 s2 s3 s4 s5 s6 => word::s6::t2::src::t1::s5::t3::t4::s1::s2::s3::s4::R

set_option maxRecDepth 10000 in
theorem easRefUIDDispatch {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {uid word src t1 t2 t3 t4 : UInt256} {R : List UInt256}
    (v : EASImmutables) (site : UIDSite) (hstack : R.length+21 ≤ 1024)
    (hload : memLoad (refUIDPtr site t3+UInt256.ofNat 96) mem = uid)
    (rd : RD fork (deployedRuntime v) ee g s0 (bytesWrittenPC site)
      (bytesWriteSaved site word src t1 t2 t3 t4 R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0
      (if uid = ⟨0⟩ then refUIDReadyPC site else refUIDReadPC site)
      (refUIDReadyStack site uid word src t1 t2 t3 t4 R) mem aw' rdata σ k' C' := by
  by_cases hz : uid = ⟨0⟩
  · rw [if_pos hz]
    cases site with
    | single s1 s2 s3 s4 s5 s6 s7 s8 =>
      obtain ⟨aw',k',C',hr⟩ := easBlocks.eas_block_9085_fallthrough_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) (hload.trans hz) rd
      exact ⟨aw',k',C',by simpa only [easBlocks.eas_block_9085_fallthrough_stack,← hload] using hr⟩
    | many s1 s2 s3 s4 s5 s6 =>
      obtain ⟨aw',k',C',hr⟩ := easBlocks.eas_block_11367_fallthrough_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) (hload.trans hz) rd
      exact ⟨aw',k',C',by simpa only [easBlocks.eas_block_11367_fallthrough_stack,← hload] using hr⟩
  · rw [if_neg hz]
    cases site with
    | single s1 s2 s3 s4 s5 s6 s7 s8 =>
      obtain ⟨aw',k',C',hr⟩ := easBlocks.eas_block_9085_taken_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) (fun h => hz (hload.symm.trans h))
        (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
      exact ⟨aw',k',C',by simpa only [easBlocks.eas_block_9085_taken_stack,← hload] using hr⟩
    | many s1 s2 s3 s4 s5 s6 =>
      obtain ⟨aw',k',C',hr⟩ := easBlocks.eas_block_11367_taken_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) (fun h => hz (hload.symm.trans h))
        (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
      exact ⟨aw',k',C',by simpa only [easBlocks.eas_block_11367_taken_stack,← hload] using hr⟩

end Benchmarks.EAS.EAS
