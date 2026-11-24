import Benchmarks.EAS.EAS.BytesLongControl

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS

def bytesLongHeaderPC : UIDSite → UInt256
  | .single .. => UInt256.ofNat 9463
  | .many .. => UInt256.ofNat 11695

def bytesLongTailEVMWord (payload len : UInt256) : UInt256 :=
  UInt256.land (UInt256.lnot (UInt256.shiftRight (UInt256.ofNat (2^256-1))
    (UInt256.land (UInt256.shiftLeft len (UInt256.ofNat 3)) (UInt256.ofNat 248)))) payload

set_option maxRecDepth 10000 in
theorem easBytesLongHeader {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {x0 x1 x2 len slot : UInt256} {R : List UInt256} (v : EASImmutables) (site : UIDSite)
    (hstack : R.length+7 ≤ 1024) (hp : ee.perm = true)
    (rd : RD fork (deployedRuntime v) ee g s0 (bytesLongHeaderPC site)
      (x0::x1::x2::len::UInt256.ofNat 1::UInt256.ofNat 6::slot::R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 (bytesWrittenPC site) R mem aw' rdata
      (sstoreAccountMap ee.codeOwner σ (slot+⟨6⟩) (UInt256.shiftLeft len (UInt256.ofNat 1)+⟨1⟩)) k' C' := by
  cases site with
  | single s1 s2 s3 s4 s5 s6 s7 s8 =>
    exact easBlocks.eas_block_9463_packed (immWords := wordsOf (immStore v)) hstack hp
      (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
  | many s1 s2 s3 s4 s5 s6 =>
    exact easBlocks.eas_block_11695_packed (immWords := wordsOf (immStore v)) hstack hp
      (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd

set_option maxRecDepth 10000 in
theorem easBytesLongTail {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {idx ptr stride dst len slot : UInt256} {R : List UInt256} (v : EASImmutables) (site : UIDSite)
    (hstack : R.length+10 ≤ 1024) (hp : ee.perm = true)
    (rd : RD fork (deployedRuntime v) ee g s0 (bytesLongTailPC site)
      (idx::ptr::stride::dst::len::slot::R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 (bytesWrittenPC site) R mem aw' rdata
      (sstoreAccountMap ee.codeOwner
        (if len.toNat%32=0 then σ else sstoreAccountMap ee.codeOwner σ dst
          (bytesLongTailEVMWord (memLoad (ptr+stride) mem) len))
        (slot+⟨6⟩) (UInt256.shiftLeft len (UInt256.ofNat 1)+⟨1⟩)) k' C' := by
  by_cases hz : len.toNat%32=0
  · rw [if_pos hz]
    have hc := longDataNoTail len hz
    cases site with
    | single s1 s2 s3 s4 s5 s6 s7 s8 =>
      have hr := easBlocks.eas_block_9413_fallthrough (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) hc rd
      exact easBytesLongHeader v (.single s1 s2 s3 s4 s5 s6 s7 s8) (by omega) hp hr
    | many s1 s2 s3 s4 s5 s6 =>
      have hr := easBlocks.eas_block_11645_fallthrough (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) hc rd
      exact easBytesLongHeader v (.many s1 s2 s3 s4 s5 s6) (by omega) hp hr
  · rw [if_neg hz]
    have hc : UInt256.lt (UInt256.land len (UInt256.lnot ⟨31⟩)) len ≠ ⟨0⟩ := by
      intro he
      have h := longDataTail len hz
      rw [he] at h
      contradiction
    cases site with
    | single s1 s2 s3 s4 s5 s6 s7 s8 =>
      have hr1 := easBlocks.eas_block_9413_taken (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) hc (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
      obtain ⟨aw',k',C',hr2⟩ := easBlocks.eas_block_9477_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) hp (by rw [easPatchedValidJumpsRuntime v]; jump_dest) hr1
      exact easBytesLongHeader v (.single s1 s2 s3 s4 s5 s6 s7 s8) (by omega) hp hr2
    | many s1 s2 s3 s4 s5 s6 =>
      have hr1 := easBlocks.eas_block_11645_taken (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) hc (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
      obtain ⟨aw',k',C',hr2⟩ := easBlocks.eas_block_11709_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) hp (by rw [easPatchedValidJumpsRuntime v]; jump_dest) hr1
      exact easBytesLongHeader v (.many s1 s2 s3 s4 s5 s6) (by omega) hp hr2

end Benchmarks.EAS.EAS
