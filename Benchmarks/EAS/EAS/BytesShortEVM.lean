import Benchmarks.EAS.EAS.BytesWriteDispatch

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS

def bytesShortStorePC : UIDSite → UInt256
  | .single .. => UInt256.ofNat 9034
  | .many .. => UInt256.ofNat 11316
def bytesShortEVMWord (payload len : UInt256) : UInt256 :=
  UInt256.lor (UInt256.land (UInt256.lnot (UInt256.shiftRight
    (UInt256.ofNat (2^256-1)) (UInt256.shiftLeft len (UInt256.ofNat 3)))) payload)
    (UInt256.shiftLeft len (UInt256.ofNat 1))

theorem easBytesShortStore {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {x0 x1 payload len slot : UInt256} {R : List UInt256} (v : EASImmutables) (site : UIDSite)
    (hstack : R.length+7 ≤ 1024) (hp : ee.perm = true)
    (rd : RD fork (deployedRuntime v) ee g s0 (bytesShortStorePC site)
      (x0::x1::payload::len::UInt256.ofNat 6::slot::R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 (bytesWrittenPC site) R mem aw' rdata
      (sstoreAccountMap ee.codeOwner σ (slot+⟨6⟩) (bytesShortEVMWord payload len)) k' C' := by
  cases site with
  | single s1 s2 s3 s4 s5 s6 s7 s8 =>
    exact easBlocks.eas_block_9034_packed (immWords := wordsOf (immStore v)) hstack hp rd
  | many s1 s2 s3 s4 s5 s6 =>
    exact easBlocks.eas_block_11316_packed (immWords := wordsOf (immStore v)) hstack hp rd

set_option maxRecDepth 10000 in
theorem easBytesShortData {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {ptr len slot : UInt256} {R : List UInt256} (v : EASImmutables) (site : UIDSite)
    (hstack : R.length+8 ≤ 1024)
    (rd : RD fork (deployedRuntime v) ee g s0 (bytesShortPC site)
      (ptr::UInt256.ofNat 32::len::slot::R) mem aw rdata σ k C) :
    ∃ x0 x1 aw' k' C', RD fork (deployedRuntime v) ee g s0 (bytesShortStorePC site)
      (x0::x1::(if len = ⟨0⟩ then ⟨0⟩ else memLoad (ptr+UInt256.ofNat 32) mem)::len::UInt256.ofNat 6::slot::R)
      mem aw' rdata σ k' C' := by
  by_cases hz : len = ⟨0⟩
  · rw [if_pos hz]
    cases site with
    | single s1 s2 s3 s4 s5 s6 s7 s8 =>
      obtain ⟨aw',k',C',hr⟩ := easBlocks.eas_block_9022_fallthrough_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) hz rd
      exact ⟨ptr,UInt256.ofNat 32,aw',k',C',hr⟩
    | many s1 s2 s3 s4 s5 s6 =>
      obtain ⟨aw',k',C',hr⟩ := easBlocks.eas_block_11304_fallthrough_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) hz rd
      exact ⟨ptr,UInt256.ofNat 32,aw',k',C',hr⟩
  · rw [if_neg hz]
    cases site with
    | single s1 s2 s3 s4 s5 s6 s7 s8 =>
      have hr1 := easBlocks.eas_block_9022_taken (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) hz (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
      obtain ⟨aw',k',C',hr2⟩ := easBlocks.eas_block_9344_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) hr1
      exact ⟨_,_,aw',k',C',hr2⟩
    | many s1 s2 s3 s4 s5 s6 =>
      have hr1 := easBlocks.eas_block_11304_taken (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) hz (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
      obtain ⟨aw',k',C',hr2⟩ := easBlocks.eas_block_11576_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) hr1
      exact ⟨_,_,aw',k',C',hr2⟩

theorem easBytesShortWrite {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {ptr len slot : UInt256} {R : List UInt256} (v : EASImmutables) (site : UIDSite)
    (hstack : R.length+8 ≤ 1024) (hp : ee.perm = true)
    (rd : RD fork (deployedRuntime v) ee g s0 (bytesShortPC site)
      (ptr::UInt256.ofNat 32::len::slot::R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 (bytesWrittenPC site) R mem aw' rdata
      (sstoreAccountMap ee.codeOwner σ (slot+⟨6⟩)
        (bytesShortEVMWord (if len = ⟨0⟩ then ⟨0⟩ else memLoad (ptr+UInt256.ofNat 32) mem) len)) k' C' := by
  obtain ⟨x0,x1,aw',k',C',hr⟩ := easBytesShortData v site hstack rd
  exact easBytesShortStore v site (by omega) hp hr

end Benchmarks.EAS.EAS
