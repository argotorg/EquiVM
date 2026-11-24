import Benchmarks.EAS.EAS.BytesShortEVM
import Benchmarks.EAS.EAS.BytesDataHash

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS

def bytesLongLoopPC : UIDSite → UInt256
  | .single .. => UInt256.ofNat 9371
  | .many .. => UInt256.ofNat 11603
def bytesLongTailPC : UIDSite → UInt256
  | .single .. => UInt256.ofNat 9413
  | .many .. => UInt256.ofNat 11645

theorem easBytesLongPrepare {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {ptr len slot : UInt256} {R : List UInt256} (v : EASImmutables) (site : UIDSite)
    (hstack : R.length+8 ≤ 1024)
    (rd : RD fork (deployedRuntime v) ee g s0 (bytesLongPC site)
      (ptr::UInt256.ofNat 32::len::slot::R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 (bytesLongLoopPC site)
      (⟨0⟩::ptr::UInt256.ofNat 32::solidityBytesDataBaseSlot (slot+⟨6⟩)::len::slot::R)
      (Reasoning.Theory.writeWord mem 0 (slot+⟨6⟩)) aw' rdata σ k' C' := by
  have hh : keccakWord (UInt256.ofNat 0) (UInt256.ofNat 32)
      ((slot+UInt256.ofNat 6).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) = solidityBytesDataBaseSlot (slot+⟨6⟩) :=
    (bytesDataHash (slot+UInt256.ofNat 6) mem).trans
      (congrArg solidityBytesDataBaseSlot (show slot+UInt256.ofNat 6 = slot+⟨6⟩ from rfl))
  cases site with
  | single s1 s2 s3 s4 s5 s6 s7 s8 =>
    obtain ⟨aw',k',C',hr⟩ := easBlocks.eas_block_9355_packed (immWords := wordsOf (immStore v)) (by omega) rd
    exact ⟨aw',k',C',by simpa only [bytesLongLoopPC,easBlocks.eas_block_9355_stack,easBlocks.eas_block_9355_memory,hh] using hr⟩
  | many s1 s2 s3 s4 s5 s6 =>
    obtain ⟨aw',k',C',hr⟩ := easBlocks.eas_block_11587_packed (immWords := wordsOf (immStore v)) (by omega) rd
    exact ⟨aw',k',C',by simpa only [bytesLongLoopPC,easBlocks.eas_block_11587_stack,easBlocks.eas_block_11587_memory,hh] using hr⟩

set_option maxRecDepth 10000 in
theorem easBytesLongStep {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {idx ptr stride dst len slot word src t1 t2 t3 t4 : UInt256} {R : List UInt256}
    (v : EASImmutables) (site : UIDSite) (hstack : R.length+24 ≤ 1024) (hp : ee.perm = true)
    (hc : UInt256.lt idx (UInt256.land len (UInt256.ofNat (2^256-32))) ≠ ⟨0⟩)
    (rd : RD fork (deployedRuntime v) ee g s0 (bytesLongLoopPC site)
      (idx::ptr::stride::dst::len::slot::bytesWriteSaved site word src t1 t2 t3 t4 R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 (bytesLongLoopPC site)
      ((UInt256.ofNat 32+idx)::ptr::(UInt256.ofNat 32+stride)::(dst+UInt256.ofNat 1)::len::slot::
        bytesWriteSaved site word src t1 t2 t3 t4 R) mem aw' rdata
      (sstoreAccountMap ee.codeOwner σ dst (memLoad (stride+ptr) mem)) k' C' := by
  cases site with
  | single s1 s2 s3 s4 s5 s6 s7 s8 =>
    have hr1 := easBlocks.eas_block_9371_taken (immWords := wordsOf (immStore v))
      (by simp only [bytesWriteSaved,List.length_cons]; omega) hc (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    exact easBlocks.eas_block_9532_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) hp (by rw [easPatchedValidJumpsRuntime v]; jump_dest) hr1
  | many s1 s2 s3 s4 s5 s6 =>
    have hr1 := easBlocks.eas_block_11603_taken (immWords := wordsOf (immStore v))
      (by simp only [bytesWriteSaved,recordBytesSaved,List.length_cons]; omega) hc (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    exact easBlocks.eas_block_11764_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) hp (by rw [easPatchedValidJumpsRuntime v]; jump_dest) hr1

theorem easBytesLongDone {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {idx ptr stride dst len : UInt256} {R : List UInt256} (v : EASImmutables) (site : UIDSite)
    (hstack : R.length+7 ≤ 1024) (hc : UInt256.lt idx (UInt256.land len (UInt256.ofNat (2^256-32))) = ⟨0⟩)
    (rd : RD fork (deployedRuntime v) ee g s0 (bytesLongLoopPC site)
      (idx::ptr::stride::dst::len::R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 (bytesLongTailPC site)
      (idx::ptr::stride::dst::len::R) mem aw' rdata σ k' C' := by
  cases site with
  | single s1 s2 s3 s4 s5 s6 s7 s8 =>
    exact easBlocks.eas_block_9371_fallthrough_packed (immWords := wordsOf (immStore v)) hstack hc rd
  | many s1 s2 s3 s4 s5 s6 =>
    exact easBlocks.eas_block_11603_fallthrough_packed (immWords := wordsOf (immStore v)) hstack hc rd

end Benchmarks.EAS.EAS
