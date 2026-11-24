import Benchmarks.EAS.EAS.RecordBytesEntry
import Benchmarks.EAS.EAS.RuntimeBlocks_033
import Benchmarks.EAS.EAS.RuntimeBlocks_037
import Reasoning.StorageLoops

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS

def bytesClearPC : UIDSite → UInt256
  | .single .. => UInt256.ofNat 9599
  | .many .. => UInt256.ofNat 11857
def bytesClearEndPC : UIDSite → UInt256
  | .single .. => UInt256.ofNat 9615
  | .many .. => UInt256.ofNat 11873
def bytesClearLimit (old first : UInt256) : UInt256 :=
  UInt256.sub (UInt256.shiftRight (old+UInt256.ofNat 31) (UInt256.ofNat 5)) first

set_option maxRecDepth 10000 in
theorem easBytesClearStep {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {idx base first old : UInt256} {R : List UInt256} (v : EASImmutables) (site : UIDSite)
    (hstack : R.length+7 ≤ 1024) (hp : ee.perm = true)
    (hc : UInt256.lt idx (bytesClearLimit old first) ≠ ⟨0⟩)
    (rd : RD fork (deployedRuntime v) ee g s0 (bytesClearPC site) (idx::base::first::old::R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 (bytesClearPC site)
      (((⟨1⟩ : UInt256)+idx)::base::first::old::R) mem aw' rdata
      (sstoreAccountMap ee.codeOwner σ ((base+first)+idx) ⟨0⟩) k' C' := by
  have hslot : idx+(first+base) = (base+first)+idx := by
    rw [u256_add_comm idx,u256_add_comm first base]
  cases site with
  | single s1 s2 s3 s4 s5 s6 s7 s8 =>
    have hr1 := easBlocks.eas_block_9599_taken (immWords := wordsOf (immStore v)) hstack hc
      (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    obtain ⟨aw',k',C',hr2⟩ := easBlocks.eas_block_9622_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) hp (by rw [easPatchedValidJumpsRuntime v]; jump_dest) hr1
    exact ⟨aw',k',C',by simpa only [easBlocks.eas_block_9622_stack,hslot,bytesClearPC] using hr2⟩
  | many s1 s2 s3 s4 s5 s6 =>
    have hr1 := easBlocks.eas_block_11857_taken (immWords := wordsOf (immStore v)) hstack hc
      (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    obtain ⟨aw',k',C',hr2⟩ := easBlocks.eas_block_11887_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) hp (by rw [easPatchedValidJumpsRuntime v]; jump_dest) hr1
    exact ⟨aw',k',C',by simpa only [easBlocks.eas_block_11887_stack,hslot,bytesClearPC] using hr2⟩

theorem easBytesClearDone {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {idx base first old : UInt256} {R : List UInt256} (v : EASImmutables) (site : UIDSite)
    (hstack : R.length+7 ≤ 1024) (hc : UInt256.lt idx (bytesClearLimit old first) = ⟨0⟩)
    (rd : RD fork (deployedRuntime v) ee g s0 (bytesClearPC site) (idx::base::first::old::R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 (bytesClearEndPC site)
      (idx::base::first::old::R) mem aw' rdata σ k' C' := by
  cases site with
  | single s1 s2 s3 s4 s5 s6 s7 s8 =>
    exact easBlocks.eas_block_9599_fallthrough_packed (immWords := wordsOf (immStore v)) hstack hc rd
  | many s1 s2 s3 s4 s5 s6 =>
    exact easBlocks.eas_block_11857_fallthrough_packed (immWords := wordsOf (immStore v)) hstack hc rd

theorem easBytesClearLoop {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {base first old : UInt256} {R : List UInt256} (v : EASImmutables) (site : UIDSite)
    (hstack : R.length+7 ≤ 1024) (hp : ee.perm = true) (idx fuel : Nat)
    (hbound : (bytesClearLimit old first).toNat = idx+fuel)
    (rd : RD fork (deployedRuntime v) ee g s0 (bytesClearPC site)
      (UInt256.ofNat idx::base::first::old::R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 (bytesClearEndPC site)
      (bytesClearLimit old first::base::first::old::R) mem aw' rdata
      (clearDataWordsForwardFrom ee.codeOwner σ (base+first) (UInt256.ofNat idx) fuel) k' C' := by
  induction fuel generalizing idx aw σ k C with
  | zero =>
    have he : UInt256.ofNat idx = bytesClearLimit old first := by
      rw [← show (bytesClearLimit old first).toNat = idx from by omega,u256_ofNat_toNat]
    simp only [he] at rd
    exact easBytesClearDone v site hstack (ult_zero (le_refl _)) rd
  | succ fuel ih =>
    have hi : idx < UInt256.size := by have hb := (bytesClearLimit old first).val.isLt; change (bytesClearLimit old first).toNat < UInt256.size at hb; omega
    have hc : UInt256.lt (UInt256.ofNat idx) (bytesClearLimit old first) ≠ ⟨0⟩ := by
      rw [ult_one (by rw [ulit_toNat' _ hi,hbound]; omega)]
      decide
    obtain ⟨aw1,k1,C1,hr⟩ := easBytesClearStep v site hstack hp hc rd
    rw [u256_one_add_ofNat] at hr
    have hr' := ih (idx+1) (by omega) hr
    simpa only [clearDataWordsForwardFrom,u256_one_add_ofNat] using hr'

end Benchmarks.EAS.EAS
