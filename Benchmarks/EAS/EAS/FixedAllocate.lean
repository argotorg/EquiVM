import Benchmarks.EAS.EAS.Allocate

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

inductive FixedAllocationSite where
  | bytes64 | bytes96 | bytes128 | bytes192 | bytes320

def FixedAllocationSite.size : FixedAllocationSite → Nat
  | .bytes64 => 64 | .bytes96 => 96 | .bytes128 => 128 | .bytes192 => 192 | .bytes320 => 320
def FixedAllocationSite.pc : FixedAllocationSite → UInt256
  | .bytes64 => ⟨4798⟩ | .bytes96 => ⟨4826⟩ | .bytes128 => ⟨4695⟩ | .bytes192 => ⟨4770⟩ | .bytes320 => ⟨4854⟩
def FixedAllocationSite.finish : FixedAllocationSite → UInt256
  | .bytes64 => ⟨4822⟩ | .bytes96 => ⟨4850⟩ | .bytes128 => ⟨4719⟩ | .bytes192 => ⟨4794⟩ | .bytes320 => ⟨4879⟩

theorem fixedAllocation_word (site : FixedAllocationSite) (heap : UInt256) :
    heap+UInt256.ofNat site.size = UInt256.ofNat (allocateNext heap.toNat site.size) := by
  have hm : UInt256.land (UInt256.ofNat site.size+⟨31⟩) (UInt256.lnot ⟨31⟩) = UInt256.ofNat site.size := by cases site <;> rfl
  have hs : (UInt256.ofNat site.size).toNat = site.size := by cases site <;> rfl
  simpa only [hm,hs] using allocateNext_word heap (UInt256.ofNat site.size)

theorem fixedAllocation_next (site : FixedAllocationSite) {heap : Nat} (hh : heap ≤ 2^64-1) :
    allocateNext heap site.size = heap+site.size := by
  have hm : allocateRounded site.size = site.size := by cases site <;> rfl
  have hs : site.size ≤ 320 := by cases site <;> decide
  unfold allocateNext
  rw [hm]
  apply Nat.mod_eq_of_lt
  change heap+site.size < 2^256
  omega

theorem easFixedAllocate_ok {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {heap ret : UInt256} {R : List UInt256} (v : EASImmutables) (site : FixedAllocationSite)
    (hstack : R.length+5 ≤ 1024)
    (hg : allocateNext heap.toNat site.size ≤ 2^64-1 ∧ heap.toNat ≤ allocateNext heap.toNat site.size)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 site.pc (heap::ret::R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ret R
      (Reasoning.Theory.writeWord mem 64 (UInt256.ofNat (allocateNext heap.toNat site.size))) aw' rdata σ k' C' := by
  have hm : UInt256.land (UInt256.ofNat site.size+⟨31⟩) (UInt256.lnot ⟨31⟩) = UInt256.ofNat site.size := by cases site <;> rfl
  have hs : (UInt256.ofNat site.size).toNat = site.size := by cases site <;> rfl
  have hc := allocateCheck_ok heap (UInt256.ofNat site.size) (by simpa only [hs] using hg)
  simp only [hm] at hc
  have hfirst : ∃ a j D, RD fork (deployedRuntime v) ee g s0 site.finish
      ((heap+UInt256.ofNat site.size)::ret::R) mem a rdata σ j D := by
    cases site with
    | bytes64 =>
      exact easBlocks.eas_block_4798_fallthrough_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) hc rd
    | bytes96 =>
      exact easBlocks.eas_block_4826_fallthrough_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) hc rd
    | bytes128 =>
      exact easBlocks.eas_block_4695_fallthrough_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) hc rd
    | bytes192 =>
      exact easBlocks.eas_block_4770_fallthrough_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) hc rd
    | bytes320 =>
      exact easBlocks.eas_block_4854_fallthrough_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) hc rd
  obtain ⟨a1,j1,D1,r1⟩ := hfirst
  have hlast : ∃ a j D, RD fork (deployedRuntime v) ee g s0 ret R
      (Reasoning.Theory.writeWord mem 64 (heap+UInt256.ofNat site.size)) a rdata σ j D := by
    cases site with
    | bytes64 =>
      exact easBlocks.eas_block_4822_packed (immWords := wordsOf (immStore v)) (by omega) hret r1
    | bytes96 =>
      exact easBlocks.eas_block_4850_packed (immWords := wordsOf (immStore v)) (by omega) hret r1
    | bytes128 =>
      exact easBlocks.eas_block_4719_packed (immWords := wordsOf (immStore v)) (by omega) hret r1
    | bytes192 =>
      exact easBlocks.eas_block_4794_packed (immWords := wordsOf (immStore v)) (by omega) hret r1
    | bytes320 =>
      exact easBlocks.eas_block_4879_packed (immWords := wordsOf (immStore v)) (by omega) hret r1
  simpa only [fixedAllocation_word] using hlast

theorem easFixedAllocate_revert {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {heap : UInt256} {R : List UInt256} (v : EASImmutables) (site : FixedAllocationSite)
    (hstack : R.length+4 ≤ 1024)
    (hg : ¬ (allocateNext heap.toNat site.size ≤ 2^64-1 ∧ heap.toNat ≤ allocateNext heap.toNat site.size))
    (rd : RD fork (deployedRuntime v) ee g s0 site.pc (heap::R) mem aw rdata σ k C) :
    RDrev fork (deployedRuntime v) g s0 := by
  have hm : UInt256.land (UInt256.ofNat site.size+⟨31⟩) (UInt256.lnot ⟨31⟩) = UInt256.ofNat site.size := by cases site <;> rfl
  have hs : (UInt256.ofNat site.size).toNat = site.size := by cases site <;> rfl
  have hc := allocateCheck_revert heap (UInt256.ofNat site.size) (by simpa only [hs] using hg)
  simp only [hm] at hc
  have hfirst : ∃ a j D, RD fork (deployedRuntime v) ee g s0 ⟨4723⟩
      ((heap+UInt256.ofNat site.size)::R) mem a rdata σ j D := by
    have hdest : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 4723) = true := by rw [easPatchedValidJumps v]; jump_dest
    cases site with
    | bytes64 =>
      exact easBlocks.eas_block_4798_taken_packed (immWords := wordsOf (immStore v)) hstack hc hdest rd
    | bytes96 =>
      exact easBlocks.eas_block_4826_taken_packed (immWords := wordsOf (immStore v)) hstack hc hdest rd
    | bytes128 =>
      exact easBlocks.eas_block_4695_taken_packed (immWords := wordsOf (immStore v)) hstack hc hdest rd
    | bytes192 =>
      exact easBlocks.eas_block_4770_taken_packed (immWords := wordsOf (immStore v)) hstack hc hdest rd
    | bytes320 =>
      exact easBlocks.eas_block_4854_taken_packed (immWords := wordsOf (immStore v)) hstack hc hdest rd
  obtain ⟨a1,j1,D1,r1⟩ := hfirst
  exact easBlocks.eas_block_4723 (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) r1

end Benchmarks.EAS.EAS
