import Benchmarks.EAS.EAS.RefUIDSites
import Benchmarks.EAS.EAS.MappingHash

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS

set_option maxRecDepth 10000 in
theorem easRefUIDRead {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {uid word src t1 t2 t3 t4 : UInt256} {R : List UInt256}
    (v : EASImmutables) (site : UIDSite) (hstack : R.length+21 ≤ 1024)
    (rd : RD fork (deployedRuntime v) ee g s0 (refUIDReadPC site)
      (refUIDReadyStack site uid word src t1 t2 t3 t4 R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 (refUIDRequirePC site)
      (UInt256.isZero (UInt256.isZero (solcSlotWord σ ee (dbSlot uid)))::refUIDReadSaved site word src t1 t2 t3 t4 R)
      (twoWordHashMem uid ⟨1⟩ mem) aw' rdata σ k' C' := by
  cases site with
  | single s1 s2 s3 s4 s5 s6 s7 s8 =>
    obtain ⟨aw',k',C',hr⟩ := easBlocks.eas_block_9257_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    exact ⟨aw',k',C',by simpa only [easBlocks.eas_block_9257_stack,easBlocks.eas_block_9257_memory,mappingHash] using hr⟩
  | many s1 s2 s3 s4 s5 s6 =>
    obtain ⟨aw',k',C',hr⟩ := easBlocks.eas_block_11538_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    exact ⟨aw',k',C',by simpa only [easBlocks.eas_block_11538_stack,easBlocks.eas_block_11538_memory,mappingHash] using hr⟩

set_option maxRecDepth 10000 in
theorem easRefUIDRequire {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {value : UInt256} {R : List UInt256} (v : EASImmutables) (site : UIDSite)
    (hstack : R.length+2 ≤ 1024)
    (rd : RD fork (deployedRuntime v) ee g s0 (refUIDRequirePC site)
      (UInt256.isZero (UInt256.isZero value)::R) mem aw rdata σ k C) :
    if value = ⟨0⟩ then RDrev fork (deployedRuntime v) g s0 else
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 (refUIDRequireNextPC site) R mem aw' rdata σ k' C' := by
  by_cases hz : value = ⟨0⟩
  · rw [if_pos hz]
    have hc : UInt256.isZero (UInt256.isZero (UInt256.isZero value)) ≠ ⟨0⟩ := by rw [hz]; decide
    cases site with
    | single s1 s2 s3 s4 s5 s6 s7 s8 =>
      have hr := easBlocks.eas_block_9286_taken (immWords := wordsOf (immStore v)) hstack hc
        (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
      exact easBlocks.eas_block_9302 (immWords := wordsOf (immStore v)) hstack hr
    | many s1 s2 s3 s4 s5 s6 =>
      have hr := easBlocks.eas_block_11563_taken (immWords := wordsOf (immStore v)) hstack hc
        (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
      exact easBlocks.eas_block_9302 (immWords := wordsOf (immStore v)) hstack hr
  · rw [if_neg hz]
    have hc : UInt256.isZero (UInt256.isZero (UInt256.isZero value)) = ⟨0⟩ := by rw [isZero_eq_zero_of_ne hz]; decide
    cases site with
    | single s1 s2 s3 s4 s5 s6 s7 s8 =>
      exact easBlocks.eas_block_9286_fallthrough_packed (immWords := wordsOf (immStore v)) hstack hc rd
    | many s1 s2 s3 s4 s5 s6 =>
      exact easBlocks.eas_block_11563_fallthrough_packed (immWords := wordsOf (immStore v)) hstack hc rd

set_option maxRecDepth 10000 in
theorem easRefUIDFinish {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {word src t1 t2 t3 t4 : UInt256} {R : List UInt256}
    (v : EASImmutables) (site : UIDSite) (hstack : R.length+21 ≤ 1024)
    (rd : RD fork (deployedRuntime v) ee g s0 (refUIDRequireNextPC site)
      (refUIDReadSaved site word src t1 t2 t3 t4 R) mem aw rdata σ k C) :
    ∃ dummy aw' k' C', RD fork (deployedRuntime v) ee g s0 (refUIDReadyPC site)
      (refUIDReadyStack site dummy word src t1 t2 t3 t4 R) mem aw' rdata σ k' C' := by
  cases site with
  | single s1 s2 s3 s4 s5 s6 s7 s8 =>
    obtain ⟨aw',k',C',hr⟩ := easBlocks.eas_block_9292_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    exact ⟨_,aw',k',C',hr⟩
  | many s1 s2 s3 s4 s5 s6 =>
    obtain ⟨aw',k',C',hr⟩ := easBlocks.eas_block_11569_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    exact ⟨_,aw',k',C',hr⟩

end Benchmarks.EAS.EAS
