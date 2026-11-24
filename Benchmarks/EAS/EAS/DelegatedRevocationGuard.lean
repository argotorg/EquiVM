import Benchmarks.EAS.EAS.DelegatedRevocationMemory
import Benchmarks.EAS.EAS.RuntimeBlocks_008
import Benchmarks.EAS.EAS.RuntimeBlocks_009

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem easDelegatedRevocationGuard {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {row data sig base n available last i tag : UInt256} {R : List UInt256}
    {r : DelegatedRevocationBatch} {heap : Nat}
    (v : EASImmutables) (hstack : R.length+16 ≤ 1024) (hh : heap < UInt256.size)
    (hv : DelegatedRevocationBatchMemoryView (delegatedRevocationSetRevoker mem row (UInt256.ofNat r.revoker.val)) row data sig r heap)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨1521⟩
      (UInt256.ofNat r.revoker.val::base::n::available::(row+UInt256.ofNat 32)::
        (row+UInt256.ofNat 64)::sig::last::row::i::tag::R) mem aw rdata σ k C) :
    if 0<r.data.length ∧ r.data.length=r.signatures.length then
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨1552⟩
        (⟨0⟩::base::n::available::(row+UInt256.ofNat 96)::(row+UInt256.ofNat 64)::data::last::row::i::tag::R)
        (delegatedRevocationSetRevoker mem row (UInt256.ofNat r.revoker.val)) aw' rdata σ k' C'
    else RDrev fork (deployedRuntime v) g s0 := by
  have hd := hv.data.span
  have hs := hv.signatures.span
  have hnd : (UInt256.ofNat r.data.length).toNat = r.data.length := ulit_toNat' _ (by omega)
  have hns : (UInt256.ofNat r.signatures.length).toNat = r.signatures.length := ulit_toNat' _ (by omega)
  have hread : memLoad (memLoad (row+UInt256.ofNat 32) (delegatedRevocationSetRevoker mem row (UInt256.ofNat r.revoker.val)))
      (delegatedRevocationSetRevoker mem row (UInt256.ofNat r.revoker.val)) = UInt256.ofNat r.data.length := by
    rw [hv.dataPointer,hv.data.length]
  have hraw : memLoad (memLoad (row+UInt256.ofNat 32)
      ((UInt256.ofNat r.revoker.val).toByteArray.write 0 mem (row+UInt256.ofNat 96).toNat 32))
      ((UInt256.ofNat r.revoker.val).toByteArray.write 0 mem (row+UInt256.ofNat 96).toNat 32) = UInt256.ofNat r.data.length := hread
  have hpraw : memLoad (row+UInt256.ofNat 32)
      ((UInt256.ofNat r.revoker.val).toByteArray.write 0 mem (row+UInt256.ofNat 96).toNat 32) = data := hv.dataPointer
  have hsraw : memLoad sig
      ((UInt256.ofNat r.revoker.val).toByteArray.write 0 mem (row+UInt256.ofNat 96).toNat 32) = UInt256.ofNat r.signatures.length := hv.signatures.length
  have hdraw : memLoad data
      ((UInt256.ofNat r.revoker.val).toByteArray.write 0 mem (row+UInt256.ofNat 96).toNat 32) = UInt256.ofNat r.data.length := hv.data.length
  by_cases hn : 0<r.data.length
  · have hz : UInt256.ofNat r.data.length ≠ (⟨0⟩ : UInt256) := by
      intro he
      have hnat := congrArg UInt256.toNat he
      rw [hnd] at hnat
      change r.data.length=0 at hnat
      omega
    obtain ⟨a1,j1,D1,r1⟩ := easBlocks.eas_block_1521_taken_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega)
      (by rw [hraw,isZero_eq_zero_of_ne hz]; decide)
      (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    obtain ⟨a2,j2,D2,r2⟩ := easBlocks.eas_block_1768_packed (immWords := wordsOf (immStore v))
      (by omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r1
    simp only [easBlocks.eas_block_1768_stack,easBlocks.eas_block_1521_taken_stack,
      easBlocks.eas_block_1521_taken_memory,hraw,hpraw,hsraw,hdraw] at r2
    by_cases he : r.data.length=r.signatures.length
    · rw [if_pos ⟨hn,he⟩]
      obtain ⟨a3,j3,D3,r3⟩ := easBlocks.eas_block_1543_fallthrough_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) (by rw [he,uInt256_eq_self]; rfl) r2
      exact easBlocks.eas_block_1550_packed (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) r3
    · rw [if_neg (fun h => he h.2)]
      have hne : UInt256.ofNat r.signatures.length ≠ UInt256.ofNat r.data.length := by
        intro hw
        have hnat := congrArg UInt256.toNat hw
        rw [hnd,hns] at hnat
        exact he hnat.symm
      obtain ⟨a3,j3,D3,r3⟩ := easBlocks.eas_block_1543_taken_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) (by rw [uInt256_eq_zero_of_ne (fun he => hne (uInt256_eq_one_eq he))]; decide)
        (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r2
      exact easBlocks.eas_block_1726 (immWords := wordsOf (immStore v))
        (by simp only [easBlocks.eas_block_1543_taken_stack,List.length_cons]; omega) r3
  · have hzero : r.data.length=0 := by omega
    rw [if_neg (fun h => hn h.1)]
    obtain ⟨a1,j1,D1,r1⟩ := easBlocks.eas_block_1521_fallthrough_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (by rw [hraw,hzero]; rfl) rd
    obtain ⟨a2,j2,D2,r2⟩ := easBlocks.eas_block_1543_taken_packed (immWords := wordsOf (immStore v))
      (by simp only [easBlocks.eas_block_1521_fallthrough_stack,List.length_cons]; omega)
      (by change UInt256.isZero (memLoad (memLoad (row+UInt256.ofNat 32)
          ((UInt256.ofNat r.revoker.val).toByteArray.write 0 mem (row+UInt256.ofNat 96).toNat 32))
          ((UInt256.ofNat r.revoker.val).toByteArray.write 0 mem (row+UInt256.ofNat 96).toNat 32)) ≠ ⟨0⟩
          rw [hraw,hzero]; decide)
      (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r1
    exact easBlocks.eas_block_1726 (immWords := wordsOf (immStore v))
      (by simp only [easBlocks.eas_block_1543_taken_stack,List.length_cons]; omega) r2

end Benchmarks.EAS.EAS
