import Benchmarks.EAS.EAS.SignatureArrayMemory
import Benchmarks.EAS.EAS.RuntimeBlocks_008
import Benchmarks.EAS.EAS.RuntimeBlocks_009

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem signatureAt_eq_record (cd : ByteArray) (ptr : UInt256) (hb : ptr.toNat+64 < UInt256.size) :
    signatureAt cd ptr = signatureRecord cd ptr.toNat := by
  simp only [signatureAt,signatureRecord,uadd_word_ofNat_toNat _ _ hb,
    uadd_word_ofNat_toNat ptr 32 (by omega)]

theorem easCopySignatureArrayStep {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {dst src limit heap : UInt256} {R : List UInt256} (v : EASImmutables) (hstack : R.length+15 ≤ 1024)
    (hi : src.toNat<limit.toNat) (hh : heap.toNat ≤ 2^64-1) (hfree : memLoad (UInt256.ofNat 64) mem = heap)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨1492⟩ (dst::src::limit::R) mem aw rdata σ k C) :
    ((signatureAtValid ee.calldata src ∧ heap.toNat+96 ≤ 2^64-1) →
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨1492⟩ ((dst+UInt256.ofNat 32)::(src+UInt256.ofNat 96)::limit::R)
        (signatureArrayCopyMemory mem dst heap (signatureAt ee.calldata src)) aw' rdata σ k' C') ∧
    (¬ (signatureAtValid ee.calldata src ∧ heap.toNat+96 ≤ 2^64-1) → RDrev fork (deployedRuntime v) g s0) := by
  obtain ⟨a1,j1,D1,r1⟩ := easBlocks.eas_block_1492_taken_packed (immWords := wordsOf (immStore v)) (by omega)
    (by rw [ult_one hi]; decide) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
  obtain ⟨a2,j2,D2,r2⟩ := easBlocks.eas_block_1780_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r1
  have hc := easSignatureCalldataCopy v (by simp only [List.length_cons]; omega) hh hfree
    (by rw [easPatchedValidJumps v]; jump_dest) r2
  refine ⟨?_,hc.2⟩
  intro hg
  obtain ⟨a3,j3,D3,r3⟩ := hc.1 hg
  obtain ⟨a4,j4,D4,r4⟩ := easBlocks.eas_block_1795_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r3
  exact ⟨a4,j4,D4,r4⟩

theorem easCopySignatureArrayDone {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {dst stop : UInt256} {R : List UInt256} (v : EASImmutables) (hstack : R.length+5 ≤ 1024)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨1492⟩ (dst::stop::stop::R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨1500⟩ (dst::stop::stop::R) mem aw' rdata σ k' C' :=
  easBlocks.eas_block_1492_fallthrough_packed (immWords := wordsOf (immStore v)) hstack (ult_zero (le_refl _)) rd

end Benchmarks.EAS.EAS
