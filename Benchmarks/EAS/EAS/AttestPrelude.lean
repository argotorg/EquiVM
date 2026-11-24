import Benchmarks.EAS.EAS.AttestDecode
import Benchmarks.EAS.EAS.OneRequestAllocate
import Benchmarks.EAS.EAS.RuntimeBlocks_004

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables ABI.Solc08Calldata
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

-- LIBRARY CANDIDATE: reassociate a wrapping offset check through a four-byte selector.
theorem word_sub_offset4 (size offset : UInt256) :
    UInt256.sub size offset+UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639932 =
      UInt256.sub size (UInt256.ofNat 4+offset) := by
  have hn : UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639932 =
      (⟨-(⟨4⟩ : UInt256).val⟩ : UInt256) := rfl
  rw [hn,← word_sub_eq_add_neg (UInt256.sub size offset) ⟨4⟩]
  apply u256_inj
  change ((size.val-offset.val)-4).val = (size.val-(4+offset.val)).val
  rw [sub_sub,add_comm offset.val]

def attestHeadValid (cd : ByteArray) : Prop :=
  (calldataWord cd 4).toNat ≤ solcMaxU64 ∧
  UInt256.slt (UInt256.sub (UInt256.ofNat cd.size) (attestRoot cd)) ⟨64⟩ = ⟨0⟩
instance (cd : ByteArray) : Decidable (attestHeadValid cd) := inferInstanceAs (Decidable (_ ∧ _))

theorem easAttestHead {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+6 ≤ 1024)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨450⟩ R mem aw rdata σ k C) :
    (attestHeadValid ee.calldata →
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨516⟩
        (attestRoot ee.calldata::calldataWord ee.calldata 4::R) mem aw' rdata σ k' C') ∧
    (¬ attestHeadValid ee.calldata → RDrev fork (deployedRuntime v) g s0) := by
  by_cases ho : (calldataWord ee.calldata 4).toNat ≤ solcMaxU64
  · obtain ⟨a1,k1,C1,r1⟩ := easBlocks.eas_block_450_fallthrough_packed (immWords := wordsOf (immStore v))
      (by omega) (ugt_zero ho) rd
    simp only [easBlocks.eas_block_450_fallthrough_stack] at r1
    constructor
    · intro hg
      exact easBlocks.eas_block_468_fallthrough_packed (immWords := wordsOf (immStore v))
        hstack (by rw [word_sub_offset4]; exact hg.2) r1
    · intro hg
      have hh : UInt256.slt (UInt256.sub (UInt256.ofNat ee.calldata.size) (attestRoot ee.calldata)) ⟨64⟩ ≠ ⟨0⟩ := fun hh => hg ⟨ho,hh⟩
      obtain ⟨a2,k2,C2,r2⟩ := easBlocks.eas_block_468_taken_packed (immWords := wordsOf (immStore v))
        hstack (by rw [word_sub_offset4]; exact hh) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r1
      exact easBlocks.eas_block_402 (immWords := wordsOf (immStore v))
        (by simp only [easBlocks.eas_block_468_taken_stack,List.length_cons]; omega) r2
  · constructor
    · exact fun h => False.elim (ho h.1)
    · intro _
      obtain ⟨a1,k1,C1,r1⟩ := easBlocks.eas_block_450_taken_packed (immWords := wordsOf (immStore v))
        (by omega) (ne_of_eq_of_ne (ugt_one (a := calldataWord ee.calldata 4)
          (b := UInt256.ofNat 18446744073709551615) (by change 18446744073709551615 < _; change ¬ _ ≤ 18446744073709551615 at ho; omega)) (by decide))
        (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
      exact easBlocks.eas_block_402 (immWords := wordsOf (immStore v))
        (by simp only [easBlocks.eas_block_450_taken_stack,List.length_cons]; omega) r1

theorem easRequestReference_branches {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {base head ret : UInt256} {R : List UInt256} (v : EASImmutables) (hstack : R.length+6 ≤ 1024)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨6189⟩ (base::head::ret::R) mem aw rdata σ k C) :
    (requestReferenceValid ee.calldata base head →
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ret
        ((base+calldataWord ee.calldata head.toNat)::R) mem aw' rdata σ k' C') ∧
    (¬ requestReferenceValid ee.calldata base head → RDrev fork (deployedRuntime v) g s0) := by
  have h := easRequestReference v hstack hret rd
  constructor
  · intro hv
    rw [if_pos hv] at h
    exact h
  · intro hv
    rw [if_neg hv] at h
    exact h

theorem easAttestPrepare {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {root offset heap : UInt256} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+21 ≤ 1024)
    (hroot : root = UInt256.ofNat 4+offset) (hlo : 96 ≤ heap.toNat) (hh : heap.toNat+256 ≤ 2^64-1)
    (hheap : memLoad (UInt256.ofNat 64) mem = heap)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨516⟩ (root::offset::R) mem aw rdata σ k C) :
    (requestReferenceValid ee.calldata root (root+UInt256.ofNat 32) →
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨5344⟩
        (attestRequestData ee.calldata root::UInt256.ofNat ee.calldata.size::UInt256.ofNat 557::root::heap::
          UInt256.ofNat 587::UInt256.ofNat 32::UInt256.ofNat 594::UInt256.ofNat 32::R)
        (oneRequestArrayMemory mem heap) aw' rdata σ k' C') ∧
    (¬ requestReferenceValid ee.calldata root (root+UInt256.ofNat 32) → RDrev fork (deployedRuntime v) g s0) := by
  obtain ⟨a1,k1,C1,r1⟩ := easBlocks.eas_block_516_packed (immWords := wordsOf (immStore v))
    (by omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
  simp only [easBlocks.eas_block_516_stack] at r1
  obtain ⟨a2,k2,C2,r2⟩ := easOneRequestAllocate v (by simp only [List.length_cons]; omega) hlo hh hheap
    (by rw [easPatchedValidJumps v]; jump_dest) r1
  obtain ⟨a3,k3,C3,r3⟩ := easBlocks.eas_block_537_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r2
  have hoff : offset+UInt256.ofNat 36 = root+UInt256.ofNat 32 := by
    rw [hroot,u256_add_comm (UInt256.ofNat 4) offset,u256_add_assoc]
    rfl
  simp only [easBlocks.eas_block_537_stack,hoff] at r3
  have hr := easRequestReference_branches v (by simp only [List.length_cons]; omega)
    (by rw [easPatchedValidJumps v]; jump_dest) r3
  constructor
  · intro hv
    obtain ⟨a4,k4,C4,r4⟩ := hr.1 hv
    exact easBlocks.eas_block_552_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r4
  · exact hr.2

end Benchmarks.EAS.EAS
