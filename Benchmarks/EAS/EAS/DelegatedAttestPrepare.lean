import Benchmarks.EAS.EAS.DelegatedAttestPrepareMemory
import Benchmarks.EAS.EAS.CalldataAddress
import Benchmarks.EAS.EAS.RuntimeBlocks_008
import Benchmarks.EAS.EAS.RuntimeBlocks_009
import Benchmarks.EAS.EAS.RuntimeBlocks_010

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def delegatedAttestReady (cd : ByteArray) (root : UInt256) : Prop :=
  delegatedAttestFieldsValid cd root ∧ copyRequestValid 352 (delegatedAttestRecord cd root).data.data.size ∧
    delegatedAttestCopyHeap cd root+96 ≤ 2^64-1
instance (cd : ByteArray) (root : UInt256) : Decidable (delegatedAttestReady cd root) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))
def delegatedAttestSavedStack (cd : ByteArray) (root : UInt256) (R : List UInt256) : List UInt256 :=
  UInt256.ofNat 2122::root::UInt256.ofNat 2141::(root+UInt256.ofNat 160)::UInt256.ofNat 2166::
    (root+UInt256.ofNat 32)::calldataWord cd root.toNat::UInt256.ofNat 587::UInt256.ofNat 32::UInt256.ofNat 594::UInt256.ofNat 32::R

theorem easDelegatedAttestPrepare {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat} {off : UInt256} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+27 ≤ 1024) (hsize : ee.calldata.size < 2^255+4)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨1999⟩ ((UInt256.ofNat 4+off)::off::R) attestPublicInitialMemory aw rdata σ k C) :
    (delegatedAttestReady ee.calldata (UInt256.ofNat 4+off) →
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨13494⟩
        (UInt256.ofNat 224::delegatedAttestSavedStack ee.calldata (UInt256.ofNat 4+off) R)
        (delegatedAttestInputMemory ee.calldata (UInt256.ofNat 4+off)) aw' rdata σ k' C') ∧
    (¬ delegatedAttestReady ee.calldata (UInt256.ofNat 4+off) → RDrev fork (deployedRuntime v) g s0) := by
  let root := UInt256.ofNat 4+off
  have h32 : off+UInt256.ofNat 36 = root+UInt256.ofNat 32 := by
    change _ = (UInt256.ofNat 4+off)+UInt256.ofNat 32
    rw [u256_add_comm (UInt256.ofNat 4) off,u256_add_assoc]; rfl
  have h64 : off+UInt256.ofNat 68 = root+UInt256.ofNat 64 := by
    change _ = (UInt256.ofNat 4+off)+UInt256.ofNat 64
    rw [u256_add_comm (UInt256.ofNat 4) off,u256_add_assoc]; rfl
  have h160 : off+UInt256.ofNat 164 = root+UInt256.ofNat 160 := by
    change _ = (UInt256.ofNat 4+off)+UInt256.ofNat 160
    rw [u256_add_comm (UInt256.ofNat 4) off,u256_add_assoc]; rfl
  obtain ⟨a1,k1,C1,r1⟩ := easBlocks.eas_block_1999_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
  simp only [easBlocks.eas_block_1999_stack,show memLoad (UInt256.ofNat 64) attestPublicInitialMemory = UInt256.ofNat 224 by native_decide] at r1
  obtain ⟨a2,k2,C2,r2⟩ := easFixedAllocate_ok v .bytes128 (by simp only [List.length_cons]; omega)
    (by native_decide) (by rw [easPatchedValidJumps v]; jump_dest) r1
  simp only [FixedAllocationSite.size,show (UInt256.ofNat 224).toNat = 224 from rfl,show allocateNext 224 128 = 352 by native_decide] at r2
  by_cases ho : (calldataWord ee.calldata (root+UInt256.ofNat 32).toNat).toNat ≤ 2^64-1
  · obtain ⟨a3,k3,C3,r3⟩ := easBlocks.eas_block_2011_fallthrough_packed (immWords := wordsOf (immStore v))
      (by omega) (by rw [h32]; exact (word_gt_zero _ _).mpr ho) r2
    obtain ⟨a4,k4,C4,r4⟩ := easBlocks.eas_block_2041_packed (immWords := wordsOf (immStore v))
      (by omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r3
    have hdata : (off+calldataWord ee.calldata (root+UInt256.ofNat 32).toNat)+UInt256.ofNat 4 = delegatedAttestData ee.calldata root := by
      rw [u256_add_comm _ (UInt256.ofNat 4),← u256_add_assoc]
      rfl
    simp only [easBlocks.eas_block_2041_stack,easBlocks.eas_block_2011_fallthrough_memory,
      easBlocks.eas_block_2011_fallthrough_stack,← writeWord_as_write,hdata,h32] at r4
    change RD fork (deployedRuntime v) ee g s0 ⟨5344⟩
      (delegatedAttestData ee.calldata root::UInt256.ofNat ee.calldata.size::UInt256.ofNat 2079::off::UInt256.ofNat 164::
        UInt256.ofNat 2122::root::UInt256.ofNat 2141::UInt256.ofNat 224::UInt256.ofNat 2166::(root+UInt256.ofNat 32)::
        calldataWord ee.calldata root.toNat::UInt256.ofNat 587::UInt256.ofNat 32::UInt256.ofNat 594::UInt256.ofNat 32::R)
      (delegatedAttestSchemaMemory ee.calldata root) a4 rdata σ k4 C4 at r4
    have hcopy := easCopyRequest_branches (heap := UInt256.ofNat 352) v (by simp only [List.length_cons]; omega)
      (by decide) (by decide) (delegatedAttestSchemaMemory_facts ee.calldata root).2.1
      (by rw [easPatchedValidJumps v]; jump_dest) r4
    by_cases hg : requestCopyRunValid ee.calldata (delegatedAttestData ee.calldata root) (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 352)
    · have hd := requestCopyRunValid_data hg
      have hv := (requestCopyRunValid_iff hd).mp hg
      have hm := requestCopyMemory_views (delegatedAttestSchemaMemory ee.calldata root) ee.calldata (delegatedAttestData ee.calldata root)
        (UInt256.ofNat 352) (by decide) (by decide) hsize hd hv
      let heap := delegatedAttestCopyHeap ee.calldata root
      have hheap : heap ≤ 2^64-1 := hv.2.2.1
      have hn : (UInt256.ofNat heap).toNat = heap := ulit_toNat' _ (by change heap < 2^256; omega)
      obtain ⟨a5,k5,C5,r5⟩ := hcopy.1 hg
      obtain ⟨a6,k6,C6,r6⟩ := easBlocks.eas_block_2079_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r5
      simp only [easBlocks.eas_block_2079_stack,h64,easBlocks.eas_block_2079_memory,← writeWord_as_write] at r6
      change RD fork (deployedRuntime v) ee g s0 ⟨6273⟩
        ((root+UInt256.ofNat 64)::UInt256.ofNat ee.calldata.size::UInt256.ofNat 2096::off::UInt256.ofNat 164::
          UInt256.ofNat 2122::root::UInt256.ofNat 2141::UInt256.ofNat 224::UInt256.ofNat 2166::(root+UInt256.ofNat 32)::
          calldataWord ee.calldata root.toNat::UInt256.ofNat 587::UInt256.ofNat 32::UInt256.ofNat 594::UInt256.ofNat 32::R)
        (delegatedAttestLinkedMemory ee.calldata root) a6 rdata σ k6 C6 at r6
      have hfree : memLoad (UInt256.ofNat 64) (delegatedAttestLinkedMemory ee.calldata root) = UInt256.ofNat heap := by
        unfold delegatedAttestLinkedMemory
        rw [memLoad_write_below _ _ _ _ (by decide) (by
          have hcov := hm.2.1.covered
          change 352+192 ≤ (delegatedAttestCopiedMemory ee.calldata root).size at hcov
          change 96 ≤ (delegatedAttestCopiedMemory ee.calldata root).size; omega)]
        exact hm.2.2.1
      have hsig := easSignatureCalldataCopy (heap := UInt256.ofNat heap) v (by simp only [List.length_cons]; omega)
        (by rw [hn]; exact hheap) hfree (by rw [easPatchedValidJumps v]; jump_dest) r6
      by_cases hsg : signatureAtValid ee.calldata (root+UInt256.ofNat 64) ∧ heap+96 ≤ 2^64-1
      · obtain ⟨a7,k7,C7,r7⟩ := hsig.1 (by simpa only [hn] using hsg)
        obtain ⟨a8,k8,C8,r8⟩ := easBlocks.eas_block_2096_packed (immWords := wordsOf (immStore v))
          (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r7
        simp only [easBlocks.eas_block_2096_stack,h160] at r8
        have hadd := easCalldataAddress v (by simp only [List.length_cons]; omega)
          (by rw [easPatchedValidJumps v]; jump_dest) r8
        by_cases ha : (calldataWord ee.calldata (root+UInt256.ofNat 160).toNat).toNat < EVM.addressModulus
        · rw [if_pos ha] at hadd
          obtain ⟨a9,k9,C9,r9⟩ := hadd
          obtain ⟨a10,k10,C10,r10⟩ := easBlocks.eas_block_2112_packed (immWords := wordsOf (immStore v))
            (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r9
          exact ⟨fun _ => ⟨a10,k10,C10,r10⟩,fun h => False.elim (h ⟨⟨ho,hd,hsg.1,ha⟩,hv,hsg.2⟩)⟩
        · rw [if_neg ha] at hadd
          exact ⟨fun h => False.elim (ha h.1.2.2.2),fun _ => hadd⟩
      · have hr := hsig.2 (by simpa only [hn] using hsg)
        exact ⟨fun h => False.elim (hsg ⟨h.1.2.2.1,h.2.2⟩),fun _ => hr⟩
    · have hr := hcopy.2 hg
      exact ⟨fun h => False.elim (hg ((requestCopyRunValid_iff h.1.2.1).mpr h.2.1)),fun _ => hr⟩
  · obtain ⟨a3,k3,C3,r3⟩ := easBlocks.eas_block_2011_taken_packed (immWords := wordsOf (immStore v))
      (by omega) (by rw [h32]; exact (word_gt_zero _ _).not.mpr ho)
      (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r2
    have hr := easBlocks.eas_block_402 (immWords := wordsOf (immStore v))
      (by simp only [easBlocks.eas_block_2011_taken_stack,List.length_cons]; omega) r3
    exact ⟨fun h => False.elim (ho h.1.1),fun _ => hr⟩

end Benchmarks.EAS.EAS
