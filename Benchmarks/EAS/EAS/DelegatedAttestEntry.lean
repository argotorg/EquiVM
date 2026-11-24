import Benchmarks.EAS.EAS.DelegatedAttestPrepare
import Benchmarks.EAS.EAS.DelegatedAttestBounds

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def delegatedAttestEntryReady (cd : ByteArray) : Prop := delegatedAttestValid cd ∧
  copyRequestValid 352 (delegatedAttestRecord cd (attestRoot cd)).data.data.size ∧
  delegatedAttestCopyHeap cd (attestRoot cd)+96 ≤ 2^64-1
instance (cd : ByteArray) : Decidable (delegatedAttestEntryReady cd) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem easDelegatedAttestEntry {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+27 ≤ 1024) (hsize : ee.calldata.size < 2^255+4)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨1933⟩ R attestPublicInitialMemory aw rdata σ k C) :
    (delegatedAttestEntryReady ee.calldata → ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨13494⟩
      (UInt256.ofNat 224::delegatedAttestSavedStack ee.calldata (attestRoot ee.calldata) R)
      (delegatedAttestInputMemory ee.calldata (attestRoot ee.calldata)) aw' rdata σ k' C') ∧
    (¬ delegatedAttestEntryReady ee.calldata → RDrev fork (deployedRuntime v) g s0) := by
  by_cases ho : (calldataWord ee.calldata 4).toNat ≤ 2^64-1
  · obtain ⟨a1,k1,C1,r1⟩ := easBlocks.eas_block_1933_fallthrough_packed (immWords := wordsOf (immStore v))
      (by omega) ((word_gt_zero _ _).mpr ho) rd
    by_cases hh : UInt256.slt (UInt256.sub (UInt256.ofNat ee.calldata.size) (attestRoot ee.calldata)) ⟨192⟩ = ⟨0⟩
    · obtain ⟨a2,k2,C2,r2⟩ := easBlocks.eas_block_1951_fallthrough_packed (immWords := wordsOf (immStore v))
        (by omega) (by rw [delegatedAttestHead_sub]; exact hh) r1
      have hp := easDelegatedAttestPrepare v hstack hsize r2
      exact ⟨fun h => hp.1 ⟨h.1.2.2,h.2⟩,fun h => hp.2 (fun h' => h ⟨⟨ho,hh,h'.1⟩,h'.2⟩)⟩
    · obtain ⟨a2,k2,C2,r2⟩ := easBlocks.eas_block_1951_taken_packed (immWords := wordsOf (immStore v))
        (by omega) (by rw [delegatedAttestHead_sub]; exact hh) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r1
      have hr := easBlocks.eas_block_402 (immWords := wordsOf (immStore v))
        (by simp only [easBlocks.eas_block_1951_taken_stack,List.length_cons]; omega) r2
      exact ⟨fun h => False.elim (hh h.1.2.1),fun _ => hr⟩
  · obtain ⟨a1,k1,C1,r1⟩ := easBlocks.eas_block_1933_taken_packed (immWords := wordsOf (immStore v))
      (by omega) ((word_gt_zero _ _).not.mpr ho) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    have hr := easBlocks.eas_block_402 (immWords := wordsOf (immStore v))
      (by simp only [easBlocks.eas_block_1933_taken_stack,List.length_cons]; omega) r1
    exact ⟨fun h => False.elim (ho h.1.1),fun _ => hr⟩

end Benchmarks.EAS.EAS
