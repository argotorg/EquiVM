import Benchmarks.EAS.EAS.MultiDelegatedAttestVerifyAccess
import Benchmarks.EAS.EAS.DelegatedAttestationBatch
import Benchmarks.EAS.EAS.RuntimeBlocks_013
import Benchmarks.EAS.EAS.RuntimeBlocks_008

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem easMultiDelegatedAttestFields {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {out : ByteArray} {σ : AccountMap} {k C : Nat}
    {root i groups base available total last n : UInt256} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+19≤1024)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨2826⟩ (root::i::groups::base::available::total::last::n::R) mem aw out σ k C) :
    (DelegatedAttestationBatchReady ee.calldata root → ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨2874⟩
      (multiDelegatedAttestVerifyStack ee.calldata 0 root (delegatedAttestationDataOffset ee.calldata root)
        base n (delegatedAttestationDataLength ee.calldata root) available groups total i last R) mem aw' out σ k' C') ∧
    (¬DelegatedAttestationBatchReady ee.calldata root → RDrev fork (deployedRuntime v) g s0) := by
  obtain ⟨a1,k1,C1,r1⟩ := easBlocks.eas_block_2826_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons];omega) (by rw [easPatchedValidJumpsRuntime v];jump_dest) rd
  simp only [easBlocks.eas_block_2826_stack] at r1
  have hdata := easRequestArrayAccess v (by simp only [List.length_cons];omega) (by rw [easPatchedValidJumps v];jump_dest) r1
  by_cases hd : requestArrayAccessValid ee.calldata root
  · obtain ⟨a2,k2,C2,r2⟩ := hdata.1 hd
    change RD fork (deployedRuntime v) ee g s0 ⟨2840⟩
      (delegatedAttestationDataLength ee.calldata root::delegatedAttestationDataOffset ee.calldata root::total::i::groups::base::available::root::last::n::R)
      mem a2 out σ k2 C2 at r2
    by_cases hn : 0<(delegatedAttestationDataLength ee.calldata root).toNat
    · have hnz : delegatedAttestationDataLength ee.calldata root≠(⟨0⟩ : UInt256) := by
        intro he;rw [he] at hn;contradiction
      obtain ⟨a3,k3,C3,r3⟩ := easBlocks.eas_block_2840_taken_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons];omega) (by rw [isZero_eq_zero_of_ne hnz];decide)
        (by rw [easPatchedValidJumpsRuntime v];jump_dest) r2
      simp only [easBlocks.eas_block_2840_taken_stack] at r3
      obtain ⟨a4,k4,C4,r4⟩ := easBlocks.eas_block_3184_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons];omega) (by rw [easPatchedValidJumpsRuntime v];jump_dest) r3
      simp only [easBlocks.eas_block_3184_stack] at r4
      have hsig := easSignatureArrayReferenceAccess v (by simp only [List.length_cons];omega)
        (by rw [easPatchedValidJumps v];jump_dest) r4
      by_cases hs : signatureArrayReferenceAccessValid ee.calldata root
      · obtain ⟨a5,k5,C5,r5⟩ := hsig.1 hs
        obtain ⟨a6,k6,C6,r6⟩ := easBlocks.eas_block_3198_packed (immWords := wordsOf (immStore v))
          (by simp only [List.length_cons];omega) (by rw [easPatchedValidJumpsRuntime v];jump_dest) r5
        simp only [easBlocks.eas_block_3198_stack] at r6
        by_cases he : delegatedAttestationDataLength ee.calldata root=delegatedAttestationSigLength ee.calldata root
        · obtain ⟨a7,k7,C7,r7⟩ := easBlocks.eas_block_2852_fallthrough_packed (immWords := wordsOf (immStore v))
            (by simp only [List.length_cons];omega)
            (by change UInt256.isZero (UInt256.eq (delegatedAttestationDataLength ee.calldata root) (delegatedAttestationSigLength ee.calldata root))=⟨0⟩;rw [he,uInt256_eq_self];rfl) r6
          simp only [easBlocks.eas_block_2852_fallthrough_stack] at r7
          obtain ⟨a8,k8,C8,r8⟩ := easBlocks.eas_block_2857_packed (immWords := wordsOf (immStore v))
            (by omega) r7
          exact ⟨fun _ => ⟨a8,k8,C8,r8⟩,fun h => (h ⟨hd,hs,hn,he⟩).elim⟩
        · obtain ⟨a7,k7,C7,r7⟩ := easBlocks.eas_block_2852_taken_packed (immWords := wordsOf (immStore v))
            (by simp only [List.length_cons];omega)
            (by change UInt256.isZero (UInt256.eq (delegatedAttestationDataLength ee.calldata root) (delegatedAttestationSigLength ee.calldata root))≠⟨0⟩
                rw [uInt256_eq_zero_of_ne (fun hx => he (uInt256_eq_one_eq hx))];decide)
            (by rw [easPatchedValidJumpsRuntime v];jump_dest) r6
          exact ⟨fun h => (he h.lengths).elim,fun _ => easBlocks.eas_block_1726 (immWords := wordsOf (immStore v))
            (by simp only [easBlocks.eas_block_2852_taken_stack,List.length_cons];omega) r7⟩
      · exact ⟨fun h => (hs h.signatures).elim,fun _ => hsig.2 hs⟩
    · have hz : delegatedAttestationDataLength ee.calldata root=(⟨0⟩ : UInt256) := by
        apply u256_inj
        change (delegatedAttestationDataLength ee.calldata root).toNat=0
        omega
      obtain ⟨a3,k3,C3,r3⟩ := easBlocks.eas_block_2840_fallthrough_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons];omega) (by rw [hz];rfl) r2
      obtain ⟨a4,k4,C4,r4⟩ := easBlocks.eas_block_2852_taken_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons,easBlocks.eas_block_2840_fallthrough_stack];omega) (by rw [hz];decide)
        (by rw [easPatchedValidJumpsRuntime v];jump_dest) r3
      exact ⟨fun h => (hn h.nonempty).elim,fun _ => easBlocks.eas_block_1726 (immWords := wordsOf (immStore v))
        (by simp only [easBlocks.eas_block_2852_taken_stack,easBlocks.eas_block_2840_fallthrough_stack,List.length_cons];omega) r4⟩
  · exact ⟨fun h => (hd h.data).elim,fun _ => hdata.2 hd⟩

end Benchmarks.EAS.EAS
