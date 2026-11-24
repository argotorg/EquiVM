import Benchmarks.EAS.EAS.DelegatedAttestationDecode
import Benchmarks.EAS.EAS.SignatureArrayDecode
import Benchmarks.EAS.EAS.RuntimeBlocks_024

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def signatureArrayReferenceAccessValid (cd : ByteArray) (root : UInt256) : Prop :=
  delegatedAttestationArrayReferenceValid cd root 64 ∧
  (calldataWord cd (delegatedBatchArray cd root 64).toNat).toNat ≤ 2^64-1 ∧
  UInt256.sgt ((UInt256.ofNat 32)+delegatedBatchArray cd root 64)
    (UInt256.sub (UInt256.ofNat cd.size) (UInt256.mul (calldataWord cd (delegatedBatchArray cd root 64).toNat) (UInt256.ofNat 96))) = ⟨0⟩
instance (cd : ByteArray) (root : UInt256) : Decidable (signatureArrayReferenceAccessValid cd root) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem easSignatureArrayReferenceAccess {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {root ret : UInt256} {R : List UInt256} (v : EASImmutables) (hstack : R.length+6 ≤ 1024)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨6105⟩ (root::(root+UInt256.ofNat 64)::ret::R) mem aw rdata σ k C) :
    (signatureArrayReferenceAccessValid ee.calldata root → ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ret
      (calldataWord ee.calldata (delegatedBatchArray ee.calldata root 64).toNat::
        (delegatedBatchArray ee.calldata root 64+UInt256.ofNat 32)::R) mem aw' rdata σ k' C') ∧
    (¬signatureArrayReferenceAccessValid ee.calldata root → RDrev fork (deployedRuntime v) g s0) := by
  have hneg : (UInt256.sub (UInt256.ofNat ee.calldata.size) root)+UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639905 =
      (UInt256.ofNat ee.calldata.size-root)-⟨31⟩ := by rw [word_sub_eq_add_neg (UInt256.ofNat ee.calldata.size-root) ⟨31⟩]; rfl
  by_cases href : delegatedAttestationArrayReferenceValid ee.calldata root 64
  · obtain ⟨a1,k1,C1,r1⟩ := easBlocks.eas_block_6105_fallthrough_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (by rw [hneg]; exact href) rd
    by_cases hlen : (calldataWord ee.calldata (delegatedBatchArray ee.calldata root 64).toNat).toNat ≤ 2^64-1
    · obtain ⟨a2,k2,C2,r2⟩ := easBlocks.eas_block_6153_fallthrough_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) (ugt_zero hlen) r1
      by_cases he : UInt256.sgt ((UInt256.ofNat 32)+delegatedBatchArray ee.calldata root 64)
          (UInt256.sub (UInt256.ofNat ee.calldata.size) (UInt256.mul (calldataWord ee.calldata (delegatedBatchArray ee.calldata root 64).toNat) (UInt256.ofNat 96))) = ⟨0⟩
      · obtain ⟨a3,k3,C3,r3⟩ := easBlocks.eas_block_6172_fallthrough_packed (immWords := wordsOf (immStore v))
          (by omega) he r2
        obtain ⟨a4,k4,C4,r4⟩ := easBlocks.eas_block_6188_packed (immWords := wordsOf (immStore v))
          (by simp only [List.length_cons]; omega) hret r3
        refine ⟨fun _ => ⟨a4,k4,C4,?_⟩,fun h => (h ⟨href,hlen,he⟩).elim⟩
        simpa only [easBlocks.eas_block_6188_stack,easBlocks.eas_block_6172_fallthrough_stack,
          easBlocks.eas_block_6153_fallthrough_stack,easBlocks.eas_block_6105_fallthrough_stack,
          delegatedBatchArray,u256_add_comm (UInt256.ofNat 32)] using r4
      · obtain ⟨a3,k3,C3,r3⟩ := easBlocks.eas_block_6172_taken_packed (immWords := wordsOf (immStore v))
          (by omega) he (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r2
        exact ⟨fun h => (he h.2.2).elim,fun _ => easBlocks.eas_block_402 (immWords := wordsOf (immStore v))
          (by simp only [easBlocks.eas_block_6172_taken_stack,List.length_cons]; omega) r3⟩
    · obtain ⟨a2,k2,C2,r2⟩ := easBlocks.eas_block_6153_taken_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) (by rw [ugt_one (by change 18446744073709551615 < (calldataWord ee.calldata (delegatedBatchArray ee.calldata root 64).toNat).toNat; omega)]; decide)
        (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r1
      exact ⟨fun h => (hlen h.2.1).elim,fun _ => easBlocks.eas_block_402 (immWords := wordsOf (immStore v))
        (by simp only [easBlocks.eas_block_6153_taken_stack,List.length_cons]; omega) r2⟩
  · obtain ⟨a1,k1,C1,r1⟩ := easBlocks.eas_block_6105_taken_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (by rw [hneg]; exact href)
      (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    exact ⟨fun h => (href h.1).elim,fun _ => easBlocks.eas_block_402 (immWords := wordsOf (immStore v))
      (by simp only [easBlocks.eas_block_6105_taken_stack,List.length_cons]; omega) r1⟩

end Benchmarks.EAS.EAS
