import Benchmarks.EAS.EAS.OneRevocationAllocate
import Benchmarks.EAS.EAS.AttestPublicMemory
import Benchmarks.EAS.EAS.MemoryArrayIndex
import Benchmarks.EAS.EAS.RuntimeBlocks_015
import Benchmarks.EAS.EAS.ReferenceTail

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def revokePublicArrayMemory : ByteArray := oneRevocationArrayMemory attestPublicInitialMemory (UInt256.ofNat 224)
def revokePublicCopiedMemory (cd : ByteArray) : ByteArray :=
  Reasoning.Theory.writeWord
    (Reasoning.Theory.writeWord (Reasoning.Theory.writeWord revokePublicArrayMemory 64 (UInt256.ofNat 416))
      352 (calldataWord cd 36)) 384 (calldataWord cd 68)
def revokePublicInputMemory (cd : ByteArray) : ByteArray :=
  Reasoning.Theory.writeWord (revokePublicCopiedMemory cd) 256 (UInt256.ofNat 352)

theorem revokePublicArrayMemory_facts :
    revokePublicArrayMemory.size = 352 ∧ memLoad (UInt256.ofNat 224) revokePublicArrayMemory = ⟨1⟩ ∧
    memLoad (UInt256.ofNat 64) revokePublicArrayMemory = UInt256.ofNat 352 ∧
    memLoad (UInt256.ofNat 96) revokePublicArrayMemory = ⟨0⟩ := by native_decide

theorem easRevokePublicPrepare {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+14 ≤ 1024)
    (hsize : ee.calldata.size < UInt256.size) (h100 : 100 ≤ ee.calldata.size) (hbig : ee.calldata.size < 2^255+4)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨3588⟩ R attestPublicInitialMemory aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨12085⟩
      (calldataWord ee.calldata 4::UInt256.ofNat 224::UInt256.ofNat ee.source.val::ee.weiValue::UInt256.ofNat 1180::R)
      (revokePublicInputMemory ee.calldata) aw' rdata σ k' C' := by
  obtain ⟨a1,k1,C1,r1⟩ := easBlocks.eas_block_3588_packed (immWords := wordsOf (immStore v))
    (by omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
  simp only [easBlocks.eas_block_3588_stack] at r1
  obtain ⟨a2,k2,C2,r2⟩ := easOneRevocationAllocate (heap := UInt256.ofNat 224) v
    (by simp only [List.length_cons]; omega) (by decide) (by decide) (by native_decide)
    (by rw [easPatchedValidJumps v]; jump_dest) r1
  obtain ⟨a3,k3,C3,r3⟩ := easBlocks.eas_block_3598_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r2
  have hsub : UInt256.ofNat ee.calldata.size+UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639900 =
      UInt256.sub (UInt256.ofNat ee.calldata.size) ⟨36⟩ := by
    change _ = UInt256.ofNat ee.calldata.size-⟨36⟩
    rw [word_sub_eq_add_neg (UInt256.ofNat ee.calldata.size) ⟨36⟩]; rfl
  obtain ⟨a4,k4,C4,r4⟩ := easBlocks.eas_block_5854_fallthrough_packed (immWords := wordsOf (immStore v))
    (by simp only [easBlocks.eas_block_3598_stack,List.length_cons]; omega)
    (by rw [hsub]; exact solcDecodeLenCheckOk (head := ⟨36⟩) (need := ⟨64⟩) (by change 100 ≤ _; exact h100) (by change ee.calldata.size < 2^255+36; omega) hsize (by decide)) r3
  obtain ⟨a5,k5,C5,r5⟩ := easBlocks.eas_block_5897_packed (immWords := wordsOf (immStore v))
    (by simp only [easBlocks.eas_block_5854_fallthrough_stack,easBlocks.eas_block_3598_stack,List.length_cons]; omega)
    (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r4
  change RD fork (deployedRuntime v) ee g s0 ⟨4798⟩
    (memLoad (UInt256.ofNat 64) revokePublicArrayMemory::UInt256.ofNat 5909::UInt256.ofNat 3607::
      memLoad (UInt256.ofNat 64) revokePublicArrayMemory::UInt256.ofNat 224::UInt256.ofNat 1180::R)
    revokePublicArrayMemory a5 rdata σ k5 C5 at r5
  rw [revokePublicArrayMemory_facts.2.2.1] at r5
  obtain ⟨a6,k6,C6,r6⟩ := easFixedAllocate_ok v .bytes64 (by simp only [List.length_cons]; omega)
    (by native_decide) (by rw [easPatchedValidJumps v]; jump_dest) r5
  obtain ⟨a7,k7,C7,r7⟩ := easBlocks.eas_block_5909_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r6
  change RD fork (deployedRuntime v) ee g s0 ⟨3607⟩ (UInt256.ofNat 352::UInt256.ofNat 224::UInt256.ofNat 1180::R)
    (revokePublicCopiedMemory ee.calldata) a7 rdata σ k7 C7 at r7
  obtain ⟨a8,k8,C8,r8⟩ := easBlocks.eas_block_3607_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r7
  have hlen : memLoad (UInt256.ofNat 224) (revokePublicCopiedMemory ee.calldata) = ⟨1⟩ := by
    unfold revokePublicCopiedMemory
    rw [memLoad_write_below _ _ _ _ (by decide) (by change 256 ≤ _; rw [writeWord_sparse_size,writeWord_sparse_size]; omega),
      memLoad_write_below _ _ _ _ (by decide) (by rw [writeWord_sparse_size,revokePublicArrayMemory_facts.1]; decide),
      memLoad_write_above _ _ _ _ (by decide) (by rw [revokePublicArrayMemory_facts.1]; decide)]
    exact revokePublicArrayMemory_facts.2.1
  obtain ⟨a9,k9,C9,r9⟩ := easMemoryArrayFirst v (by simp only [easBlocks.eas_block_3607_stack,List.length_cons]; omega)
    (by rw [hlen]; decide) (by rw [easPatchedValidJumps v]; jump_dest) r8
  obtain ⟨a10,k10,C10,r10⟩ := easBlocks.eas_block_3616_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r9
  change RD fork (deployedRuntime v) ee g s0 ⟨5712⟩
    (UInt256.ofNat 224::UInt256.ofNat 3626::UInt256.ofNat 224::UInt256.ofNat 1180::R)
    (revokePublicInputMemory ee.calldata) a10 rdata σ k10 C10 at r10
  have hlen' : memLoad (UInt256.ofNat 224) (revokePublicInputMemory ee.calldata) = ⟨1⟩ := by
    unfold revokePublicInputMemory
    rw [memLoad_write_below _ _ _ _ (by decide) (by change 256 ≤ _; unfold revokePublicCopiedMemory; rw [writeWord_sparse_size]; omega)]
    exact hlen
  obtain ⟨a11,k11,C11,r11⟩ := easMemoryArrayFirst v (by simp only [List.length_cons]; omega)
    (by rw [hlen']; decide) (by rw [easPatchedValidJumps v]; jump_dest) r10
  exact easBlocks.eas_block_3626_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r11

end Benchmarks.EAS.EAS
