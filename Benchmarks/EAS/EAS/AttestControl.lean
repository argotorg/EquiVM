import Benchmarks.EAS.EAS.OneRequestMemory
import Benchmarks.EAS.EAS.AttestResultMemory
import Benchmarks.EAS.EAS.RuntimeBlocks_004

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem easAttestArraySet {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {array ptr root : UInt256} {R : List UInt256} (v : EASImmutables) (hstack : R.length+9 ≤ 1024)
    (hfit : array.toNat+32 < UInt256.size) (hc : array.toNat+32 ≤ mem.size)
    (hn : memLoad array mem ≠ ⟨0⟩)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨557⟩ (ptr::root::array::R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨7650⟩
      (calldataWord ee.calldata root.toNat::array::UInt256.ofNat ee.source.val::ee.weiValue::R)
      (Reasoning.Theory.writeWord mem (array.toNat+32) ptr) aw' rdata σ k' C' := by
  obtain ⟨a1,k1,C1,r1⟩ := easBlocks.eas_block_557_packed (immWords := wordsOf (immStore v))
    (by omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
  simp only [easBlocks.eas_block_557_stack] at r1
  obtain ⟨a2,k2,C2,r2⟩ := easMemoryArrayFirst v (by simp only [List.length_cons]; omega) hn
    (by rw [easPatchedValidJumps v]; jump_dest) r1
  obtain ⟨a3,k3,C3,r3⟩ := easBlocks.eas_block_566_packed (immWords := wordsOf (immStore v))
    (by omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r2
  have hs : (UInt256.ofNat (array.toNat+32)).toNat = array.toNat+32 := ulit_toNat' _ hfit
  simp only [easBlocks.eas_block_566_stack,easBlocks.eas_block_566_memory,hs] at r3
  change RD fork (deployedRuntime v) ee g s0 ⟨5712⟩ (array::UInt256.ofNat 576::root::array::R)
    (Reasoning.Theory.writeWord mem (array.toNat+32) ptr) a3 rdata σ k3 C3 at r3
  have hn' : memLoad array (Reasoning.Theory.writeWord mem (array.toNat+32) ptr) ≠ ⟨0⟩ := by
    rw [memLoad_write_below _ _ _ _ (le_refl _) hc]
    exact hn
  obtain ⟨a4,k4,C4,r4⟩ := easMemoryArrayFirst v (by simp only [List.length_cons]; omega) hn'
    (by rw [easPatchedValidJumps v]; jump_dest) r3
  exact easBlocks.eas_block_576_packed (immWords := wordsOf (immStore v))
    (by omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r4

theorem easAttestPublicReturn {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {result uidPtr uid used : UInt256} {heap : Nat} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+6 ≤ 1024)
    (hv : AttestResultMemoryView mem result uidPtr [uid] used heap)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨587⟩
      (result::UInt256.ofNat 32::UInt256.ofNat 594::UInt256.ofNat 32::R) mem aw rdata σ k C) :
    RDret fork (deployedRuntime v) g s0 σ uid.toByteArray := by
  obtain ⟨a1,k1,C1,r1⟩ := easBlocks.eas_block_587_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
  simp only [easBlocks.eas_block_587_stack,hv.uidPointer] at r1
  have hn : memLoad uidPtr mem ≠ ⟨0⟩ := by rw [hv.uids.length]; change (⟨1⟩ : UInt256) ≠ ⟨0⟩; decide
  obtain ⟨a2,k2,C2,r2⟩ := easMemoryArrayFirst v (by simp only [List.length_cons]; omega) hn
    (by rw [easPatchedValidJumps v]; jump_dest) r1
  have r3 := easBlocks.eas_block_594 (immWords := wordsOf (immStore v)) (by omega) r2
  have hword : memLoad (UInt256.ofNat (uidPtr.toNat+32)) mem = uid := hv.uids.get 0 (by simp)
  simp only [hword,show (UInt256.ofNat 32).toNat = 32 from rfl] at r3
  change RDret fork (deployedRuntime v) g s0 σ
    ((Reasoning.Theory.writeWord mem (memLoad (UInt256.ofNat 64) mem).toNat uid).readWithPadding
      (memLoad (UInt256.ofNat 64) mem).toNat 32) at r3
  rw [writeWord_sparse_read_back] at r3
  exact r3

end Benchmarks.EAS.EAS
