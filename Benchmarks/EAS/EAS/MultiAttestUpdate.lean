import Benchmarks.EAS.EAS.MultiAttestControl
import Benchmarks.EAS.EAS.AttestResultMemory
import Benchmarks.EAS.EAS.RuntimeBlocks_013
import Benchmarks.EAS.EAS.RuntimeBlocks_016
import Benchmarks.EAS.EAS.RuntimeBlocks_022

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem easCheckedSub {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {a b ret : UInt256} {R : List UInt256} (v : EASImmutables) (hstack : R.length+4 ≤ 1024)
    (hb : b.toNat ≤ a.toNat) (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨5652⟩ (a::b::ret::R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ret (UInt256.sub a b::R) mem aw' rdata σ k' C' := by
  obtain ⟨a1,j1,D1,h1⟩ := easBlocks.eas_block_5652_fallthrough_packed (immWords := wordsOf (immStore v))
    hstack (ugt_zero (by rw [usub_toNat hb]; omega)) rd
  exact easBlocks.eas_block_5664_packed (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) hret h1

theorem easMultiAttestUpdate {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C n i heap : Nat}
    {base table available count result uid used : UInt256} {words R : List UInt256} (v : EASImmutables)
    (hstack : R.length+18 ≤ 1024) (hi : i<n)
    (ht : table.toNat+32+32*n ≤ result.toNat) (hb : heap < UInt256.size)
    (hm : AttestResultMemoryView mem result uid words used heap)
    (hl : memLoad table mem = UInt256.ofNat n) (hused : used.toNat ≤ available.toNat)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨3131⟩ (result::multiAttestSaved n i base table available count R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨3767⟩
      (multiAttestLoopStack n (i+1) base table (UInt256.sub available used) (UInt256.ofNat words.length+count) R)
      (Reasoning.Theory.writeWord mem (table.toNat+32+32*i) uid) aw' rdata σ k' C' := by
  have hrspan := hm.span
  have huspan := hm.uids.span
  have hcovered := hm.covered
  have hn : n<UInt256.size := by omega
  have hs : (UInt256.ofNat (table.toNat+32+32*i)).toNat = table.toNat+32+32*i := ulit_toNat' _ (by omega)
  have hp32 : (result+⟨32⟩).toNat = result.toNat+32 := uadd_word_ofNat_toNat result 32 (by omega)
  obtain ⟨a1,j1,D1,h1⟩ := easBlocks.eas_block_3131_packed (immWords := wordsOf (immStore v))
    (by simp only [multiAttestSaved,List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
  simp only [easBlocks.eas_block_3131_stack,hm.usedValue] at h1
  obtain ⟨a2,j2,D2,h2⟩ := easCheckedSub v (by simp only [List.length_cons]; omega) hused
    (by rw [easPatchedValidJumps v]; jump_dest) h1
  obtain ⟨a3,j3,D3,h3⟩ := easBlocks.eas_block_3853_packed (immWords := wordsOf (immStore v))
    (by omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) h2
  have hptr : memLoad (result+⟨32⟩) mem = uid := hm.uidPointer
  simp only [easBlocks.eas_block_3853_stack,hptr] at h3
  obtain ⟨a4,j4,D4,h4⟩ := easMemoryArrayIndex v (by simp only [List.length_cons]; omega) hi hn (by omega) hl
    (by rw [easPatchedValidJumps v]; jump_dest) h3
  obtain ⟨a5,j5,D5,h5⟩ := easBlocks.eas_block_3867_packed (immWords := wordsOf (immStore v))
    (by omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) h4
  simp only [easBlocks.eas_block_3867_stack,easBlocks.eas_block_3867_memory,← writeWord_as_write,hs] at h5
  have hl' : memLoad table (Reasoning.Theory.writeWord mem (table.toNat+32+32*i) uid) = UInt256.ofNat n :=
    (memLoad_write_below _ _ _ _ (by omega) (by omega)).trans hl
  obtain ⟨a6,j6,D6,h6⟩ := easMemoryArrayIndex v (by simp only [List.length_cons]; omega) hi hn (by omega) hl'
    (by rw [easPatchedValidJumps v]; jump_dest) h5
  have hp' : memLoad (result+⟨32⟩) (Reasoning.Theory.writeWord mem (table.toNat+32+32*i) uid) = uid :=
    (memLoad_write_above _ _ _ _ (by rw [hp32]; omega) (by rw [hp32]; omega)).trans hm.uidPointer
  have hu' : memLoad uid (Reasoning.Theory.writeWord mem (table.toNat+32+32*i) uid) = UInt256.ofNat words.length :=
    (memLoad_write_above _ _ _ _ (by omega) (by have := hm.uids.covered; omega)).trans hm.uids.length
  obtain ⟨a7,j7,D7,h7⟩ := easBlocks.eas_block_3878_packed (immWords := wordsOf (immStore v))
    (by omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) h6
  have hinc : UInt256.ofNat i+⟨1⟩ = UInt256.ofNat (i+1) :=
    (u256_add_comm _ _).trans (u256_one_add_ofNat i)
  exact ⟨a7,j7,D7,by simpa only [easBlocks.eas_block_3878_stack,hp',hu',multiAttestLoopStack,hinc] using h7⟩

end Benchmarks.EAS.EAS
