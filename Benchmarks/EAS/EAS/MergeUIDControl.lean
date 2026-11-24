import Benchmarks.EAS.EAS.WordArrayPrefix
import Benchmarks.EAS.EAS.RuntimeBlocks_037
import Benchmarks.EAS.EAS.RuntimeBlocks_038

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem easMergeUIDDone {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {lists out current ret : UInt256} {n : Nat} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length+8 ≤ 1024) (hl : memLoad lists mem = UInt256.ofNat n)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨11990⟩ (out::current::UInt256.ofNat n::lists::ret::R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ret (out::R) mem aw' rdata σ k' C' := by
  obtain ⟨a1,k1,C1,r1⟩ := easBlocks.eas_block_11990_taken_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (by rw [hl,ult_zero (le_refl _)]; decide)
    (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
  exact easBlocks.eas_block_12078_packed (immWords := wordsOf (immStore v)) (by omega) hret r1

theorem easMergeUIDOuterEnter {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {lists out current ret : UInt256} {i : Nat} {groups : List (List UInt256)} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+12 ≤ 1024)
    (hm : WordArrayArrayMemoryView mem lists groups out.toNat) (hi : i < groups.length)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨11990⟩ (out::current::UInt256.ofNat i::lists::ret::R) mem aw rdata σ k C) :
    ∃ ptr aw' k' C', WordArrayMemoryView mem ptr groups[i] out.toNat ∧
      RD fork (deployedRuntime v) ee g s0 ⟨12017⟩ (⟨0⟩::lists::out::ret::UInt256.ofNat i::ptr::current::R) mem aw' rdata σ k' C' := by
  have hs := hm.span
  have hb := out.val.isLt
  change out.toNat < UInt256.size at hb
  have hlen : groups.length < UInt256.size := by omega
  obtain ⟨ptr,hptr,hview⟩ := hm.arrays i hi
  obtain ⟨a1,k1,C1,r1⟩ := easBlocks.eas_block_11990_fallthrough_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega)
    (by rw [hm.length,ult_one (by rw [ulit_toNat' _ (by omega),ulit_toNat' _ hlen]; exact hi)]; decide) rd
  obtain ⟨a2,k2,C2,r2⟩ := easBlocks.eas_block_12000_packed (immWords := wordsOf (immStore v))
    (by omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r1
  obtain ⟨a3,k3,C3,r3⟩ := easMemoryArrayIndex v (by simp only [List.length_cons]; omega) hi hlen (by omega) hm.length
    (by rw [easPatchedValidJumps v]; jump_dest) r2
  obtain ⟨a4,k4,C4,r4⟩ := easBlocks.eas_block_12012_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) r3
  refine ⟨ptr,a4,k4,C4,hview,?_⟩
  simpa only [easBlocks.eas_block_12012_stack,hptr] using r4

theorem easMergeUIDInnerDone {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {lists out src current ret : UInt256} {i n : Nat} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length+10 ≤ 1024) (hl : memLoad src mem = UInt256.ofNat n)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨12017⟩
      (UInt256.ofNat n::lists::out::ret::UInt256.ofNat i::src::current::R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨11990⟩
      (out::current::UInt256.ofNat (i+1)::lists::ret::R) mem aw' rdata σ k' C' := by
  obtain ⟨a1,k1,C1,r1⟩ := easBlocks.eas_block_12017_taken_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (by rw [hl,ult_zero (le_refl _)]; decide)
    (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
  obtain ⟨a2,k2,C2,r2⟩ := easBlocks.eas_block_12061_packed (immWords := wordsOf (immStore v))
    (by omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r1
  refine ⟨a2,k2,C2,?_⟩
  simpa only [easBlocks.eas_block_12061_stack,show UInt256.ofNat 1 = (⟨1⟩ : UInt256) from rfl,
    u256_add_comm (UInt256.ofNat i),u256_one_add_ofNat] using r2

theorem easMergeUIDInnerStep {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {lists out src ret : UInt256} {i j c len : Nat} {values : List UInt256} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+18 ≤ 1024)
    (hs : WordArrayMemoryView mem src values out.toNat) (hj : j < values.length)
    (hd : memLoad out mem = UInt256.ofNat len) (hc : c < len) (hlen : len ≤ 2^64-1)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨12017⟩
      (UInt256.ofNat j::lists::out::ret::UInt256.ofNat i::src::UInt256.ofNat c::R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨12017⟩
      (UInt256.ofNat (j+1)::lists::out::ret::UInt256.ofNat i::src::UInt256.ofNat (c+1)::R)
      (Reasoning.Theory.writeWord mem (UInt256.ofNat (out.toNat+32+32*c)).toNat values[j]) aw' rdata σ k' C' := by
  have hspan := hs.span
  have hb := out.val.isLt
  change out.toNat < UInt256.size at hb
  have hvlen : values.length < UInt256.size := by omega
  have hlen' : len < UInt256.size := by change _ < 2^256; omega
  obtain ⟨a1,k1,C1,r1⟩ := easBlocks.eas_block_12017_fallthrough_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega)
    (by rw [hs.length,ult_one (by rw [ulit_toNat' _ (by omega),ulit_toNat' _ hvlen]; exact hj)]; decide) rd
  obtain ⟨a2,k2,C2,r2⟩ := easBlocks.eas_block_12027_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r1
  obtain ⟨a3,k3,C3,r3⟩ := easMemoryArrayIndex v (by simp only [List.length_cons]; omega) hj hvlen (by omega) hs.length
    (by rw [easPatchedValidJumps v]; jump_dest) r2
  obtain ⟨a4,k4,C4,r4⟩ := easBlocks.eas_block_12040_packed (immWords := wordsOf (immStore v))
    (by omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r3
  simp only [easBlocks.eas_block_12040_stack,hs.get j hj] at r4
  obtain ⟨a5,k5,C5,r5⟩ := easMemoryArrayIndex v (by simp only [List.length_cons]; omega) hc hlen'
    (by change _ < 2^256; omega) hd (by rw [easPatchedValidJumps v]; jump_dest) r4
  obtain ⟨a6,k6,C6,r6⟩ := easBlocks.eas_block_12051_packed (immWords := wordsOf (immStore v))
    (by omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r5
  refine ⟨a6,k6,C6,?_⟩
  simpa only [easBlocks.eas_block_12051_stack,easBlocks.eas_block_12051_memory,Reasoning.Theory.writeWord,
    show UInt256.ofNat 1 = (⟨1⟩ : UInt256) from rfl,
    u256_add_comm (UInt256.ofNat j),u256_add_comm (UInt256.ofNat c),u256_one_add_ofNat] using r6

end Benchmarks.EAS.EAS
