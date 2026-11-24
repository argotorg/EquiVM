import Benchmarks.EAS.EAS.BoolMemory
import Benchmarks.EAS.EAS.SchemaHead

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

def schemaFieldsMemory (mem : ByteArray) (src dst : UInt256) : ByteArray :=
  writeWordSequence mem dst.toNat [memLoad src mem,memLoad (src+UInt256.ofNat 32) mem,memLoad (src+UInt256.ofNat 64) mem]

theorem easSchemaFields {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {src dst ending ret : UInt256} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length+11 ≤ 1024) (hsrc : 96 ≤ src.toNat) (hin : src.toNat+128 ≤ mem.size)
    (hdisj : src.toNat+128 ≤ dst.toNat) (hb : dst.toNat+128 < UInt256.size)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨7385⟩ (src::ending::dst::ret::R) mem aw out σ k C) :
    if (memLoad (src+UInt256.ofNat 32) mem).toNat < EVM.addressModulus ∧
        (memLoad (src+UInt256.ofNat 64) mem = ⟨0⟩ ∨ memLoad (src+UInt256.ofNat 64) mem = ⟨1⟩) ∧
        (memLoad (src+UInt256.ofNat 96) mem).toNat ≤ solcMaxU64 then
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨7467⟩
        (src::memLoad (src+UInt256.ofNat 96) mem::ending::dst::ret::R)
        (schemaFieldsMemory mem src dst) aw' out σ k' C'
    else RDrev fork (deployedRuntime v) g s0 := by
  let uid := memLoad src mem
  let resolver := memLoad (src+UInt256.ofNat 32) mem
  let rev := memLoad (src+UInt256.ofNat 64) mem
  let offset := memLoad (src+UInt256.ofNat 96) mem
  let m1 := Reasoning.Theory.writeWord mem dst.toNat uid
  let m2 := Reasoning.Theory.writeWord m1 (dst.toNat+32) resolver
  let m3 := Reasoning.Theory.writeWord m2 (dst.toNat+64) rev
  have hd32 : (dst+UInt256.ofNat 32).toNat = dst.toNat+32 := uadd_word_ofNat_toNat dst 32 (by omega)
  have hd64 : (dst+UInt256.ofNat 64).toNat = dst.toNat+64 := uadd_word_ofNat_toNat dst 64 (by omega)
  have hp1 : MemoryPrefix mem m1 dst.toNat := memoryPrefix_sparse_writeWord _ _ _ _ (Or.inl (le_refl _))
  have hp2 : MemoryPrefix mem m2 dst.toNat := hp1.trans (memoryPrefix_sparse_writeWord _ _ _ _ (Or.inl (by omega)))
  have hp3 : MemoryPrefix mem m3 dst.toNat := hp2.trans (memoryPrefix_sparse_writeWord _ _ _ _ (Or.inl (by omega)))
  have keep {after : ByteArray} (hp : MemoryPrefix mem after dst.toNat) (n : Nat) (hn : n ≤ 96) :
      memLoad (src+UInt256.ofNat n) after = memLoad (src+UInt256.ofNat n) mem := by
    have hs : (src+UInt256.ofNat n).toNat = src.toNat+n := uadd_word_ofNat_toNat src n (by omega)
    exact memLoad_of_prefix hp _ (by rw [hs]; omega) (by rw [hs]; omega) (by rw [hs]; omega)
  have hr1 : memLoad (src+UInt256.ofNat 32) m1 = resolver := keep hp1 32 (by decide)
  have hr2 : memLoad (src+UInt256.ofNat 64) m2 = rev := keep hp2 64 (by decide)
  have hr3 : memLoad (src+UInt256.ofNat 96) m3 = offset := keep hp3 96 (by decide)
  by_cases ha : resolver.toNat < EVM.addressModulus
  · have hc : UInt256.sub (memLoad (src+UInt256.ofNat 32) m1)
        (UInt256.land (memLoad (src+UInt256.ofNat 32) m1) solcAddrMask) = ⟨0⟩ := by
      rw [hr1,solcAddrMask_clean ha,u256_sub_self]
    obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_7385_fallthrough_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) hc rd
    change RD fork (deployedRuntime v) ee g s0 ⟨7424⟩
      (memLoad (src+UInt256.ofNat 32) m1::src::ending::dst::ret::R) m1 aw1 out σ k1 C1 at rd1
    rw [hr1] at rd1
    obtain ⟨aw2,k2,C2,rd2⟩ := easBlocks.eas_block_7424_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd1
    simp only [easBlocks.eas_block_7424_stack,easBlocks.eas_block_7424_memory,hd32] at rd2
    have hr := easDecodeBoolMemory v (by simp only [List.length_cons]; omega)
      (by rw [easPatchedValidJumps v]; jump_dest) rd2
    change (if memLoad (src+UInt256.ofNat 64) m2 = ⟨0⟩ ∨ memLoad (src+UInt256.ofNat 64) m2 = ⟨1⟩ then
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨7440⟩
        (memLoad (src+UInt256.ofNat 64) m2::src::ending::dst::ret::R) m2 aw' out σ k' C'
      else RDrev fork (deployedRuntime v) g s0) at hr
    rw [hr2] at hr
    by_cases hrev : rev=⟨0⟩ ∨ rev=⟨1⟩
    · rw [if_pos hrev] at hr
      obtain ⟨aw3,k3,C3,rd3⟩ := hr
      have hmem3 : easBlocks.eas_block_7440_fallthrough_memory (mem := m2) (x0 := rev) (x3 := dst) = m3 := by
        simp only [easBlocks.eas_block_7440_fallthrough_memory,hd64]; rfl
      by_cases hoff : offset.toNat ≤ solcMaxU64
      · have hc1 : UInt256.gt (memLoad (src+UInt256.ofNat 96) m3) (UInt256.ofNat 18446744073709551615) = ⟨0⟩ := by
          rw [hr3]; exact ugt_zero hoff
        obtain ⟨aw4,k4,C4,rd4⟩ := easBlocks.eas_block_7440_fallthrough_packed (immWords := wordsOf (immStore v))
          (by simp only [List.length_cons]; omega) (by simpa only [hd64] using hc1) rd3
        rw [if_pos ⟨ha,hrev,hoff⟩]
        refine ⟨aw4,k4,C4,?_⟩
        simp only [easBlocks.eas_block_7440_fallthrough_stack, hmem3, hd64] at rd4
        change RD fork (deployedRuntime v) ee g s0 ⟨7467⟩
          (src::memLoad (src+UInt256.ofNat 96) m3::ending::dst::ret::R) m3 aw4 out σ k4 C4 at rd4
        rw [hr3] at rd4
        have hm : schemaFieldsMemory mem src dst = m3 := by
          simp only [schemaFieldsMemory,writeWordSequence,Nat.add_assoc]; rfl
        rw [hm]
        exact rd4
      · have hc1 : UInt256.gt (memLoad (src+UInt256.ofNat 96) m3) (UInt256.ofNat 18446744073709551615) ≠ ⟨0⟩ := by
          rw [hr3,ugt_one (by change 18446744073709551615 < offset.toNat; change ¬ offset.toNat ≤ 18446744073709551615 at hoff; omega)]; decide
        obtain ⟨aw4,k4,C4,rd4⟩ := easBlocks.eas_block_7440_taken_packed (immWords := wordsOf (immStore v))
          (by simp only [List.length_cons]; omega) (by simpa only [hd64] using hc1)
          (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd3
        rw [if_neg (by intro h; exact hoff h.2.2)]
        exact easBlocks.eas_block_402 (immWords := wordsOf (immStore v))
          (by simp only [easBlocks.eas_block_7440_taken_stack,List.length_cons]; omega) rd4
    · rw [if_neg hrev] at hr
      rw [if_neg (by intro h; exact hrev h.2.1)]
      exact hr
  · have hc : UInt256.sub (memLoad (src+UInt256.ofNat 32) m1)
        (UInt256.land (memLoad (src+UInt256.ofNat 32) m1) solcAddrMask) ≠ ⟨0⟩ := by
      rw [hr1]
      apply u256_sub_ne_zero_of_ne
      intro he
      exact ha (he ▸ solcAddrMask_result_canonical resolver)
    obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_7385_taken_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) hc (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    rw [if_neg (by intro h; exact ha h.1)]
    exact easBlocks.eas_block_402 (immWords := wordsOf (immStore v))
      (by simp only [easBlocks.eas_block_7385_taken_stack,List.length_cons]; omega) rd1

end Benchmarks.EAS.EAS
