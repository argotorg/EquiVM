import Benchmarks.EAS.EAS.RevokeArrayStore

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def revokeValuesLogMemory (mem : ByteArray) (site : RevokeSite) (heap value word : UInt256) (i : Nat) : ByteArray :=
  Reasoning.Theory.writeWord (Reasoning.Theory.writeWord mem (site.values.toNat+32+32*i) value) heap.toNat word

theorem easRevokeValuesLog {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C i : Nat}
    {cell request word value heap : UInt256} {R : List UInt256} (v : EASImmutables) (site : RevokeSite)
    (hstack : R.length+26 ≤ 1024) (hperm : ee.perm = true) (hi : i < site.length)
    (hb : site.values.toNat+32+32*site.length < UInt256.size)
    (hin : site.values.toNat+32 ≤ mem.size) (hlo : 96 ≤ site.values.toNat)
    (hl : memLoad site.values mem = UInt256.ofNat site.length)
    (hr : request.toNat+64 ≤ site.values.toNat)
    (hu : memLoad request mem = word) (hv : memLoad (request+UInt256.ofNat 32) mem = value)
    (hh : memLoad (UInt256.ofNat 64) mem = heap)
    (rd : RD fork (deployedRuntime v) ee g s0 site.kind.valuesPC
      (revokeValuesStack site ee cell request (UInt256.ofNat i) word R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 site.kind.loopPC (revokeLoopStack site ee (UInt256.ofNat (i+1)) R)
      (revokeValuesLogMemory mem site heap value word i) aw' rdata σ k' C' := by
  let m := Reasoning.Theory.writeWord mem (site.values.toNat+32+32*i) value
  have hcell : (UInt256.ofNat (site.values.toNat+32+32*i)).toNat = site.values.toNat+32+32*i := ulit_toNat' _ (by omega)
  have hu' : memLoad request m = word := (memLoad_write_below _ _ _ _ (by omega) (by omega)).trans hu
  have hh' : memLoad (UInt256.ofNat 64) m = heap := (memLoad_write_below _ _ _ _ (by change 64+32 ≤ _; omega) (by change 64+32 ≤ _; omega)).trans hh
  have hinc : UInt256.ofNat i+(⟨1⟩ : UInt256) = UInt256.ofNat (i+1) :=
    (u256_add_comm _ _).trans (u256_one_add_ofNat i)
  have hv32 : memLoad (request+(⟨32⟩ : UInt256)) mem = value := hv
  cases hk : site.kind with
  | single =>
    simp only [revokeValuesStack,hk,RevokeKind.valuesPC,List.cons_append,List.nil_append] at rd
    obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_12595_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    simp only [easBlocks.eas_block_12595_stack,hv32] at rd1
    obtain ⟨aw2,k2,C2,rd2⟩ := easMemoryArrayIndex v (by simp only [List.length_cons]; omega) hi (by omega) (by omega) hl
      (by rw [easPatchedValidJumps v]; jump_dest) rd1
    obtain ⟨aw3,k3,C3,rd3⟩ := easBlocks.eas_block_12610_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) hperm (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd2
    have hm : easBlocks.eas_block_12610_memory (mem := mem)
        (x0 := UInt256.ofNat (site.values.toNat+32+32*i)) (x1 := value) (x7 := request) =
        revokeValuesLogMemory mem site heap value word i := by
      simp only [easBlocks.eas_block_12610_memory,hcell]
      change Reasoning.Theory.writeWord m (memLoad (UInt256.ofNat 64) m).toNat (memLoad request m) = _
      rw [hh',hu']; rfl
    exact ⟨aw3,k3,C3,by simpa only [easBlocks.eas_block_12610_stack,hinc,hm,revokeLoopStack,revokeGuardTail,revokeGuardRest,
      hk,RevokeKind.loopPC,List.cons_append,List.nil_append] using rd3⟩
  | many =>
    simp only [revokeValuesStack,hk,RevokeKind.valuesPC,List.cons_append,List.nil_append] at rd
    obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_13165_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    simp only [easBlocks.eas_block_13165_stack,hv] at rd1
    obtain ⟨aw2,k2,C2,rd2⟩ := easMemoryArrayIndex v (by simp only [List.length_cons]; omega) hi (by omega) (by omega) hl
      (by rw [easPatchedValidJumps v]; jump_dest) rd1
    obtain ⟨aw3,k3,C3,rd3⟩ := easBlocks.eas_block_13181_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) hperm (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd2
    have hm : easBlocks.eas_block_13181_memory (mem := mem)
        (x0 := UInt256.ofNat (site.values.toNat+32+32*i)) (x1 := value) (x3 := request) =
        revokeValuesLogMemory mem site heap value word i := by
      simp only [easBlocks.eas_block_13181_memory,hcell]
      change Reasoning.Theory.writeWord m (memLoad (UInt256.ofNat 64) m).toNat (memLoad request m) = _
      rw [hh',hu']; rfl
    exact ⟨aw3,k3,C3,by simpa only [easBlocks.eas_block_13181_stack,hinc,hm,revokeLoopStack,revokeGuardTail,revokeGuardRest,
      hk,RevokeKind.loopPC,List.cons_append,List.nil_append] using rd3⟩

end Benchmarks.EAS.EAS
