import Benchmarks.EAS.EAS.RevokeLayout
import Benchmarks.EAS.EAS.ArrayStoreIndex

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def RevokeKind.valuesPC : RevokeKind → UInt256 | .single => ⟨12595⟩ | .many => ⟨13165⟩
def revokeValuesStack (site : RevokeSite) (ee : ExecutionEnv) (cell request idx word : UInt256) (R : List UInt256) : List UInt256 :=
  match site.kind with
  | .single => [cell,site.values,dbSlot word,⟨4⟩,solcAddrMask,⟨32⟩,revokedTopic,request,UInt256.ofNat site.revoker.val,
      dbSlot word+⟨1⟩,idx,⟨1⟩,UInt256.ofNat site.revoker.val,site.schema,UInt256.ofNat site.length,
      easTimeWord ee,site.schemaPtr,site.records,site.values,site.available,site.ret,site.data] ++ R
  | .many => [cell,dbSlot word,request,idx,⟨1⟩,site.schema,UInt256.ofNat site.revoker.val,UInt256.ofNat site.length,
      site.schemaPtr,site.records,site.values,site.available,site.last.toUInt256,site.ret,site.data] ++ R

theorem easRevokeArrayStore {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C i : Nat}
    {src request word : UInt256} {R : List UInt256} (v : EASImmutables) (site : RevokeSite)
    (hstack : R.length+30 ≤ 1024) (hi : i < site.length)
    (hb : site.records.toNat+32+32*site.length < UInt256.size)
    (hin : site.records.toNat+32+32*site.length ≤ mem.size)
    (hl : memLoad site.records mem = UInt256.ofNat site.length)
    (rd : RD fork (deployedRuntime v) ee g s0 site.kind.copyReturnPC
      (src::revokeCopySaved site ee request (UInt256.ofNat i) word R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 site.kind.valuesPC
      (revokeValuesStack site ee (UInt256.ofNat (site.records.toNat+32+32*i)) request (UInt256.ofNat i) word R)
      (Reasoning.Theory.writeWord mem (site.records.toNat+32+32*i) src) aw' rdata σ k' C' := by
  have hcell : (UInt256.ofNat (site.records.toNat+32+32*i)).toNat = site.records.toNat+32+32*i := ulit_toNat' _ (by omega)
  have hl' : memLoad site.records (Reasoning.Theory.writeWord mem (site.records.toNat+32+32*i) src) = UInt256.ofNat site.length :=
    (memLoad_write_below _ _ _ _ (by omega) (by omega)).trans hl
  cases hk : site.kind with
  | single =>
    simp only [revokeCopySaved,hk,RevokeKind.copyReturnPC,List.cons_append,List.nil_append] at rd
    obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_12585_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    obtain ⟨aw2,k2,C2,rd2⟩ := easArrayStoreIndex v (by simp only [List.length_cons]; omega) hi hb hin hl
      (by rw [easPatchedValidJumps v]; jump_dest) rd1
    exact ⟨aw2,k2,C2,by simpa only [hk,RevokeKind.valuesPC,revokeValuesStack] using rd2⟩
  | many =>
    simp only [revokeCopySaved,hk,RevokeKind.copyReturnPC,List.cons_append,List.nil_append] at rd
    obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_13144_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    obtain ⟨aw2,k2,C2,rd2⟩ := easMemoryArrayIndex v
      (by simp only [List.length_cons]; omega) hi (by omega) (by omega) hl
      (by rw [easPatchedValidJumps v]; jump_dest) rd1
    obtain ⟨aw3,k3,C3,rd3⟩ := easBlocks.eas_block_13154_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd2
    simp only [easBlocks.eas_block_13154_stack,easBlocks.eas_block_13154_memory,hcell] at rd3
    obtain ⟨aw4,k4,C4,rd4⟩ := easMemoryArrayIndex v
      (by simp only [List.length_cons]; omega) hi (by omega) (by omega) hl'
      (by rw [easPatchedValidJumps v]; jump_dest) rd3
    exact ⟨aw4,k4,C4,by simpa only [hk,RevokeKind.valuesPC,revokeValuesStack] using rd4⟩

end Benchmarks.EAS.EAS
