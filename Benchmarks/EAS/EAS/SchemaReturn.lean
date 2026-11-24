import Benchmarks.EAS.EAS.SchemaDecode
import Benchmarks.EAS.EAS.GetSchemaTail
import Benchmarks.EAS.EAS.RuntimeBlocks_033

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
set_option linter.constructorNameAsVariable false

-- LIBRARY CANDIDATE: copying a possibly empty ABI buffer preserves its complete words.
theorem ReturnMemoryView.copyAny (mem out : ByteArray) (base : Nat)
    (hlo : 96 ≤ base) (hin : base ≤ mem.size) (hb : base+out.size < UInt256.size) :
    ReturnMemoryView (out.write 0 mem base out.size) base out := by
  by_cases hz : out.size=0
  · refine ⟨hlo,?_,?_⟩
    · simpa only [hz,byteArray_write_len_zero,Nat.add_zero] using hin
    · intro i hi; omega
  · exact ReturnMemoryView.copy _ _ _ hlo hin (by omega) hb

theorem easSchemaReturn {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {ptr ret : UInt256} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length+12 ≤ 1024) (hlo : 96 ≤ ptr.toNat) (hptr : ptr.toNat ≤ 2^64-1)
    (hin : ptr.toNat ≤ mem.size) (hout : out.size < 2^138)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨4883⟩
      (ptr::UInt256.ofNat out.size::⟨9829⟩::UInt256.ofNat out.size::ptr::ret::R)
      (out.write 0 mem ptr.toNat out.size) aw out σ k C) :
    if schemaCallValid ptr.toNat true out then
      ∃ mem' aw' k' C', RD fork (deployedRuntime v) ee g s0 ret (UInt256.ofNat (schemaCopyHeap ptr.toNat out)::R) mem' aw' out σ k' C' ∧
        MemoryPrefix mem mem' ptr.toNat ∧
        SchemaMemoryView mem' (UInt256.ofNat (schemaCopyHeap ptr.toNat out)) (decodedSchemaRecord out (schemaReturnOffset out)) ∧
        memLoad (UInt256.ofNat 64) mem' = UInt256.ofNat (schemaFinalHeap ptr.toNat out)
    else RDrev fork (deployedRuntime v) g s0 := by
  have ho : (UInt256.ofNat out.size).toNat = out.size := ulit_toNat' _ (by change out.size < 2^256; omega)
  by_cases hg : schemaCopyHeap ptr.toNat out ≤ 2^64-1 ∧ ptr.toNat ≤ schemaCopyHeap ptr.toNat out
  · obtain ⟨aw1,k1,C1,rd1⟩ := easAllocate_ok v (by simp only [List.length_cons]; omega)
      (by simpa only [ho] using hg) (by rw [easPatchedValidJumps v]; jump_dest) rd
    obtain ⟨aw2,k2,C2,rd2⟩ := easBlocks.eas_block_9829_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd1
    let record := UInt256.ofNat (schemaCopyHeap ptr.toNat out)
    have hn : record.toNat = schemaCopyHeap ptr.toNat out := ulit_toNat' _ (by change schemaCopyHeap ptr.toNat out < 2^256; omega)
    have hb : ptr.toNat+out.size < UInt256.size := by change ptr.toNat+out.size < 2^256; omega
    have hv := ReturnMemoryView.copyAny mem out ptr.toNat hlo hin hb
    have hdisj : ptr.toNat+out.size ≤ record.toNat := by
      rw [hn]
      change ptr.toNat+out.size ≤ allocateNext ptr.toNat out.size
      rw [allocateNext_small hptr hout]
      omega
    have hp := returnCopyMemory_prefix mem out ptr.toNat hin
    have hp1 : MemoryPrefix (out.write 0 mem ptr.toNat out.size)
        (Reasoning.Theory.writeWord (out.write 0 mem ptr.toNat out.size) 64 record) record.toNat :=
      memoryPrefix_sparse_writeWord _ _ _ _ (Or.inr (by decide))
    have hv1 := hv.preserve hp1 hdisj (by rw [hn]; change _ < 2^256; omega)
    simp only [easBlocks.eas_block_9829_stack,ho] at rd2
    have hr := easSchemaDecode v hstack hptr (by rw [hn]; exact hg.1) hout hv1 hdisj
      (writeWordSequence_setFree_load64 _ 96 [] record (le_refl _)) hvalid rd2
    have hi : (32 ≤ out.size ∧ schemaReturnOffset out ≤ solcMaxU64 ∧
        schemaBodyRunValid record.toNat out (schemaReturnOffset out)) ↔ schemaCallValid ptr.toNat true out := by
      rw [hn]
      constructor
      · rintro ⟨hhead,hoff,halloc,hbody,hfinal⟩
        exact ⟨rfl,hg,halloc,⟨hhead,hoff,hbody⟩,hfinal⟩
      · intro h
        exact ⟨h.2.2.2.1.1,h.2.2.2.1.2.1,h.2.2.1,h.2.2.2.1.2.2,h.2.2.2.2⟩
    simp only [hi] at hr
    by_cases hs : schemaCallValid ptr.toNat true out
    · rw [if_pos hs] at hr ⊢
      obtain ⟨mem',aw3,k3,C3,rd3,hp3,hview,hfree⟩ := hr
      refine ⟨mem',aw3,k3,C3,rd3,hp.trans ((hp1.trans hp3).mono (by rw [hn]; exact hg.2)),hview,?_⟩
      simpa only [schemaBodyNext,hn,schemaFinalHeap,schemaDecodeHeap] using hfree
    · rw [if_neg hs] at hr ⊢
      exact hr
  · rw [if_neg (by intro h; exact hg h.2.1)]
    exact easAllocate_revert v (by simp only [List.length_cons]; omega) (by simpa only [ho] using hg) rd

end Benchmarks.EAS.EAS
