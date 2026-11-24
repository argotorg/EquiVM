import Benchmarks.EAS.EAS.SchemaMemory
import Benchmarks.EAS.EAS.SchemaBuffer
import Benchmarks.EAS.EAS.SchemaTextHead
import Benchmarks.EAS.EAS.Allocate128
import Benchmarks.EAS.EAS.AllocateBounds

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000
set_option linter.constructorNameAsVariable false

def schemaBodyNext (heap : Nat) (out : ByteArray) (base : Nat) : Nat :=
  allocateNext (allocateNext heap 128) (bytesAllocation (schemaTextLength out base))
def schemaBodyRunValid (heap : Nat) (out : ByteArray) (base : Nat) : Prop :=
  (allocateNext heap 128 ≤ 2^64-1 ∧ heap ≤ allocateNext heap 128) ∧ schemaBodyValid out base ∧
  (schemaBodyNext heap out base ≤ 2^64-1 ∧ allocateNext heap 128 ≤ schemaBodyNext heap out base)
instance (heap : Nat) (out : ByteArray) (base : Nat) : Decidable (schemaBodyRunValid heap out base) := by
  unfold schemaBodyRunValid; infer_instance

theorem easSchemaBody {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {ptr record ret : UInt256} {base : Nat} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length+12 ≤ 1024) (hptr : ptr.toNat ≤ 2^64-1) (hrec : record.toNat ≤ 2^64-1)
    (hout : out.size < 2^138) (hbase : base ≤ solcMaxU64) (hhead : base+128 ≤ out.size)
    (hv : ReturnMemoryView mem ptr.toNat out) (hdisj : ptr.toNat+out.size ≤ record.toNat)
    (hh : memLoad (UInt256.ofNat 64) mem = record)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨7373⟩
      ((ptr+UInt256.ofNat out.size)::(ptr+UInt256.ofNat base)::ret::R) mem aw out σ k C) :
    if schemaBodyRunValid record.toNat out base then
      ∃ mem' aw' k' C', RD fork (deployedRuntime v) ee g s0 ret (record::R) mem' aw' out σ k' C' ∧
        MemoryPrefix mem mem' record.toNat ∧ SchemaMemoryView mem' record (decodedSchemaRecord out base) ∧
        memLoad (UInt256.ofNat 64) mem' = UInt256.ofNat (schemaBodyNext record.toNat out base)
    else RDrev fork (deployedRuntime v) g s0 := by
  let src := ptr+UInt256.ofNat base
  let ending := ptr+UInt256.ofNat out.size
  let next := allocateNext record.toNat 128
  have hs : src.toNat = ptr.toNat+base := uadd_word_ofNat_toNat ptr base (by change ptr.toNat+base < 2^256; change base ≤ 2^64-1 at hbase; omega)
  have he : ending.toNat = ptr.toNat+out.size := uadd_word_ofNat_toNat ptr out.size (by change ptr.toNat+out.size < 2^256; omega)
  have hlo : 96 ≤ record.toNat := by have := hv.low; omega
  have hb : record.toNat+128 < UInt256.size := by change record.toNat+128 < 2^256; omega
  obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_7373_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
  simp only [easBlocks.eas_block_7373_stack,hh] at rd1
  have hr := easAllocate128 v (by simp only [List.length_cons]; omega)
    (by rw [easPatchedValidJumps v]; jump_dest) rd1
  by_cases hg : next ≤ 2^64-1 ∧ record.toNat ≤ next
  · rw [if_pos hg] at hr
    obtain ⟨aw2,k2,C2,rd2⟩ := hr
    let m1 := Reasoning.Theory.writeWord mem 64 (UInt256.ofNat next)
    have hn : (UInt256.ofNat next).toNat = next := ulit_toNat' _ (by change next < 2^256; omega)
    have hnext : next = record.toNat+128 := allocateNext_128 hrec
    have hp1 : MemoryPrefix mem m1 record.toNat := memoryPrefix_sparse_writeWord _ _ _ _ (Or.inr (by decide))
    have hv1 : ReturnMemoryView m1 ptr.toNat out := hv.preserve hp1 hdisj (by omega)
    have words (n : Nat) (hn' : n ≤ 96) : memLoad (src+UInt256.ofNat n) m1 = calldataWord out (base+n) := by
      apply hv1.load
      · rw [uadd_word_ofNat_toNat src n (by rw [hs]; omega),hs]; omega
      · omega
    change RD fork (deployedRuntime v) ee g s0 ⟨7385⟩ (src::ending::record::ret::R) m1 aw2 out σ k2 C2 at rd2
    have hfields := easSchemaFields v (by omega) (by rw [hs]; have := hv.low; omega)
      (by rw [hs]; have := hv1.covered; omega) (by rw [hs]; omega) hb rd2
    simp only [words 32 (by decide),words 64 (by decide),words 96 (by decide),boolWord_nat_iff] at hfields
    by_cases hf : (calldataWord out (base+32)).toNat < EVM.addressModulus ∧
        ((calldataWord out (base+64)).toNat=0 ∨ (calldataWord out (base+64)).toNat=1) ∧
        (calldataWord out (base+96)).toNat ≤ solcMaxU64
    · rw [if_pos hf] at hfields
      obtain ⟨aw3,k3,C3,rd3⟩ := hfields
      let m2 := schemaFieldsMemory m1 src record
      have hp2 : MemoryPrefix m1 m2 record.toNat := schemaFieldsMemory_prefix _ _ _
      have hv2 : ReturnMemoryView m2 ptr.toNat out := hv1.preserve hp2 hdisj (by omega)
      let text := src+calldataWord out (base+96)
      have ht : text.toNat = ptr.toNat+schemaTextStart out base := by
        have ho := hf.2.2
        change (calldataWord out (base+96)).toNat ≤ 2^64-1 at ho
        dsimp only [text]
        rw [uadd_toNat,hs,Nat.mod_eq_of_lt (by change ptr.toNat+base+(calldataWord out (base+96)).toNat < 2^256; change base ≤ 2^64-1 at hbase; omega)]
        unfold schemaTextStart
        omega
      have hth := easSchemaTextHead v (by simp only [List.length_cons]; omega)
        (by rw [hs]; change base ≤ 2^64-1 at hbase; have ho := hf.2.2; change _ ≤ 2^64-1 at ho; omega)
        (by rw [he]; omega) rd3
      have hthiff : src.toNat+(calldataWord out (base+96)).toNat+32 ≤ ending.toNat ↔
          schemaTextStart out base+32 ≤ out.size := by rw [hs,he]; unfold schemaTextStart; omega
      simp only [hthiff] at hth
      by_cases htext : schemaTextStart out base+32 ≤ out.size
      · rw [if_pos htext] at hth
        obtain ⟨aw4,k4,C4,rd4⟩ := hth
        change RD fork (deployedRuntime v) ee g s0 ⟨7479⟩ (text::ending::record::ret::R) m2 aw4 out σ k4 C4 at rd4
        have hlen : memLoad text m2 = calldataWord out (schemaTextStart out base) := hv2.load ht htext
        have hfree : memLoad (UInt256.ofNat 64) m2 = UInt256.ofNat next := schemaFieldsMemory_heap mem src record _ hlo
        have htextSmall : text.toNat < 2^140 := by rw [ht]; omega
        have hrtext := easSchemaText v (by omega) htextSmall (by rw [hn]; exact hg.1) hlen hfree hvalid rd4
        simp only [hn,ht,he] at hrtext
        have hlastiff :
            ((calldataWord out (schemaTextStart out base)).toNat ≤ 2^64-1 ∧
              (allocateNext next (bytesAllocation (calldataWord out (schemaTextStart out base)).toNat) ≤ 2^64-1 ∧
                next ≤ allocateNext next (bytesAllocation (calldataWord out (schemaTextStart out base)).toNat)) ∧
              ptr.toNat+schemaTextStart out base+(calldataWord out (schemaTextStart out base)).toNat+32 ≤ ptr.toNat+out.size) ↔
            schemaBodyRunValid record.toNat out base := by
          unfold schemaBodyRunValid schemaBodyValid schemaBodyNext schemaTextLength
          change base ≤ 2^64-1 at hbase
          change (next ≤ 2^64-1 ∧ record.toNat ≤ next) at hg
          change _ ↔ (next ≤ 2^64-1 ∧ record.toNat ≤ next) ∧ _ ∧ _
          simp only [hg,hhead,hf.1,hf.2.1,hf.2.2,htext,true_and]
          unfold solcMaxU64
          dsimp only [next]
          omega
        simp only [hlastiff] at hrtext
        by_cases hvall : schemaBodyRunValid record.toNat out base
        · rw [if_pos hvall] at hrtext ⊢
          obtain ⟨aw5,k5,C5,rd5⟩ := hrtext
          have hviews := schemaFieldsTextMemory_views m1 src record text (UInt256.ofNat next)
            (calldataWord out (schemaTextStart out base)) (decodedSchemaRecord out base) hlo
            (by rw [hn,hnext]) (by rw [hn]; exact hg.1) hvall.2.1.2.2.2.2.2.1
            (by simpa only [show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl,u256_add_zero,Nat.add_zero] using words 0 (by decide))
            (by rw [words 32 (by decide)]; exact (addressWord_eq_ofNat_address hf.1).symm)
            (by rw [words 64 (by decide)]; exact (boolWord_from_nat _ hf.2.1).symm)
          refine ⟨_,aw5,k5,C5,rd5,hp1.trans hviews.1,hviews.2.1,?_⟩
          simpa only [hn,schemaBodyNext,schemaTextLength] using hviews.2.2
        · rw [if_neg hvall] at hrtext ⊢
          exact hrtext
      · rw [if_neg htext] at hth
        rw [if_neg (by intro h; exact htext h.2.1.2.2.2.2.1)]
        exact hth
    · rw [if_neg hf] at hfields
      rw [if_neg (by intro h; exact hf ⟨h.2.1.2.1,h.2.1.2.2.1,h.2.1.2.2.2.1⟩)]
      exact hfields
  · rw [if_neg hg] at hr
    rw [if_neg (by intro h; exact hg h.1)]
    exact hr

end Benchmarks.EAS.EAS
