import Benchmarks.EAS.EAS.SchemaBody

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem easSchemaDecode {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {ptr record ret : UInt256} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length+12 ≤ 1024) (hptr : ptr.toNat ≤ 2^64-1) (hrec : record.toNat ≤ 2^64-1)
    (hout : out.size < 2^138) (hv : ReturnMemoryView mem ptr.toNat out)
    (hdisj : ptr.toNat+out.size ≤ record.toNat) (hh : memLoad (UInt256.ofNat 64) mem = record)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨7332⟩
      (ptr::(ptr+UInt256.ofNat out.size)::ret::R) mem aw out σ k C) :
    if 32 ≤ out.size ∧ schemaReturnOffset out ≤ solcMaxU64 ∧ schemaBodyRunValid record.toNat out (schemaReturnOffset out) then
      ∃ mem' aw' k' C', RD fork (deployedRuntime v) ee g s0 ret (record::R) mem' aw' out σ k' C' ∧
        MemoryPrefix mem mem' record.toNat ∧ SchemaMemoryView mem' record (decodedSchemaRecord out (schemaReturnOffset out)) ∧
        memLoad (UInt256.ofNat 64) mem' = UInt256.ofNat (schemaBodyNext record.toNat out (schemaReturnOffset out))
    else RDrev fork (deployedRuntime v) g s0 := by
  have hhead := easSchemaHead v (by omega) hptr hout
    (fun hw => hv.load (by omega : ptr.toNat=ptr.toNat+0) hw) rd
  by_cases hg : 32 ≤ out.size ∧ schemaReturnOffset out ≤ solcMaxU64 ∧ schemaReturnOffset out+128 ≤ out.size
  · rw [if_pos hg] at hhead
    obtain ⟨aw1,k1,C1,rd1⟩ := hhead
    have hr := easSchemaBody v hstack hptr hrec hout hg.2.1 hg.2.2 hv hdisj hh hvalid rd1
    simpa only [hg.1,hg.2.1,true_and] using hr
  · rw [if_neg hg] at hhead
    rw [if_neg (by intro h; exact hg ⟨h.1,h.2.1,h.2.2.2.1.1⟩)]
    exact hhead

end Benchmarks.EAS.EAS
