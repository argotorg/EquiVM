import Benchmarks.EAS.EAS.SchemaReturn
import Benchmarks.EAS.EAS.SchemaControl

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem schemaCallResult {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw ptr : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : EASImmutables) (site : SchemaCallSite) (success : Bool)
    (hstack : R.length+20 ≤ 1024) (hlo : 96 ≤ ptr.toNat) (hptr : ptr.toNat ≤ 2^64-1)
    (hin : ptr.toNat ≤ mem.size) (hout : out.size < 2^138)
    (rd : RD fork (deployedRuntime v) ee g s0 (schemaAfterCallPC site)
      ((if success then ⟨1⟩ else ⟨0⟩)::schemaCallSaved site ptr R) mem aw out σ k C) :
    if schemaCallValid ptr.toNat success out then
      ∃ mem' aw' k' C', RD fork (deployedRuntime v) ee g s0 (schemaDonePC site)
        (schemaDoneStack v site (UInt256.ofNat (schemaCopyHeap ptr.toNat out)) R) mem' aw' out σ k' C' ∧
        MemoryPrefix mem mem' ptr.toNat ∧
        SchemaMemoryView mem' (UInt256.ofNat (schemaCopyHeap ptr.toNat out)) (decodedSchemaRecord out (schemaReturnOffset out)) ∧
        memLoad (UInt256.ofNat 64) mem' = UInt256.ofNat (schemaFinalHeap ptr.toNat out)
    else RDrev fork (deployedRuntime v) g s0 := by
  have hr := schemaCallResultPrepare v site success (by omega) hout rd
  cases success with
  | false =>
    rw [if_neg (by intro h; cases h.1)]
    exact hr
  | true =>
    obtain ⟨aw1,k1,C1,rd1⟩ := hr
    have hd := easSchemaReturn v (by cases site <;> simp only [schemaDecodeSaved,List.length_cons] <;> omega)
      hlo hptr hin hout (schemaDecodeReturn_valid v site) rd1
    by_cases hv : schemaCallValid ptr.toNat true out
    · rw [if_pos hv] at hd ⊢
      obtain ⟨mem',aw2,k2,C2,rd2,hprefix,hview,hfree⟩ := hd
      obtain ⟨aw3,k3,C3,rd3⟩ := schemaCallResultFinish v site (by omega) rd2
      exact ⟨mem',aw3,k3,C3,rd3,hprefix,hview,hfree⟩
    · rw [if_neg hv] at hd ⊢
      exact hd

end Benchmarks.EAS.EAS
