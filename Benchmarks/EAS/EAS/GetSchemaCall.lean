import Benchmarks.EAS.EAS.SchemaResult
import Benchmarks.EAS.EAS.GetSchemaBody

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem getSchemaCallRun {locals : Store} {args : List Expr} {retVar : Ident}
    {evm : EVM.State} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw gasArg ptr uid : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (v : EASImmutables) (site : SchemaCallSite)
    (he : evalExprs? config {contract := contract, locals := locals, immutables := immStore v} evm args =
      .ok [wordBytes32Value uid,.int (Int.ofNat ptr.toNat)])
    (hstack : R.length+20 ≤ 1024) (hs : SourceState s0 ee σ evm)
    (hlo : 96 ≤ ptr.toNat) (hptr : ptr.toNat ≤ 2^64-1) (hin : ptr.toNat ≤ mem.size)
    (hcd : mem.readWithPadding ptr.toNat 36 = getSchemaPayload uid)
    (rd : RD fork (deployedRuntime v) ee g s0 (schemaCallPC site)
      (gasArg::UInt256.land (EVM.word v._schemaRegistry.val) solcAddrMask::ptr::⟨36⟩::ptr::⟨0⟩::schemaCallSaved site ptr R)
      mem aw rdata σ k C) :
    (∃ (a : SchemaRecord) (record : UInt256) (heap : Nat) (evm' : EVM.State) (σ' : AccountMap)
        (mem' out : ByteArray) (aw' : UInt256) (k' C' : Nat),
      SourceState s0 ee σ' evm' ∧ ptr.toNat ≤ heap ∧ heap ≤ 2^64-1 ∧ ptr.toNat ≤ record.toNat ∧ record.toNat+128 ≤ heap ∧
      MemoryPrefix mem mem' ptr.toNat ∧ SchemaMemoryView mem' record a ∧
      memLoad (UInt256.ofNat 64) mem' = UInt256.ofNat heap ∧
      ExecStmt fork config {contract := contract, locals := locals, immutables := immStore v} evm
        (.internalCall "_getSchema" args retVar)
        (.ok (resumeAfterInternalCall {contract := contract, locals := locals, immutables := immStore v}
          retVar (some [a.value,.int (Int.ofNat heap)])) evm') ∧
      RD fork (deployedRuntime v) ee g s0 (schemaDonePC site) (schemaDoneStack v site record R) mem' aw' out σ' k' C') ∨
    (ExecStmt fork config {contract := contract, locals := locals, immutables := immStore v} evm
      (.internalCall "_getSchema" args retVar) .reverted ∧ RDrev fork (deployedRuntime v) g s0) := by
  obtain ⟨evm',σ',success,out,aw1,k1,C1,hcall,hs',hout,rd1⟩ := schemaStaticcall v site
    (by cases site <;> simp only [schemaCallSaved,List.length_cons] <;> omega) hs hcd rd
  have hr := schemaCallResult v site success hstack hlo hptr hin hout rd1
  have hsrc := getSchemaBodySource (heap := ptr.toNat) v hcall (by omega)
  by_cases hv : schemaCallValid ptr.toNat success out
  · rw [if_pos hv] at hr hsrc
    obtain ⟨mem',aw2,k2,C2,rd2,hprefix,hview,hfree⟩ := hr
    obtain ⟨locals',hbody⟩ := hsrc
    have hexe := internalCallFunctionReturn (retVar := retVar) he getSchema_lookup (getSchema_bind uid ptr.toNat) hbody
    have hnext : schemaDecodeHeap ptr.toNat out = schemaCopyHeap ptr.toNat out+128 := allocateNext_128 hv.2.1.1
    have hn : (UInt256.ofNat (schemaCopyHeap ptr.toNat out)).toNat = schemaCopyHeap ptr.toNat out :=
      ulit_toNat' _ (by change schemaCopyHeap ptr.toNat out < 2^256; have := hv.2.1.1; omega)
    refine Or.inl ⟨decodedSchemaRecord out (schemaReturnOffset out),UInt256.ofNat (schemaCopyHeap ptr.toNat out),
      schemaFinalHeap ptr.toNat out,evm',σ',mem',out,aw2,k2,C2,hs',?_,hv.2.2.2.2.1,?_,?_,hprefix,hview,hfree,hexe,rd2⟩
    · exact le_trans hv.2.1.2 (le_trans hv.2.2.1.2 hv.2.2.2.2.2)
    · rw [hn]; exact hv.2.1.2
    · rw [hn,← hnext]
      exact hv.2.2.2.2.2
  · rw [if_neg hv] at hr hsrc
    exact Or.inr ⟨internalCallFunctionRevert he getSchema_lookup (getSchema_bind uid ptr.toNat) hsrc,hr⟩

end Benchmarks.EAS.EAS
