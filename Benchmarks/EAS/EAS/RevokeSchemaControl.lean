import Benchmarks.EAS.EAS.RevokeArraysControl
import Benchmarks.EAS.EAS.SchemaUIDCheck

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def RevokeKind.schemaSite : RevokeKind → SchemaCallSite | .single => .at12196 | .many => .at12855
def RevokeKind.entryPC : RevokeKind → UInt256 | .single => ⟨12085⟩ | .many => ⟨12743⟩
def revokeEntryStack (kind : RevokeKind) (schema data revoker available last ret : UInt256) (R : List UInt256) : List UInt256 :=
  match kind with
  | .single => schema::data::revoker::available::ret::R
  | .many => schema::data::revoker::available::last::ret::R

def revokeSchemaSaved (kind : RevokeKind) (schema data revoker available last ret : UInt256) (R : List UInt256) : List UInt256 :=
  match kind with
  | .single => revoker::schema::available::ret::data::R
  | .many => revoker::schema::available::last::ret::data::R

theorem easRevokeSchemaPrepare {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {schema data revoker available last ret heap : UInt256} {R : List UInt256}
    (v : EASImmutables) (kind : RevokeKind) (hstack : R.length+13 ≤ 1024)
    (hb : heap.toNat+4 < UInt256.size) (hh : memLoad (UInt256.ofNat 64) mem = heap)
    (rd : RD fork (deployedRuntime v) ee g s0 kind.entryPC
      (revokeEntryStack kind schema data revoker available last ret R) mem aw rdata σ k C) :
    ∃ gasArg aw' k' C', RD fork (deployedRuntime v) ee g s0 (schemaCallPC kind.schemaSite)
      (gasArg::UInt256.land (EVM.word v._schemaRegistry.val) solcAddrMask::heap::⟨36⟩::heap::⟨0⟩::
        schemaCallSaved kind.schemaSite heap (revokeSchemaSaved kind schema data revoker available last ret R))
      (getSchemaCallMemory mem heap schema) aw' rdata σ k' C' := by
  have ho := uadd_word_ofNat_toNat heap 4 hb
  cases kind with
  | single =>
    obtain ⟨a,j,D,hr⟩ := easBlocks.eas_block_12085_packed (immWords := wordsOf (immStore v)) (by omega) rd
    let gasArg := (easBlocks.eas_block_12085_stack (immWords := wordsOf (immStore v))
      (g := g) (mem := mem) (aw := aw) (C := C) (x0 := schema) (x1 := data) (x2 := revoker)
      (x3 := available) (x4 := ret) (R := R)).head!
    exact ⟨gasArg,a,j,D,by simpa only [gasArg,List.head!_cons,easBlocks.eas_block_12085_stack,easBlocks.eas_block_12085_memory,
      hh,ho,wordsOf_immStore__schemaRegistry,getSchemaCallMemory,selectorArgumentMemory,Reasoning.Theory.writeWord] using hr⟩
  | many =>
    obtain ⟨a,j,D,hr⟩ := easBlocks.eas_block_12743_packed (immWords := wordsOf (immStore v)) hstack rd
    let gasArg := (easBlocks.eas_block_12743_stack (immWords := wordsOf (immStore v))
      (g := g) (mem := mem) (aw := aw) (C := C) (x0 := schema) (x1 := data) (x2 := revoker)
      (x3 := available) (x4 := last) (x5 := ret) (R := R)).head!
    exact ⟨gasArg,a,j,D,by simpa only [gasArg,List.head!_cons,easBlocks.eas_block_12743_stack,easBlocks.eas_block_12743_memory,
      hh,ho,wordsOf_immStore__schemaRegistry,getSchemaCallMemory,selectorArgumentMemory,Reasoning.Theory.writeWord] using hr⟩

end Benchmarks.EAS.EAS
