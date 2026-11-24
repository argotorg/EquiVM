import Benchmarks.EAS.EAS.AttestResultAllocate
import Benchmarks.EAS.EAS.AttestUIDMemory

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def AttestCallKind.entryPC : AttestCallKind → UInt256
  | .single => ⟨7650⟩ | .many => ⟨9856⟩
def AttestCallKind.uidReturn : AttestCallKind → UInt256
  | .single => ⟨7682⟩ | .many => ⟨9901⟩
def attestEntryStack (kind : AttestCallKind) (schema data attester available last ret : UInt256) (R : List UInt256) : List UInt256 :=
  match kind with
  | .single => schema::data::attester::available::ret::R
  | .many => schema::data::attester::available::last::ret::R

def attestEntryMemory (kind : AttestCallKind) (mem : ByteArray) (data attester : UInt256) : ByteArray :=
  match kind with
  | .single => mem
  | .many => Reasoning.Theory.writeWord (Reasoning.Theory.writeWord mem 192 data) 160 attester

def attestResultRegisterMemory (kind : AttestCallKind) (mem : ByteArray) (result : UInt256) : ByteArray :=
  match kind with
  | .single => mem | .many => Reasoning.Theory.writeWord mem 128 result

def attestUIDSaved (kind : AttestCallKind) (schema data attester available last ret len result : UInt256) (R : List UInt256) : List UInt256 :=
  match kind with
  | .single => len::schema::attester::data::available::result::ret::R
  | .many => schema::available::last::ret::len::R

def attestCallSchemaSite (kind : AttestCallKind) (schema available last ret len : UInt256) : SchemaCallSite :=
  match kind with
  | .single => .at7795 schema len | .many => .at10016 len schema available last ret

def attestCallSchemaSaved (kind : AttestCallKind) (data attester available ret result : UInt256) (R : List UInt256) : List UInt256 :=
  match kind with
  | .single => attester::data::available::result::ret::R | .many => R

theorem easAttestEntry {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {schema data attester available last ret : UInt256} {R : List UInt256}
    (v : EASImmutables) (kind : AttestCallKind) (hstack : R.length+7 ≤ 1024)
    (rd : RD fork (deployedRuntime v) ee g s0 kind.entryPC (attestEntryStack kind schema data attester available last ret R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨7214⟩
      (kind.firstReturn::attestFirstSaved kind schema data attester available last ret R)
      (attestEntryMemory kind mem data attester) aw' rdata σ k' C' := by
  have hd : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 7214) = true := by rw [easPatchedValidJumps v]; jump_dest
  cases kind with
  | single => exact easBlocks.eas_block_7650_packed (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) hd rd
  | many => exact easBlocks.eas_block_9856_packed (immWords := wordsOf (immStore v)) hstack hd rd

theorem easAttestUIDPrepare {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {schema data attester available last ret len result : UInt256} {R : List UInt256}
    (v : EASImmutables) (kind : AttestCallKind) (hstack : R.length+10 ≤ 1024)
    (rd : RD fork (deployedRuntime v) ee g s0 kind.secondReturn
      (result::attestSecondSaved kind schema data attester available last ret len R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨7240⟩
      (len::kind.uidReturn::attestUIDSaved kind schema data attester available last ret len result R)
      (attestResultRegisterMemory kind mem result) aw' rdata σ k' C' := by
  have hd : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 7240) = true := by rw [easPatchedValidJumps v]; jump_dest
  cases kind with
  | single => exact easBlocks.eas_block_7672_packed (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) hd rd
  | many => exact easBlocks.eas_block_9889_packed (immWords := wordsOf (immStore v)) (by omega) hd rd

set_option maxHeartbeats 1000000 in
theorem easAttestSchemaPrepare {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {schema data attester available last ret len result uidPtr heap : UInt256} {R : List UInt256}
    (v : EASImmutables) (kind : AttestCallKind) (hstack : R.length+14 ≤ 1024)
    (hr : 96 ≤ result.toNat) (hs : result.toNat+64 ≤ heap.toNat) (hh : heap.toNat ≤ 2^64-1)
    (hsize : 96 ≤ mem.size) (hheap : memLoad (UInt256.ofNat 64) mem = heap)
    (hreg : kind = .many → memLoad (UInt256.ofNat 128) mem = result)
    (rd : RD fork (deployedRuntime v) ee g s0 kind.uidReturn
      (uidPtr::attestUIDSaved kind schema data attester available last ret len result R) mem aw rdata σ k C) :
    ∃ gasArg aw' k' C', RD fork (deployedRuntime v) ee g s0
      (schemaCallPC (attestCallSchemaSite kind schema available last ret len))
      (gasArg::UInt256.land (EVM.word v._schemaRegistry.val) solcAddrMask::heap::⟨36⟩::heap::⟨0⟩::
        schemaCallSaved (attestCallSchemaSite kind schema available last ret len) heap
          (attestCallSchemaSaved kind data attester available ret result R))
      (getSchemaCallMemory (Reasoning.Theory.writeWord mem (result.toNat+32) uidPtr) heap schema) aw' rdata σ k' C' := by
  have hn : (result+UInt256.ofNat 32).toNat = result.toNat+32 := uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)
  have hh4 : (heap+UInt256.ofNat 4).toNat = heap.toNat+4 := uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)
  have hp : memLoad (UInt256.ofNat 64) (uidPtr.toByteArray.write 0 mem (result+UInt256.ofNat 32).toNat 32) = heap := by
    rw [hn]
    exact (memLoad_write_below mem (result.toNat+32) (UInt256.ofNat 64) uidPtr (by change 96 ≤ result.toNat+32; omega) hsize).trans hheap
  have hp' : memLoad (UInt256.ofNat 64) (uidPtr.toByteArray.write 0 mem (result.toNat+32) 32) = heap := by
    simpa only [hn] using hp
  cases kind with
  | single =>
    obtain ⟨a,j,D,h⟩ := easBlocks.eas_block_7682_packed (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) rd
    let gasArg := (easBlocks.eas_block_7682_stack (immWords := wordsOf (immStore v))
      (g := g) (mem := mem) (aw := aw) (C := C) (x0 := uidPtr) (x1 := len) (x2 := schema)
      (x3 := attester) (x4 := data) (x5 := available) (x6 := result) (R := ret::R)).head!
    refine ⟨gasArg,a,j,D,?_⟩
    simpa only [gasArg,List.head!_cons,easBlocks.eas_block_7682_stack,easBlocks.eas_block_7682_memory,hp',wordsOf_immStore__schemaRegistry,
      getSchemaCallMemory,selectorArgumentMemory,Reasoning.Theory.writeWord,hn,hh4] using h
  | many =>
    obtain ⟨a,j,D,h⟩ := easBlocks.eas_block_9901_packed (immWords := wordsOf (immStore v)) (by omega) rd
    have hreg' := hreg rfl
    let gasArg := (easBlocks.eas_block_9901_stack (immWords := wordsOf (immStore v))
      (g := g) (mem := mem) (aw := aw) (C := C) (x0 := uidPtr) (x1 := schema)
      (x2 := available) (x3 := last) (x4 := ret) (x5 := len) (R := R)).head!
    refine ⟨gasArg,a,j,D,?_⟩
    simpa only [gasArg,List.head!_cons,easBlocks.eas_block_9901_stack,easBlocks.eas_block_9901_memory,hreg',hp',wordsOf_immStore__schemaRegistry,
      getSchemaCallMemory,selectorArgumentMemory,Reasoning.Theory.writeWord,hn,hh4] using h

end Benchmarks.EAS.EAS
