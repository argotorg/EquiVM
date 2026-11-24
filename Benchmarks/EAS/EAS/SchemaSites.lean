import Benchmarks.EAS.EAS.StaticCallBridge
import Benchmarks.EAS.EAS.GetSchemaSource
import Benchmarks.EAS.EAS.CallMemory

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

inductive SchemaCallSite where
  | at7795 (a b : UInt256)
  | at10016 (a b c d e : UInt256)
  | at12196
  | at12855

def schemaCallPC : SchemaCallSite → UInt256
  | .at7795 .. => ⟨7795⟩
  | .at10016 .. => ⟨10016⟩
  | .at12196 => ⟨12196⟩
  | .at12855 => ⟨12855⟩
def schemaAfterCallPC : SchemaCallSite → UInt256
  | .at7795 .. => ⟨7796⟩
  | .at10016 .. => ⟨10017⟩
  | .at12196 => ⟨12197⟩
  | .at12855 => ⟨12856⟩
def schemaCallSaved (site : SchemaCallSite) (ptr : UInt256) (R : List UInt256) : List UInt256 :=
  match site with
  | .at7795 a b => a::b::ptr::R
  | .at10016 a b c d e => a::b::c::d::e::ptr::R
  | .at12196 | .at12855 => ptr::R

def getSchemaSelectorWord : UInt256 :=
  ⟨73688982465788432266081024889082741544416521440692999874815521305510878904320⟩
def getSchemaCallMemory (mem : ByteArray) (ptr uid : UInt256) : ByteArray :=
  selectorArgumentMemory mem ptr.toNat getSchemaSelectorWord uid

theorem getSchemaCallMemory_read (mem : ByteArray) (ptr uid : UInt256) :
    (getSchemaCallMemory mem ptr uid).readWithPadding ptr.toNat 36 = getSchemaPayload uid := by
  rw [getSchemaCallMemory,selectorArgumentMemory_read]
  have h : getSchemaSelectorWord.toByteArray.extract 0 4 = selectorBytes 0xa2 0xea 0x7c 0x6e := by decide +kernel
  rw [h]; rfl

theorem schemaCall_decode (v : EASImmutables) (site : SchemaCallSite) :
    decode (deployedRuntime v) (schemaCallPC site) = some (.STATICCALL,none) := by
  cases site with
  | at7795 a b =>
    change decode (immutableLayout.runtime easBytecode (wordsOf (immStore v))) (UInt256.ofNat 7795) = _
    immutable_decode(immutableLayout,easBytecode,wordsOf (immStore v),(⟨7795⟩ : UInt256),UInt8.ofNat 250,
      .STATICCALL,none,easBlocks.immutableLayout_inBounds,easBlocks.immutableTemplate_size64)
  | at10016 a b c d e =>
    change decode (immutableLayout.runtime easBytecode (wordsOf (immStore v))) (UInt256.ofNat 10016) = _
    immutable_decode(immutableLayout,easBytecode,wordsOf (immStore v),(⟨10016⟩ : UInt256),UInt8.ofNat 250,
      .STATICCALL,none,easBlocks.immutableLayout_inBounds,easBlocks.immutableTemplate_size64)
  | at12196 =>
    change decode (immutableLayout.runtime easBytecode (wordsOf (immStore v))) (UInt256.ofNat 12196) = _
    immutable_decode(immutableLayout,easBytecode,wordsOf (immStore v),(⟨12196⟩ : UInt256),UInt8.ofNat 250,
      .STATICCALL,none,easBlocks.immutableLayout_inBounds,easBlocks.immutableTemplate_size64)
  | at12855 =>
    change decode (immutableLayout.runtime easBytecode (wordsOf (immStore v))) (UInt256.ofNat 12855) = _
    immutable_decode(immutableLayout,easBytecode,wordsOf (immStore v),(⟨12855⟩ : UInt256),UInt8.ofNat 250,
      .STATICCALL,none,easBlocks.immutableLayout_inBounds,easBlocks.immutableTemplate_size64)

theorem schemaStaticcall {evm : EVM.State} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw gasArg ptr uid : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (v : EASImmutables) (site : SchemaCallSite)
    (hstack : (schemaCallSaved site ptr R).length+1 ≤ 1024) (hs : SourceState s0 ee σ evm)
    (hcd : mem.readWithPadding ptr.toNat 36 = getSchemaPayload uid)
    (rd : RD fork (deployedRuntime v) ee g s0 (schemaCallPC site)
      (gasArg::UInt256.land (EVM.word v._schemaRegistry.val) solcAddrMask::ptr::⟨36⟩::ptr::⟨0⟩::schemaCallSaved site ptr R)
      mem aw rdata σ k C) :
    ∃ evm' σ' success out aw' k' C',
      callViaEVM fork evm v._schemaRegistry 0 (getSchemaPayload uid) (success,evm',out) false ∧
      SourceState s0 ee σ' evm' ∧ out.size < 2^138 ∧
      RD fork (deployedRuntime v) ee g s0 (schemaAfterCallPC site)
        ((if success then ⟨1⟩ else ⟨0⟩)::schemaCallSaved site ptr R) mem aw' out σ' k' C' := by
  have hsmall : (getSchemaPayload uid).size ≤ Ethereum.EVM.maxReturnDataSizeByGas := by
    simp only [getSchemaPayload,ByteArray.size_append,toByteArray_size]
    change 4+32 ≤ Ethereum.EVM.maxReturnDataSizeByGas
    decide +kernel
  obtain ⟨evm',σ',success,out,k',C',hc,hs',rd',hout⟩ :=
    staticcallBridge rd hs (schemaCall_decode v site) hcd hsmall hstack
  rw [solcAddrMask_clean (word_val_addr_canonical v._schemaRegistry),accountAddress_of_word_val_tail] at hc
  rw [callOutputMem_zero] at rd'
  have hpc : schemaCallPC site+⟨1⟩ = schemaAfterCallPC site := by cases site <;> rfl
  rw [hpc] at rd'
  exact ⟨evm',σ',success,out,_,k',C',hc,hs',hout,rd'⟩

end Benchmarks.EAS.EAS
