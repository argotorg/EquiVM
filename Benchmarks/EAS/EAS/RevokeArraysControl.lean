import Benchmarks.EAS.EAS.RevokeLayout
import Benchmarks.EAS.EAS.AttestArraysControl

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def RevokeKind.arraysPC : RevokeKind → UInt256 | .single => ⟨12220⟩ | .many => ⟨12879⟩
def RevokeKind.recordsReturnPC : RevokeKind → UInt256 | .single => ⟨12231⟩ | .many => ⟨12889⟩
def RevokeKind.valuesReturnPC : RevokeKind → UInt256 | .single => ⟨12241⟩ | .many => ⟨12899⟩
def revokeArraysStack (site : RevokeSite) (R : List UInt256) : List UInt256 :=
  match site.kind with
  | .single => [site.schemaPtr,UInt256.ofNat site.revoker.val,site.schema,site.available,site.ret,site.data]++R
  | .many => [site.schemaPtr,UInt256.ofNat site.revoker.val,site.schema,site.available,site.last.toUInt256,site.ret,site.data]++R

def revokeRecordsSaved (site : RevokeSite) (R : List UInt256) : List UInt256 :=
  match site.kind with
  | .single => [UInt256.ofNat site.revoker.val,site.schemaPtr,UInt256.ofNat site.length,site.schema,site.available,site.ret,site.data]++R
  | .many => [UInt256.ofNat site.length,site.schemaPtr,UInt256.ofNat site.revoker.val,site.schema,site.available,site.last.toUInt256,site.ret,site.data]++R

def revokeValuesSaved (site : RevokeSite) (R : List UInt256) : List UInt256 :=
  match site.kind with
  | .single => [UInt256.ofNat site.length,UInt256.ofNat site.revoker.val,site.schemaPtr,site.records,site.schema,site.available,site.ret,site.data]++R
  | .many => [UInt256.ofNat site.revoker.val,UInt256.ofNat site.length,site.schemaPtr,site.records,site.schema,site.available,site.last.toUInt256,site.ret,site.data]++R

theorem easRevokeRecordsStart {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : EASImmutables) (site : RevokeSite) (hstack : R.length+11 ≤ 1024)
    (hl : memLoad site.data mem = UInt256.ofNat site.length)
    (rd : RD fork (deployedRuntime v) ee g s0 site.kind.arraysPC (revokeArraysStack site R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨7541⟩
      (UInt256.ofNat site.length::site.kind.recordsReturnPC::revokeRecordsSaved site R) mem aw' rdata σ k' C' := by
  cases hk : site.kind with
  | single =>
    simp only [revokeArraysStack,hk,RevokeKind.arraysPC,List.cons_append,List.nil_append] at rd
    obtain ⟨a,j,D,hr⟩ := easBlocks.eas_block_12220_packed (immWords := wordsOf (immStore v))
      (by omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    exact ⟨a,j,D,by simpa only [easBlocks.eas_block_12220_stack,hl,hk,RevokeKind.recordsReturnPC,revokeRecordsSaved] using hr⟩
  | many =>
    simp only [revokeArraysStack,hk,RevokeKind.arraysPC,List.cons_append,List.nil_append] at rd
    obtain ⟨a,j,D,hr⟩ := easBlocks.eas_block_12879_packed (immWords := wordsOf (immStore v))
      hstack (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    exact ⟨a,j,D,by simpa only [easBlocks.eas_block_12879_stack,hl,hk,RevokeKind.recordsReturnPC,revokeRecordsSaved] using hr⟩

theorem easRevokeValuesStart {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : EASImmutables) (site : RevokeSite) (hstack : R.length+12 ≤ 1024)
    (rd : RD fork (deployedRuntime v) ee g s0 site.kind.recordsReturnPC
      (site.records::revokeRecordsSaved site R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨7240⟩
      (UInt256.ofNat site.length::site.kind.valuesReturnPC::revokeValuesSaved site R) mem aw' rdata σ k' C' := by
  cases hk : site.kind with
  | single =>
    simp only [revokeRecordsSaved,hk,RevokeKind.recordsReturnPC,List.cons_append,List.nil_append] at rd
    simpa only [revokeValuesSaved,hk,RevokeKind.valuesReturnPC] using
      easBlocks.eas_block_12231_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
  | many =>
    simp only [revokeRecordsSaved,hk,RevokeKind.recordsReturnPC,List.cons_append,List.nil_append] at rd
    simpa only [revokeValuesSaved,hk,RevokeKind.valuesReturnPC] using
      easBlocks.eas_block_12889_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd

theorem easRevokeArraysDone {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : EASImmutables) (site : RevokeSite) (hstack : R.length+12 ≤ 1024)
    (rd : RD fork (deployedRuntime v) ee g s0 site.kind.valuesReturnPC
      (site.values::revokeValuesSaved site R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 site.kind.loopPC
      (revokeLoopStack site ee ⟨0⟩ R) mem aw' rdata σ k' C' := by
  cases hk : site.kind with
  | single =>
    simp only [revokeValuesSaved,hk,RevokeKind.valuesReturnPC,List.cons_append,List.nil_append] at rd
    obtain ⟨a,j,D,hr⟩ := easBlocks.eas_block_12241_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) rd
    exact ⟨a,j,D,by simpa only [easBlocks.eas_block_12241_stack,revokeLoopStack,revokeGuardTail,revokeGuardRest,hk,
      RevokeKind.loopPC,show UInt256.land (UInt256.ofNat 18446744073709551615) (UInt256.ofNat ee.header.timestamp) = easTimeWord ee from u256_land_comm _ _,List.cons_append,List.nil_append] using hr⟩
  | many =>
    simp only [revokeValuesSaved,hk,RevokeKind.valuesReturnPC,List.cons_append,List.nil_append] at rd
    obtain ⟨a,j,D,hr⟩ := easBlocks.eas_block_12899_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) rd
    exact ⟨a,j,D,by simpa only [easBlocks.eas_block_12899_stack,revokeLoopStack,revokeGuardTail,revokeGuardRest,hk,
      RevokeKind.loopPC,List.cons_append,List.nil_append] using hr⟩

end Benchmarks.EAS.EAS
