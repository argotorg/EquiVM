import Benchmarks.EAS.EAS.UIDSites
import Benchmarks.EAS.EAS.ZeroBranch

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def uidAvailablePC : UIDSite → UInt256
  | .single .. => UInt256.ofNat 8511
  | .many .. => UInt256.ofNat 10727
def uidAgainPC : UIDSite → UInt256
  | .single .. => UInt256.ofNat 8497
  | .many .. => UInt256.ofNat 10713

theorem uidLookup_wf (v : EASImmutables) (site : UIDSite) :
    mappingWordLoadWf (deployedRuntime v) (uidDonePC site) ⟨1⟩ := by
  cases site with
  | single s1 s2 s3 s4 s5 s6 s7 s8 =>
    refine ⟨(by immutable_decode(immutableLayout, easBytecode, wordsOf (immStore v), (⟨8477⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)),
      (by immutable_decode(immutableLayout, easBytecode, wordsOf (immStore v), (⟨8478⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((⟨0⟩ : UInt256),1), easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)),
      (by immutable_decode(immutableLayout, easBytecode, wordsOf (immStore v), (⟨8480⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)),
      (by immutable_decode(immutableLayout, easBytecode, wordsOf (immStore v), (⟨8481⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((⟨1⟩ : UInt256),1), easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)),
      (by immutable_decode(immutableLayout, easBytecode, wordsOf (immStore v), (⟨8483⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((⟨32⟩ : UInt256),1), easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)),
      (by immutable_decode(immutableLayout, easBytecode, wordsOf (immStore v), (⟨8485⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)),
      (by immutable_decode(immutableLayout, easBytecode, wordsOf (immStore v), (⟨8486⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((⟨64⟩ : UInt256),1), easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)),
      (by immutable_decode(immutableLayout, easBytecode, wordsOf (immStore v), (⟨8488⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((⟨0⟩ : UInt256),1), easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)),
      (by immutable_decode(immutableLayout, easBytecode, wordsOf (immStore v), (⟨8490⟩ : UInt256), UInt8.ofNat 32, .KECCAK256, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)),
      (by immutable_decode(immutableLayout, easBytecode, wordsOf (immStore v), (⟨8491⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64))⟩
  | many s1 s2 s3 s4 s5 s6 =>
    refine ⟨(by immutable_decode(immutableLayout, easBytecode, wordsOf (immStore v), (⟨10693⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)),
      (by immutable_decode(immutableLayout, easBytecode, wordsOf (immStore v), (⟨10694⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((⟨0⟩ : UInt256),1), easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)),
      (by immutable_decode(immutableLayout, easBytecode, wordsOf (immStore v), (⟨10696⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)),
      (by immutable_decode(immutableLayout, easBytecode, wordsOf (immStore v), (⟨10697⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((⟨1⟩ : UInt256),1), easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)),
      (by immutable_decode(immutableLayout, easBytecode, wordsOf (immStore v), (⟨10699⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((⟨32⟩ : UInt256),1), easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)),
      (by immutable_decode(immutableLayout, easBytecode, wordsOf (immStore v), (⟨10701⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)),
      (by immutable_decode(immutableLayout, easBytecode, wordsOf (immStore v), (⟨10702⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((⟨64⟩ : UInt256),1), easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)),
      (by immutable_decode(immutableLayout, easBytecode, wordsOf (immStore v), (⟨10704⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((⟨0⟩ : UInt256),1), easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)),
      (by immutable_decode(immutableLayout, easBytecode, wordsOf (immStore v), (⟨10706⟩ : UInt256), UInt8.ofNat 32, .KECCAK256, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)),
      (by immutable_decode(immutableLayout, easBytecode, wordsOf (immStore v), (⟨10707⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64))⟩

theorem uidBranch_decode (v : EASImmutables) (site : UIDSite) :
    decode (deployedRuntime v) (uidDonePC site+⟨15⟩) = some (.ISZERO,.none) ∧
    decode (deployedRuntime v) ((uidDonePC site+⟨15⟩)+⟨1⟩) = some (.Push .PUSH2,some (uidAvailablePC site,2)) ∧
    decode (deployedRuntime v) ((uidDonePC site+⟨15⟩)+⟨4⟩) = some (.JUMPI,.none) := by
  cases site with
  | single s1 s2 s3 s4 s5 s6 s7 s8 =>
    refine ⟨(by immutable_decode(immutableLayout, easBytecode, wordsOf (immStore v), (⟨8492⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)),
      (by immutable_decode(immutableLayout, easBytecode, wordsOf (immStore v), (⟨8493⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((⟨8511⟩ : UInt256),2), easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)),
      (by immutable_decode(immutableLayout, easBytecode, wordsOf (immStore v), (⟨8496⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64))⟩
  | many s1 s2 s3 s4 s5 s6 =>
    refine ⟨(by immutable_decode(immutableLayout, easBytecode, wordsOf (immStore v), (⟨10708⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)),
      (by immutable_decode(immutableLayout, easBytecode, wordsOf (immStore v), (⟨10709⟩ : UInt256), UInt8.ofNat 97, .Push .PUSH2, some ((⟨10727⟩ : UInt256),2), easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)),
      (by immutable_decode(immutableLayout, easBytecode, wordsOf (immStore v), (⟨10712⟩ : UInt256), UInt8.ofNat 87, .JUMPI, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64))⟩

theorem easUIDAvailable {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {word : UInt256} {R : List UInt256} (v : EASImmutables) (site : UIDSite)
    (hstack : R.length+3 ≤ 1024)
    (rd : RD fork (deployedRuntime v) ee g s0 (uidDonePC site) (word::R) mem aw rdata σ k C) :
    if solcSlotWord σ ee (dbSlot word) = ⟨0⟩ then
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 (uidAvailablePC site) (word::R)
        (twoWordHashMem word ⟨1⟩ mem) aw' rdata σ k' C'
    else ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 (uidAgainPC site) (word::R)
      (twoWordHashMem word ⟨1⟩ mem) aw' rdata σ k' C' := by
  obtain ⟨aw',k',C',hr⟩ := mappingWordLoad hstack (uidLookup_wf v site) rd
  obtain ⟨hd0,hd1,hd4⟩ := uidBranch_decode v site
  have hb := zeroBranch (by simp only [List.length_cons]; omega) hd0 hd1 hd4
    (by cases site <;> rw [easPatchedValidJumps v] <;> simp only [uidAvailablePC] <;> jump_dest) hr
  by_cases hz : solcSlotWord σ ee (dbSlot word) = ⟨0⟩
  · rw [if_pos hz] at ⊢
    dsimp only [dbSlot] at hz
    rw [if_pos hz] at hb
    obtain ⟨k'',C'',hr'⟩ := hb
    exact ⟨aw',k'',C'',hr'⟩
  · rw [if_neg hz] at ⊢
    dsimp only [dbSlot] at hz
    rw [if_neg hz] at hb
    obtain ⟨k'',C'',hr'⟩ := hb
    have he : (uidDonePC site+⟨15⟩)+⟨5⟩ = uidAgainPC site := by cases site <;> rfl
    rw [he] at hr'
    exact ⟨aw',k'',C'',hr'⟩

def nextUIDBump (bump : UInt256) : UInt256 := UInt256.land (UInt256.ofNat 4294967295) (UInt256.ofNat 1+bump)

theorem easUIDAgain {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {word bump : UInt256} {R : List UInt256} (v : EASImmutables) (site : UIDSite)
    (hstack : R.length+2 ≤ 1024)
    (rd : RD fork (deployedRuntime v) ee g s0 (uidAgainPC site) (word::bump::R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 (uidStartPC site) (nextUIDBump bump::R) mem aw' rdata σ k' C' := by
  cases site with
  | single s1 s2 s3 s4 s5 s6 s7 s8 =>
    obtain ⟨aw',k',C',hr⟩ := easBlocks.eas_block_8497_packed (immWords := wordsOf (immStore v)) hstack
      (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    exact ⟨aw',k',C',hr⟩
  | many s1 s2 s3 s4 s5 s6 =>
    obtain ⟨aw',k',C',hr⟩ := easBlocks.eas_block_10713_packed (immWords := wordsOf (immStore v)) hstack
      (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    exact ⟨aw',k',C',hr⟩

end Benchmarks.EAS.EAS
