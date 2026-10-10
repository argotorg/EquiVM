import Benchmarks.Morpho.MetaMorphoV1_1.RevocationRole
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_009

/-! Entry guards and storage completion for pending-change revocations. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode

def revocationEntryPC (guardian : Bool) : UInt256 := if guardian then ⟨10526⟩ else ⟨2053⟩

set_option maxRecDepth 2000 in
theorem revocationReachRole {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (guardian : Bool) (hstack : R.length + 3 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩) (hsz : 4 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4) (hsize : I.calldata.size < UInt256.size)
    (rd : RD (deployedRuntime v) I g s0 (revocationEntryPC guardian) R mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 (revocationRolePC guardian) R
      mem aw rdata σ k' C' := by
  cases guardian
  · have r1 := metaMorphoV1_1_block_2053_fallthrough
      (immWords := wordsOf (immStore v)) (by omega) hwv rd
    exact ⟨_, _, metaMorphoV1_1_block_2059_fallthrough
      (immWords := wordsOf (immStore v)) hstack (calldataLengthCheckOk hsz hhi hsize) r1⟩
  · have r1 := metaMorphoV1_1_block_10526_fallthrough
      (immWords := wordsOf (immStore v)) (by omega) hwv rd
    exact ⟨_, _, metaMorphoV1_1_block_10532_fallthrough
      (immWords := wordsOf (immStore v)) hstack (calldataLengthCheckOk hsz hhi hsize) r1⟩

set_option maxRecDepth 2000 in
theorem revocationRevertNonPayable {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (guardian : Bool) (hstack : R.length + 2 ≤ 1024)
    (hwv : I.weiValue ≠ ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 (revocationEntryPC guardian) R mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have r1 : ∃ k' C', RD (deployedRuntime v) I g s0 ⟨917⟩ R mem aw rdata σ k' C' := by
    cases guardian
    · exact ⟨_, _, metaMorphoV1_1_block_2053_taken
        (immWords := wordsOf (immStore v)) hstack hwv
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd⟩
    · exact ⟨_, _, metaMorphoV1_1_block_10526_taken
        (immWords := wordsOf (immStore v)) hstack hwv
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd⟩
  obtain ⟨_, _, r1⟩ := r1
  exact metaMorphoV1_1_block_917 (immWords := wordsOf (immStore v)) hstack r1

set_option maxRecDepth 2000 in
theorem revocationRevertHuge {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (guardian : Bool) (hstack : R.length + 3 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩) (hhi : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (rd : RD (deployedRuntime v) I g s0 (revocationEntryPC guardian) R mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have hc : UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat I.calldata.size) ⟨0⟩ ≠ ⟨0⟩ := by
    rw [calldataLengthCheckHuge hhi hsize]
    decide
  have r1 : ∃ k' C', RD (deployedRuntime v) I g s0 ⟨917⟩ R mem aw rdata σ k' C' := by
    cases guardian
    · have r0 := metaMorphoV1_1_block_2053_fallthrough
        (immWords := wordsOf (immStore v)) (by omega) hwv rd
      exact ⟨_, _, metaMorphoV1_1_block_2059_taken
        (immWords := wordsOf (immStore v)) hstack hc
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r0⟩
    · have r0 := metaMorphoV1_1_block_10526_fallthrough
        (immWords := wordsOf (immStore v)) (by omega) hwv rd
      exact ⟨_, _, metaMorphoV1_1_block_10532_taken
        (immWords := wordsOf (immStore v)) hstack hc
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r0⟩
  obtain ⟨_, _, r1⟩ := r1
  exact metaMorphoV1_1_block_917 (immWords := wordsOf (immStore v)) (by omega) r1

set_option maxRecDepth 2000 in
theorem revocationStoreReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (guardian : Bool) (hstack : R.length + 4 ≤ 1024)
    (hperm : I.perm = true)
    (rd : RD (deployedRuntime v) I g s0 (revocationStorePC guardian) R mem aw rdata σ k C) :
    RDret (deployedRuntime v) g s0 (sstoreAccountMap I.codeOwner σ (revocationSlot guardian)
      ⟨0⟩) ByteArray.empty := by
  cases guardian
  · exact metaMorphoV1_1_block_2095 (immWords := wordsOf (immStore v)) hstack hperm rd
  · exact metaMorphoV1_1_block_10568 (immWords := wordsOf (immStore v)) hstack hperm rd

set_option maxRecDepth 2000 in
theorem revocationStoreStatic {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (guardian : Bool) (hstack : R.length + 2 ≤ 1024)
    (hperm : I.perm = false)
    (rd : RD (deployedRuntime v) I g s0 (revocationStorePC guardian) R mem aw rdata σ k C) :
    RDstatic (deployedRuntime v) g s0 := by
  cases guardian
  · have r1 := rd.push0 (by
      immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
        (⟨2095⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none,
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
    have r2 := r1.push1 ⟨17⟩ (by
      immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
        (⟨2096⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some (⟨17⟩, 1),
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
    exact r2.sstoreStatic hperm (by
      immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
        (⟨2098⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none,
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  · have r1 := rd.push0 (by
      immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
        (⟨10568⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none,
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
    have r2 := r1.push1 ⟨15⟩ (by
      immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
        (⟨10569⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some (⟨15⟩, 1),
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
    exact r2.sstoreStatic hperm (by
      immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
        (⟨10571⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none,
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)

end Benchmarks.Morpho.MetaMorphoV1_1
