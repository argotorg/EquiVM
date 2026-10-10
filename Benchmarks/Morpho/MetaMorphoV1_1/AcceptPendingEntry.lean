import Benchmarks.Morpho.MetaMorphoV1_1.AcceptPendingSyntax
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_023
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_027
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_009

/-! Nonpayable and calldata guards for pending-change acceptance. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode

def acceptPendingEntryPC (guardian : Bool) : UInt256 := if guardian then ⟨4172⟩ else ⟨4895⟩

def acceptPendingReadPC (guardian : Bool) : UInt256 := if guardian then ⟨4189⟩ else ⟨4912⟩

set_option maxRecDepth 2000 in
theorem acceptPendingReachRead {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (guardian : Bool) (hstack : R.length + 3 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩) (hsz : 4 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4) (hsize : I.calldata.size < UInt256.size)
    (rd : RD (deployedRuntime v) I g s0 (acceptPendingEntryPC guardian) R mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 (acceptPendingReadPC guardian) R
      mem aw rdata σ k' C' := by
  cases guardian
  · have r1 := metaMorphoV1_1_block_4895_fallthrough
      (immWords := wordsOf (immStore v)) (by omega) hwv rd
    exact ⟨_, _, metaMorphoV1_1_block_4901_fallthrough
      (immWords := wordsOf (immStore v)) hstack (calldataLengthCheckOk hsz hhi hsize) r1⟩
  · have r1 := metaMorphoV1_1_block_4172_fallthrough
      (immWords := wordsOf (immStore v)) (by omega) hwv rd
    exact ⟨_, _, metaMorphoV1_1_block_4178_fallthrough
      (immWords := wordsOf (immStore v)) hstack (calldataLengthCheckOk hsz hhi hsize) r1⟩

set_option maxRecDepth 2000 in
theorem acceptPendingRevertNonPayable {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (guardian : Bool) (hstack : R.length + 2 ≤ 1024)
    (hwv : I.weiValue ≠ ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 (acceptPendingEntryPC guardian) R mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have r1 : ∃ k' C', RD (deployedRuntime v) I g s0 ⟨917⟩ R mem aw rdata σ k' C' := by
    cases guardian
    · exact ⟨_, _, metaMorphoV1_1_block_4895_taken
        (immWords := wordsOf (immStore v)) hstack hwv
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd⟩
    · exact ⟨_, _, metaMorphoV1_1_block_4172_taken
        (immWords := wordsOf (immStore v)) hstack hwv
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd⟩
  obtain ⟨_, _, r1⟩ := r1
  exact metaMorphoV1_1_block_917 (immWords := wordsOf (immStore v)) hstack r1

set_option maxRecDepth 2000 in
theorem acceptPendingRevertHuge {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (guardian : Bool) (hstack : R.length + 3 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩) (hhi : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (rd : RD (deployedRuntime v) I g s0 (acceptPendingEntryPC guardian) R mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have hc : UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat I.calldata.size) ⟨0⟩ ≠ ⟨0⟩ := by
    rw [calldataLengthCheckHuge hhi hsize]
    decide
  have r1 : ∃ k' C', RD (deployedRuntime v) I g s0 ⟨917⟩ R mem aw rdata σ k' C' := by
    cases guardian
    · have r0 := metaMorphoV1_1_block_4895_fallthrough
        (immWords := wordsOf (immStore v)) (by omega) hwv rd
      exact ⟨_, _, metaMorphoV1_1_block_4901_taken
        (immWords := wordsOf (immStore v)) hstack hc
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r0⟩
    · have r0 := metaMorphoV1_1_block_4172_fallthrough
        (immWords := wordsOf (immStore v)) (by omega) hwv rd
      exact ⟨_, _, metaMorphoV1_1_block_4178_taken
        (immWords := wordsOf (immStore v)) hstack hc
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r0⟩
  obtain ⟨_, _, r1⟩ := r1
  exact metaMorphoV1_1_block_917 (immWords := wordsOf (immStore v)) (by omega) r1

end Benchmarks.Morpho.MetaMorphoV1_1
