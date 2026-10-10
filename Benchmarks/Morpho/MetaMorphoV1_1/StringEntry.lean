import Benchmarks.Morpho.MetaMorphoV1_1.Decode
import Benchmarks.Morpho.MetaMorphoV1_1.StringStorageSource
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_054
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_055
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_009
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_025

/-! Metadata getter entry guards and the call to the storage-string decoder. -/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

def stringViewEntryPC (symbol : Bool) : UInt256 := if symbol then ⟨4587⟩ else ⟨10884⟩

def stringCopyPC (symbol : Bool) : UInt256 := if symbol then ⟨4619⟩ else ⟨10916⟩

theorem stringViewReachDecoder {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (symbol : Bool) (hstack : R.length + 6 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩) (hsz : 4 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4) (hsize : I.calldata.size < UInt256.size)
    (rd : RD (deployedRuntime v) I g s0 (stringViewEntryPC symbol) R mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨11801⟩
      (codeOwnerStorageWord I σ (stringViewSlot symbol) :: stringCopyPC symbol ::
        codeOwnerStorageWord I σ (stringViewSlot symbol) :: ⟨0⟩ :: memLoad ⟨64⟩ mem :: R)
      mem aw' rdata σ k' C' := by
  cases symbol with
  | false =>
      have h1 := metaMorphoV1_1_block_10884_fallthrough
        (immWords := wordsOf (immStore v)) (by omega) hwv rd
      have h2 := metaMorphoV1_1_block_10890_fallthrough
        (immWords := wordsOf (immStore v)) (by omega) (calldataLengthCheckOk hsz hhi hsize) h1
      exact metaMorphoV1_1_block_10901_packed (immWords := wordsOf (immStore v)) hstack
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2
  | true =>
      have h1 := metaMorphoV1_1_block_4587_fallthrough
        (immWords := wordsOf (immStore v)) (by omega) hwv rd
      have h2 := metaMorphoV1_1_block_4593_fallthrough
        (immWords := wordsOf (immStore v)) (by omega) (calldataLengthCheckOk hsz hhi hsize) h1
      exact metaMorphoV1_1_block_4604_packed (immWords := wordsOf (immStore v)) hstack
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2

theorem stringViewRevertNonPayable {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (symbol : Bool) (hstack : R.length + 2 ≤ 1024)
    (hwv : I.weiValue ≠ ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 (stringViewEntryPC symbol) R mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have h1 : RD (deployedRuntime v) I g s0 ⟨917⟩ R mem aw rdata σ
      (k + 4) (C + 16) := by
    cases symbol with
    | false =>
        exact metaMorphoV1_1_block_10884_taken (immWords := wordsOf (immStore v)) hstack hwv
          (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
    | true =>
        exact metaMorphoV1_1_block_4587_taken (immWords := wordsOf (immStore v)) hstack hwv
          (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  exact metaMorphoV1_1_block_917 (immWords := wordsOf (immStore v)) hstack h1

theorem stringViewRevertHuge {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (symbol : Bool) (hstack : R.length + 3 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩) (hhi : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (rd : RD (deployedRuntime v) I g s0 (stringViewEntryPC symbol) R mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have hc : UInt256.slt (UInt256.lnot (UInt256.ofNat 3) + UInt256.ofNat I.calldata.size)
      ⟨0⟩ ≠ UInt256.ofNat 0 := by
    change UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat I.calldata.size) ⟨0⟩ ≠ ⟨0⟩
    rw [calldataLengthCheckHuge hhi hsize]
    decide
  have h2 : RD (deployedRuntime v) I g s0 ⟨917⟩ R mem aw rdata σ
      ((k + 4) + 8) ((C + 16) + 29) := by
    cases symbol with
    | false =>
        have h1 := metaMorphoV1_1_block_10884_fallthrough
          (immWords := wordsOf (immStore v)) (by omega) hwv rd
        exact metaMorphoV1_1_block_10890_taken (immWords := wordsOf (immStore v)) hstack hc
          (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
    | true =>
        have h1 := metaMorphoV1_1_block_4587_fallthrough
          (immWords := wordsOf (immStore v)) (by omega) hwv rd
        exact metaMorphoV1_1_block_4593_taken (immWords := wordsOf (immStore v)) hstack hc
          (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
  exact metaMorphoV1_1_block_917 (immWords := wordsOf (immStore v)) (by omega) h2

end Benchmarks.Morpho.MetaMorphoV1_1
