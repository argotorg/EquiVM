import Benchmarks.Morpho.MetaMorphoV1_1.StringEntry
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_026
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_059

/-! The two bytecode instances of the storage-string copy loop. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

def stringCopyLoopPC (symbol : Bool) : UInt256 := if symbol then ⟨4703⟩ else ⟨10999⟩

def stringCopyLoopExitPC (symbol : Bool) : UInt256 := if symbol then ⟨4711⟩ else ⟨11007⟩

inductive StorageStringLoopKind where
  | metadata (symbol : Bool)
  | fallback

def storageStringLoopPC : StorageStringLoopKind → UInt256
  | .metadata symbol => stringCopyLoopPC symbol
  | .fallback => ⟨11914⟩

def storageStringLoopExitPC : StorageStringLoopKind → UInt256
  | .metadata symbol => stringCopyLoopExitPC symbol
  | .fallback => ⟨11922⟩

def storageStringLoopStack (kind : StorageStringLoopKind) (len off ptr slot : UInt256)
    (R : List UInt256) : List UInt256 :=
  match kind with
  | .metadata _ => len :: off :: ptr :: slot :: R
  | .fallback => slot :: ptr :: off :: len :: R

theorem stringCopyLoopExit {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {len off ptr slot : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (symbol : Bool) (hstack : R.length + 6 ≤ 1024)
    (hcond : UInt256.lt off len = ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 (stringCopyLoopPC symbol)
      (len :: off :: ptr :: slot :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 (stringCopyLoopExitPC symbol)
      (len :: off :: ptr :: slot :: R) mem aw' rdata σ k' C' := by
  cases symbol with
  | false =>
      exact metaMorphoV1_1_block_10999_fallthrough_packed
        (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) hcond rd
  | true =>
      exact metaMorphoV1_1_block_4703_fallthrough_packed
        (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) hcond rd

theorem stringCopyLoopStep {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {len off ptr slot : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (symbol : Bool) (hstack : R.length + 10 ≤ 1024)
    (hcond : UInt256.lt off len ≠ ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 (stringCopyLoopPC symbol)
      (len :: off :: ptr :: slot :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 (stringCopyLoopPC symbol)
      (len :: (off + UInt256.ofNat 32) :: ptr :: (slot + UInt256.ofNat 1) :: R)
      (Reasoning.Theory.writeWord mem ((ptr + off) + UInt256.ofNat 32).toNat
        (codeOwnerStorageWord I σ slot)) aw' rdata σ k' C' := by
  cases symbol with
  | false =>
      obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_10999_taken_packed
        (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) hcond
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
      exact metaMorphoV1_1_block_11023_packed (immWords := wordsOf (immStore v)) hstack
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
  | true =>
      obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_4703_taken_packed
        (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) hcond
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
      exact metaMorphoV1_1_block_4727_packed (immWords := wordsOf (immStore v)) hstack
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1

theorem storageStringLoopExit {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {len off ptr slot : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (kind : StorageStringLoopKind)
    (hstack : R.length + 6 ≤ 1024) (hcond : UInt256.lt off len = ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 (storageStringLoopPC kind)
      (storageStringLoopStack kind len off ptr slot R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 (storageStringLoopExitPC kind)
      (storageStringLoopStack kind len off ptr slot R) mem aw' rdata σ k' C' := by
  cases kind with
  | metadata symbol => exact stringCopyLoopExit v symbol hstack hcond rd
  | fallback =>
      exact metaMorphoV1_1_block_11914_fallthrough_packed
        (immWords := wordsOf (immStore v)) hstack hcond rd

theorem storageStringLoopStep {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {len off ptr slot : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (kind : StorageStringLoopKind)
    (hstack : R.length + 10 ≤ 1024) (hcond : UInt256.lt off len ≠ ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 (storageStringLoopPC kind)
      (storageStringLoopStack kind len off ptr slot R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 (storageStringLoopPC kind)
      (storageStringLoopStack kind len (off + UInt256.ofNat 32) ptr
        (slot + UInt256.ofNat 1) R)
      (Reasoning.Theory.writeWord mem ((ptr + off) + UInt256.ofNat 32).toNat
        (codeOwnerStorageWord I σ slot)) aw' rdata σ k' C' := by
  cases kind with
  | metadata symbol => exact stringCopyLoopStep v symbol hstack hcond rd
  | fallback =>
      obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_11914_taken_packed
        (immWords := wordsOf (immStore v)) (by omega) hcond
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
      exact metaMorphoV1_1_block_11931_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega)
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1

end Benchmarks.Morpho.MetaMorphoV1_1
