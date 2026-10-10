import Benchmarks.Morpho.MetaMorphoV1_1.StringSetStorage
import Benchmarks.Morpho.MetaMorphoV1_1.StringDecoder
import Benchmarks.Morpho.MetaMorphoV1_1.StringSetSource

/-! Shared nonpayable and owner-call entry paths for the metadata setters. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

def stringSetEntryPC (symbol : Bool) : UInt256 := if symbol then ⟨3002⟩ else ⟨2240⟩

def stringSetDecodedPC (symbol : Bool) : UInt256 := if symbol then ⟨3016⟩ else ⟨2254⟩

theorem stringSetNonpayable {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (symbol : Bool) (hstack : R.length + 2 ≤ 1024)
    (hwv : I.weiValue ≠ ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 (stringSetEntryPC symbol) R mem aw out σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have hentry : ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨917⟩ R mem aw' out σ k' C' := by
    cases symbol with
    | false =>
        exact metaMorphoV1_1_block_2240_taken_packed (immWords := wordsOf (immStore v))
          hstack hwv (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
    | true =>
        exact metaMorphoV1_1_block_3002_taken_packed (immWords := wordsOf (immStore v))
          hstack hwv (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  obtain ⟨aw1, k1, C1, h1⟩ := hentry
  exact metaMorphoV1_1_block_917 (immWords := wordsOf (immStore v)) hstack h1

theorem stringSetDecodeEntry {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (symbol : Bool) (hstack : R.length + 3 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 (stringSetEntryPC symbol) R mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨11698⟩
      (UInt256.ofNat I.calldata.size :: stringSetDecodedPC symbol :: R) mem aw' out σ k' C' := by
  cases symbol with
  | false =>
      obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_2240_fallthrough_packed
        (immWords := wordsOf (immStore v)) (by omega) hwv rd
      exact metaMorphoV1_1_block_2246_packed (immWords := wordsOf (immStore v)) hstack
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
  | true =>
      obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_3002_fallthrough_packed
        (immWords := wordsOf (immStore v)) (by omega) hwv rd
      exact metaMorphoV1_1_block_3008_packed (immWords := wordsOf (immStore v)) hstack
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1

theorem stringSetOwnerEntry {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (symbol : Bool) (hstack : R.length + 2 ≤ 1024)
    (rd : RD (deployedRuntime v) I g s0 (stringSetDecodedPC symbol) R mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨12917⟩
      (stringSetOwnerReturnPC symbol :: R) mem aw' out σ k' C' := by
  cases symbol with
  | false =>
      exact metaMorphoV1_1_block_2254_packed (immWords := wordsOf (immStore v)) hstack
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  | true =>
      exact metaMorphoV1_1_block_3016_packed (immWords := wordsOf (immStore v)) hstack
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd

end Benchmarks.Morpho.MetaMorphoV1_1
