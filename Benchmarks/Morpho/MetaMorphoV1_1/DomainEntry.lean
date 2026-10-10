import Benchmarks.Morpho.MetaMorphoV1_1.Decode
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_047

/-! Public domain-separator guards and entry to the shared cache routine. -/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

theorem domainReachCache {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 3 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩) (hsz : 4 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4) (hsize : I.calldata.size < UInt256.size)
    (rd : RD (deployedRuntime v) I g s0 ⟨9689⟩ R mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨12937⟩
      (⟨1578⟩ :: ⟨32⟩ :: R) mem aw' rdata σ k' C' := by
  have h1 := metaMorphoV1_1_block_9689_fallthrough
    (immWords := wordsOf (immStore v)) (by omega) hwv rd
  have h2 := metaMorphoV1_1_block_9695_fallthrough
    (immWords := wordsOf (immStore v)) hstack (calldataLengthCheckOk hsz hhi hsize) h1
  exact metaMorphoV1_1_block_9706_packed (immWords := wordsOf (immStore v)) hstack
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2

theorem domainRevertNonPayable {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 2 ≤ 1024)
    (hwv : I.weiValue ≠ ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨9689⟩ R mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have h1 := metaMorphoV1_1_block_9689_taken (immWords := wordsOf (immStore v)) hstack hwv
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  exact metaMorphoV1_1_block_917 (immWords := wordsOf (immStore v)) hstack h1

theorem domainRevertHuge {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 3 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩) (hhi : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (rd : RD (deployedRuntime v) I g s0 ⟨9689⟩ R mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have h1 := metaMorphoV1_1_block_9689_fallthrough
    (immWords := wordsOf (immStore v)) (by omega) hwv rd
  have h2 := metaMorphoV1_1_block_9695_taken (immWords := wordsOf (immStore v)) hstack (by
    change UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat I.calldata.size) ⟨0⟩ ≠ ⟨0⟩
    rw [calldataLengthCheckHuge hhi hsize]
    decide) (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
  exact metaMorphoV1_1_block_917 (immWords := wordsOf (immStore v)) (by omega) h2

end Benchmarks.Morpho.MetaMorphoV1_1
