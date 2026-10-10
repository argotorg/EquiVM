import Benchmarks.Morpho.MetaMorphoV1_1.Decode
import Benchmarks.Morpho.MetaMorphoV1_1.AccessControl
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_009
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_035

/-! Calldata and owner-call setup for submitting a timelock update. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode

set_option maxRecDepth 2000 in
theorem submitTimelockReachOwner {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 3 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩) (hsz : 36 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4) (hsize : I.calldata.size < UInt256.size)
    (rd : RD (deployedRuntime v) I g s0 ⟨6869⟩ R mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ⟨12917⟩ (⟨6897⟩ :: calldataWord I.calldata 4 :: R)
      mem aw rdata σ k' C' := by
  have rd6875 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_6869_fallthrough
    (immWords := wordsOf (immStore v)) (by omega) hwv rd
  have rd6887 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_6875_fallthrough
    (immWords := wordsOf (immStore v)) hstack (by
      change UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat I.calldata.size) ⟨32⟩ = ⟨0⟩
      rw [calldataNot3_eq_sub (by omega) hsize]
      exact solcDecodeLenCheckOk_4_32 hsz hhi hsize) rd6875
  have rd12917 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_6887
    (immWords := wordsOf (immStore v)) (by omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd6887
  exact ⟨_, _, rd12917⟩

set_option maxRecDepth 2000 in
theorem submitTimelockRevertNonPayable {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 2 ≤ 1024)
    (hwv : I.weiValue ≠ ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨6869⟩ R mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have rd917 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_6869_taken
    (immWords := wordsOf (immStore v)) hstack hwv
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  exact metaMorphoV1_1Blocks.metaMorphoV1_1_block_917
    (immWords := wordsOf (immStore v)) hstack rd917

set_option maxRecDepth 2000 in
theorem submitTimelockRevertLength {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 3 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩)
    (hcond : UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat I.calldata.size) ⟨32⟩ ≠ ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨6869⟩ R mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have rd6875 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_6869_fallthrough
    (immWords := wordsOf (immStore v)) (by omega) hwv rd
  have rd917 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_6875_taken
    (immWords := wordsOf (immStore v)) hstack hcond
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd6875
  exact metaMorphoV1_1Blocks.metaMorphoV1_1_block_917
    (immWords := wordsOf (immStore v)) (by omega) rd917

end Benchmarks.Morpho.MetaMorphoV1_1
