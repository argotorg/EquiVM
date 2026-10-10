import Benchmarks.Morpho.MetaMorphoV1_1.Decode
import Benchmarks.Morpho.MetaMorphoV1_1.AccessControl
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_009
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_037

/-! Calldata and owner-call setup for setting the fee. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode

set_option maxRecDepth 2000 in
theorem setFeeReachOwner {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 3 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩) (hsz : 36 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4) (hsize : I.calldata.size < UInt256.size)
    (rd : RD (deployedRuntime v) I g s0 ⟨7417⟩ R mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ⟨12917⟩ (⟨7445⟩ :: calldataWord I.calldata 4 :: R)
      mem aw rdata σ k' C' := by
  have rd7423 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_7417_fallthrough
    (immWords := wordsOf (immStore v)) (by omega) hwv rd
  have rd7435 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_7423_fallthrough
    (immWords := wordsOf (immStore v)) hstack (by
      change UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat I.calldata.size) ⟨32⟩ = ⟨0⟩
      rw [calldataNot3_eq_sub (by omega) hsize]
      exact solcDecodeLenCheckOk_4_32 hsz hhi hsize) rd7423
  have rd12917 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_7435
    (immWords := wordsOf (immStore v)) (by omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd7435
  exact ⟨_, _, rd12917⟩

set_option maxRecDepth 2000 in
theorem setFeeRevertNonPayable {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 2 ≤ 1024)
    (hwv : I.weiValue ≠ ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨7417⟩ R mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have rd917 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_7417_taken
    (immWords := wordsOf (immStore v)) hstack hwv
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  exact metaMorphoV1_1Blocks.metaMorphoV1_1_block_917
    (immWords := wordsOf (immStore v)) hstack rd917

set_option maxRecDepth 2000 in
theorem setFeeRevertLength {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 3 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩)
    (hcond : UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat I.calldata.size) ⟨32⟩ ≠ ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨7417⟩ R mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have rd7423 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_7417_fallthrough
    (immWords := wordsOf (immStore v)) (by omega) hwv rd
  have rd917 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_7423_taken
    (immWords := wordsOf (immStore v)) hstack hcond
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd7423
  exact metaMorphoV1_1Blocks.metaMorphoV1_1_block_917
    (immWords := wordsOf (immStore v)) (by omega) rd917

end Benchmarks.Morpho.MetaMorphoV1_1
