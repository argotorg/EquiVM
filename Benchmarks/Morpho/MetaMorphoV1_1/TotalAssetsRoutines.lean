import Benchmarks.Morpho.MetaMorphoV1_1.Decode
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_054
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_055
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_009

/-! totalAssets entry guards and encoding of the total returned by fee accrual. -/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

theorem totalAssetsReachAccrual {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 3 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩) (hsz : 4 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4) (hsize : I.calldata.size < UInt256.size)
    (rd : RD (deployedRuntime v) I g s0 ⟨11049⟩ R mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨12247⟩
      (⟨11075⟩ :: ⟨32⟩ :: R) mem aw' rdata σ k' C' := by
  have h1 := metaMorphoV1_1_block_11049_fallthrough
    (immWords := wordsOf (immStore v)) (by omega) hwv rd
  have h2 := metaMorphoV1_1_block_11055_fallthrough
    (immWords := wordsOf (immStore v)) hstack (calldataLengthCheckOk hsz hhi hsize) h1
  exact metaMorphoV1_1_block_11066_packed (immWords := wordsOf (immStore v)) hstack
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2

theorem totalAssetsRevertNonPayable {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 2 ≤ 1024)
    (hwv : I.weiValue ≠ ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨11049⟩ R mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have h1 := metaMorphoV1_1_block_11049_taken
    (immWords := wordsOf (immStore v)) hstack hwv
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  exact metaMorphoV1_1_block_917 (immWords := wordsOf (immStore v)) hstack h1

theorem totalAssetsRevertHuge {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 3 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩) (hhi : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (rd : RD (deployedRuntime v) I g s0 ⟨11049⟩ R mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have h1 := metaMorphoV1_1_block_11049_fallthrough
    (immWords := wordsOf (immStore v)) (by omega) hwv rd
  have h2 := metaMorphoV1_1_block_11055_taken
    (immWords := wordsOf (immStore v)) hstack
    (by
      change UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat I.calldata.size) ⟨0⟩ ≠ ⟨0⟩
      rw [calldataLengthCheckHuge hhi hsize]; decide)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
  exact metaMorphoV1_1_block_917 (immWords := wordsOf (immStore v)) (by omega) h2

theorem totalAssetsEncodeReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {lost total shares : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 4 ≤ 1024)
    (rd : RD (deployedRuntime v) I g s0 ⟨11075⟩
      ([lost, total, shares, ⟨32⟩] ++ R) mem aw rdata σ k C) :
    RDret (deployedRuntime v) g s0 σ total.toByteArray := by
  have h := metaMorphoV1_1_block_11075 (immWords := wordsOf (immStore v)) hstack rd
  change RDret _ _ _ _ ((writeWord mem (memLoad ⟨64⟩ mem).toNat total).readWithPadding
    (memLoad ⟨64⟩ mem).toNat 32) at h
  rw [writeWord_sparse_read_back] at h
  exact h

end Benchmarks.Morpho.MetaMorphoV1_1
