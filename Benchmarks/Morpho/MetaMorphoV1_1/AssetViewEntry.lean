import Benchmarks.Morpho.MetaMorphoV1_1.Decode
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_039
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_055

/-! Shared entry guards for convertToAssets and previewRedeem. -/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

theorem assetViewReachAccrual {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 5 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩) (hsz : 36 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4) (hsize : I.calldata.size < UInt256.size)
    (rd : RD (deployedRuntime v) I g s0 ⟨7734⟩ R mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨12247⟩
      ([⟨3533⟩, ⟨11155⟩, ⟨1578⟩, ⟨32⟩] ++ R) mem aw' rdata σ k' C' := by
  obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_7734_packed
    (immWords := wordsOf (immStore v)) (by omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  obtain ⟨aw2, k2, C2, h2⟩ := metaMorphoV1_1_block_11122_fallthrough_packed
    (immWords := wordsOf (immStore v)) (by omega) hwv h1
  obtain ⟨aw3, k3, C3, h3⟩ := metaMorphoV1_1_block_11128_fallthrough_packed
    (immWords := wordsOf (immStore v)) (by omega) (by
      change UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat I.calldata.size) ⟨32⟩ = ⟨0⟩
      rw [calldataNot3_eq_sub (by omega) hsize]
      exact solcDecodeLenCheckOk_4_32 hsz hhi hsize) h2
  exact metaMorphoV1_1_block_11140_packed (immWords := wordsOf (immStore v)) hstack
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h3

theorem assetViewRevertNonPayable {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 2 ≤ 1024)
    (hwv : I.weiValue ≠ ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨7734⟩ R mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_7734_packed
    (immWords := wordsOf (immStore v)) (by omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  obtain ⟨aw2, k2, C2, h2⟩ := metaMorphoV1_1_block_11122_taken_packed
    (immWords := wordsOf (immStore v)) hstack hwv
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
  exact metaMorphoV1_1_block_917 (immWords := wordsOf (immStore v)) hstack h2

theorem assetViewRevertLength {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 3 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩)
    (hcond : UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat I.calldata.size) ⟨32⟩ ≠ ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨7734⟩ R mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_7734_packed
    (immWords := wordsOf (immStore v)) (by omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  obtain ⟨aw2, k2, C2, h2⟩ := metaMorphoV1_1_block_11122_fallthrough_packed
    (immWords := wordsOf (immStore v)) (by omega) hwv h1
  obtain ⟨aw3, k3, C3, h3⟩ := metaMorphoV1_1_block_11128_taken_packed
    (immWords := wordsOf (immStore v)) hstack hcond
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2
  exact metaMorphoV1_1_block_917 (immWords := wordsOf (immStore v)) (by omega) h3

end Benchmarks.Morpho.MetaMorphoV1_1
