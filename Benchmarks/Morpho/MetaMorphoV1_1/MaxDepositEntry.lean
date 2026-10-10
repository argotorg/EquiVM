import Benchmarks.Morpho.MetaMorphoV1_1.Decode
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_044
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_012

/-! Max-deposit entry guards, address decoding, and scalar return encoding. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode

set_option maxRecDepth 2000 in
theorem maxDepositReachDecoder {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 3 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩) (hsz : 36 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4) (hsize : I.calldata.size < UInt256.size)
    (rd : RD (deployedRuntime v) I g s0 ⟨8828⟩ R mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ⟨11163⟩
      (⟨8853⟩ :: R) mem aw rdata σ k' C' := by
  have rd8834 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_8828_fallthrough
    (immWords := wordsOf (immStore v)) (by omega) hwv rd
  have rd8846 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_8834_fallthrough
    (immWords := wordsOf (immStore v)) hstack (by
      change UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat I.calldata.size) ⟨32⟩ = ⟨0⟩
      rw [calldataNot3_eq_sub (by omega) hsize]
      exact solcDecodeLenCheckOk_4_32 hsz hhi hsize) rd8834
  have rd11163 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_8846
    (immWords := wordsOf (immStore v)) (by omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd8846
  exact ⟨_, _, rd11163⟩

set_option maxRecDepth 2000 in
theorem maxDepositRevertNonPayable {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 2 ≤ 1024)
    (hwv : I.weiValue ≠ ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨8828⟩ R mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have rd917 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_8828_taken
    (immWords := wordsOf (immStore v)) hstack hwv
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  exact metaMorphoV1_1Blocks.metaMorphoV1_1_block_917
    (immWords := wordsOf (immStore v)) hstack rd917

set_option maxRecDepth 2000 in
theorem maxDepositRevertLength {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 3 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩)
    (hcond : UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat I.calldata.size) ⟨32⟩ ≠ ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨8828⟩ R mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have rd8834 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_8828_fallthrough
    (immWords := wordsOf (immStore v)) (by omega) hwv rd
  have rd917 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_8834_taken
    (immWords := wordsOf (immStore v)) hstack hcond
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd8834
  exact metaMorphoV1_1Blocks.metaMorphoV1_1_block_917
    (immWords := wordsOf (immStore v)) (by omega) rd917

set_option maxRecDepth 2000 in
theorem maxDepositRevertNoncanonical {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 6 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩) (hsz : 36 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4) (hsize : I.calldata.size < UInt256.size)
    (hnc : ¬ (calldataWord I.calldata 4).toNat < EVM.addressModulus)
    (rd : RD (deployedRuntime v) I g s0 ⟨8828⟩ R mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  obtain ⟨_, _, rd11163⟩ := maxDepositReachDecoder v (by omega) hwv hsz hhi hsize rd
  exact decodeAddressAt4Revert v (by omega) hnc rd11163

set_option maxRecDepth 2000 in
theorem maxDepositReachFunction {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 5 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩) (hsz : 36 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4) (hsize : I.calldata.size < UInt256.size)
    (hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus)
    (rd : RD (deployedRuntime v) I g s0 ⟨8828⟩ R mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨13894⟩
      (⟨1578⟩ :: ⟨32⟩ :: R) mem aw' rdata σ k' C' := by
  obtain ⟨_, _, h1⟩ := maxDepositReachDecoder v (by omega) hwv hsz hhi hsize rd
  obtain ⟨_, _, h2⟩ := decodeAddressAt4 v hstack hcanon
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h1
  exact metaMorphoV1_1Blocks.metaMorphoV1_1_block_8853_packed
    (immWords := wordsOf (immStore v)) (by omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2

theorem maxDepositEncodeReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {total : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 4 ≤ 1024)
    (rd : RD (deployedRuntime v) I g s0 ⟨1578⟩
      (total :: ⟨32⟩ :: R) mem aw rdata σ k C) :
    RDret (deployedRuntime v) g s0 σ total.toByteArray := by
  have h := metaMorphoV1_1Blocks.metaMorphoV1_1_block_1578
    (immWords := wordsOf (immStore v)) hstack rd
  change RDret _ _ _ _ ((writeWord mem (memLoad ⟨64⟩ mem).toNat total).readWithPadding
    (memLoad ⟨64⟩ mem).toNat 32) at h
  rw [writeWord_sparse_read_back] at h
  exact h

end Benchmarks.Morpho.MetaMorphoV1_1
