import Benchmarks.Morpho.MetaMorphoV1_1.Decode
import Benchmarks.Morpho.MetaMorphoV1_1.AccessControl
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_009
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_020
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_021

/-! Calldata and owner-call setup for setting an allocator flag. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode

set_option maxRecDepth 2000 in
theorem setAllocatorReachDecoder {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 3 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩) (hsz : 68 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4) (hsize : I.calldata.size < UInt256.size)
    (rd : RD (deployedRuntime v) I g s0 ⟨3552⟩ R mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ⟨11163⟩ (⟨3577⟩ :: R)
      mem aw rdata σ k' C' := by
  have rd3558 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_3552_fallthrough
    (immWords := wordsOf (immStore v)) (by omega) hwv rd
  have rd3570 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_3558_fallthrough
    (immWords := wordsOf (immStore v)) hstack (by
      change UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat I.calldata.size) ⟨64⟩ = ⟨0⟩
      rw [calldataNot3_eq_sub (by omega) hsize]
      exact solcDecodeLenCheckOk_4_64 hsz hhi hsize) rd3558
  have rd11163 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_3570
    (immWords := wordsOf (immStore v)) (by omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd3570
  exact ⟨_, _, rd11163⟩

set_option maxRecDepth 2000 in
theorem setAllocatorRevertNonPayable {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 2 ≤ 1024)
    (hwv : I.weiValue ≠ ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨3552⟩ R mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have rd917 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_3552_taken
    (immWords := wordsOf (immStore v)) hstack hwv
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  exact metaMorphoV1_1Blocks.metaMorphoV1_1_block_917
    (immWords := wordsOf (immStore v)) hstack rd917

set_option maxRecDepth 2000 in
theorem setAllocatorRevertLength {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 3 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩)
    (hcond : UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat I.calldata.size) ⟨64⟩ ≠ ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨3552⟩ R mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have rd3558 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_3552_fallthrough
    (immWords := wordsOf (immStore v)) (by omega) hwv rd
  have rd917 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_3558_taken
    (immWords := wordsOf (immStore v)) hstack hcond
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd3558
  exact metaMorphoV1_1Blocks.metaMorphoV1_1_block_917
    (immWords := wordsOf (immStore v)) (by omega) rd917

set_option maxRecDepth 2000 in
theorem setAllocatorReachOwner {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 5 ≤ 1024)
    (hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus)
    (hflag : calldataWord I.calldata 36 = ⟨0⟩ ∨ calldataWord I.calldata 36 = ⟨1⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨11163⟩ (⟨3577⟩ :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ⟨12917⟩
      (⟨3599⟩ :: calldataWord I.calldata 4 :: calldataWord I.calldata 36 :: R)
      mem aw rdata σ k' C' := by
  obtain ⟨_, _, r1⟩ := decodeAddressAt4 v hstack hcanon
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) rd
  have hc : UInt256.sub (calldataWord I.calldata 36)
      (UInt256.isZero (UInt256.isZero (calldataWord I.calldata 36))) = ⟨0⟩ := by
    rcases hflag with h | h <;> rw [h] <;> decide
  have r2 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_3577_fallthrough
    (immWords := wordsOf (immStore v)) (by omega) hc r1
  have r3 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_3592
    (immWords := wordsOf (immStore v)) (by
      simp only [metaMorphoV1_1Blocks.metaMorphoV1_1_block_3577_fallthrough_stack, List.length]
      omega) (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r2
  change RD _ _ _ _ _ (⟨3599⟩ :: calldataWord I.calldata 4 ::
    UInt256.isZero (UInt256.isZero (calldataWord I.calldata 36)) :: R) _ _ _ _ _ _ at r3
  rw [(boolWordClean_iff _).mpr hflag] at r3
  exact ⟨_, _, r3⟩

set_option maxRecDepth 2000 in
theorem setAllocatorRevertFlag {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 5 ≤ 1024)
    (hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus)
    (hbad : ¬ (calldataWord I.calldata 36 = ⟨0⟩ ∨ calldataWord I.calldata 36 = ⟨1⟩))
    (rd : RD (deployedRuntime v) I g s0 ⟨11163⟩ (⟨3577⟩ :: R) mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  obtain ⟨_, _, r1⟩ := decodeAddressAt4 v hstack hcanon
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) rd
  have hc : UInt256.sub (calldataWord I.calldata 36)
      (UInt256.isZero (UInt256.isZero (calldataWord I.calldata 36))) ≠ ⟨0⟩ := by
    intro hz
    apply hbad
    apply (boolWordClean_iff _).mp
    exact (u256_sub_eq_zero_iff_eq.mp hz).symm
  have r2 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_3577_taken
    (immWords := wordsOf (immStore v)) (by omega) hc
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r1
  exact metaMorphoV1_1Blocks.metaMorphoV1_1_block_917
    (immWords := wordsOf (immStore v)) (by
      simp only [metaMorphoV1_1Blocks.metaMorphoV1_1_block_3577_taken_stack, List.length]
      omega) r2

end Benchmarks.Morpho.MetaMorphoV1_1
