import Benchmarks.Morpho.MetaMorphoV1_1.Decode
import Benchmarks.Morpho.MetaMorphoV1_1.Eip712StringRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_027

/-! Public domain-view guards and entry points for its two string calls. -/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000
set_option autoImplicit false

theorem eip712ReachName {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 4 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩) (hsz : 4 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4) (hsize : I.calldata.size < UInt256.size)
    (rd : RD (deployedRuntime v) I g s0 ⟨4948⟩ R mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 (domainStringPC false)
      (domainStringImmutable v false :: ⟨5008⟩ :: ⟨5104⟩ :: R) mem aw' rdata σ k' C' := by
  have h1 := metaMorphoV1_1_block_4948_fallthrough
    (immWords := wordsOf (immStore v)) (by omega) hwv rd
  have h2 := metaMorphoV1_1_block_4954_fallthrough
    (immWords := wordsOf (immStore v)) (by omega) (calldataLengthCheckOk hsz hhi hsize) h1
  obtain ⟨aw', k', C', h⟩ := metaMorphoV1_1_block_4965_packed
    (immWords := wordsOf (immStore v)) hstack
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2
  exact ⟨aw', k', C', by
    simpa only [metaMorphoV1_1_block_4965_stack, wordsOf_immStore__name,
      wordOfInt_ofNat_toNat_gen, u256_ofNat_toNat, domainStringPC, domainStringImmutable,
      Bool.false_eq_true, if_false] using h⟩

theorem eip712ReachVersion {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 3 ≤ 1024)
    (rd : RD (deployedRuntime v) I g s0 ⟨5008⟩ R mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 (domainStringPC true)
      (domainStringImmutable v true :: ⟨5049⟩ :: R) mem aw' rdata σ k' C' := by
  obtain ⟨aw', k', C', h⟩ := metaMorphoV1_1_block_5008_packed
    (immWords := wordsOf (immStore v)) hstack
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  exact ⟨aw', k', C', by
    simpa only [metaMorphoV1_1_block_5008_stack, wordsOf_immStore__version,
      wordOfInt_ofNat_toNat_gen, u256_ofNat_toNat, domainStringPC, domainStringImmutable,
      if_true] using h⟩

theorem eip712RevertNonPayable {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 2 ≤ 1024)
    (hwv : I.weiValue ≠ ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨4948⟩ R mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have h1 := metaMorphoV1_1_block_4948_taken (immWords := wordsOf (immStore v)) hstack hwv
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  exact metaMorphoV1_1_block_917 (immWords := wordsOf (immStore v)) hstack h1

theorem eip712RevertHuge {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 3 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩) (hhi : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (rd : RD (deployedRuntime v) I g s0 ⟨4948⟩ R mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have h1 := metaMorphoV1_1_block_4948_fallthrough
    (immWords := wordsOf (immStore v)) (by omega) hwv rd
  have h2 := metaMorphoV1_1_block_4954_taken (immWords := wordsOf (immStore v)) hstack (by
    change UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat I.calldata.size) ⟨0⟩ ≠ ⟨0⟩
    rw [calldataLengthCheckHuge hhi hsize]
    decide) (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
  exact metaMorphoV1_1_block_917 (immWords := wordsOf (immStore v)) (by omega) h2

end Benchmarks.Morpho.MetaMorphoV1_1
