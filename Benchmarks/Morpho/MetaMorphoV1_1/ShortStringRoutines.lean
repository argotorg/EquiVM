import Benchmarks.Morpho.MetaMorphoV1_1.ShortStringMemory
import Benchmarks.Morpho.MetaMorphoV1_1.AllocationRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_082
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_083
import Benchmarks.EAS.Attester.WordHelpers

/-! The two instances of immutable short-string decoding and allocation. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

open SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

def shortStringDecodePC (version : Bool) : UInt256 := if version then ⟨18521⟩ else ⟨18425⟩

theorem shortStringReachAllocation {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {word : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (version : Bool) (hstack : R.length + 7 ≤ 1024)
    (hvalid : shortStringValid word)
    (rd : RD (deployedRuntime v) I g s0 (shortStringDecodePC version)
      (word :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨11329⟩
      (memLoad ⟨64⟩ mem :: ⟨64⟩ :: ⟨18452⟩ :: shortStringLength word :: word ::
        memLoad ⟨64⟩ mem :: R) mem aw' rdata σ k' C' := by
  have hc : UInt256.gt (shortStringLength word) (UInt256.ofNat 31) = UInt256.ofNat 0 :=
    ugt_zero hvalid
  cases version with
  | false =>
      have h1 := metaMorphoV1_1_block_18425_fallthrough
        (immWords := wordsOf (immStore v)) (by omega) hc rd
      exact metaMorphoV1_1_block_18438_packed (immWords := wordsOf (immStore v)) hstack
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
  | true =>
      have h1 := metaMorphoV1_1_block_18521_fallthrough
        (immWords := wordsOf (immStore v)) (by omega) hc rd
      exact metaMorphoV1_1_block_18534_packed (immWords := wordsOf (immStore v)) hstack
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1

theorem shortStringDecodeReverts {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {word : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (version : Bool) (hstack : R.length + 5 ≤ 1024)
    (hbad : ¬ shortStringValid word)
    (rd : RD (deployedRuntime v) I g s0 (shortStringDecodePC version)
      (word :: R) mem aw rdata σ k C) : RDrev (deployedRuntime v) g s0 := by
  have hc : UInt256.gt (shortStringLength word) (UInt256.ofNat 31) ≠ UInt256.ofNat 0 := by
    rw [ugt_one (show (UInt256.ofNat 31).toNat < (shortStringLength word).toNat by
      have hn : ¬ (shortStringLength word).toNat ≤ 31 := hbad
      change 31 < _
      omega)]
    decide
  have h1 : RD (deployedRuntime v) I g s0 ⟨18471⟩
      (word :: shortStringLength word :: R) mem aw rdata σ (k + 9) (C + 34) := by
    cases version with
    | false =>
        exact metaMorphoV1_1_block_18425_taken (immWords := wordsOf (immStore v)) (by omega) hc
          (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
    | true =>
        exact metaMorphoV1_1_block_18521_taken (immWords := wordsOf (immStore v)) (by omega) hc
          (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  exact metaMorphoV1_1_block_18471 (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) h1

theorem shortStringAllocatedReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {word ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (free : Nat) (hstack : R.length + 10 ≤ 1024)
    (hsize : I.calldata.size < UInt256.size) (hfit : free + 64 < 2 ^ 64)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨11329⟩
      (UInt256.ofNat free :: ⟨64⟩ :: ⟨18452⟩ :: shortStringLength word :: word ::
        UInt256.ofNat free :: ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ret (UInt256.ofNat free :: R)
      (shortStringMemory mem I.calldata free word) aw' rdata σ k' C' := by
  have hf : free + 64 < UInt256.size := lt_trans hfit (by decide)
  have ha : allocationFits (UInt256.ofNat free) ⟨64⟩ := by
    rw [allocationFits_iff_sum_lt]
    change (UInt256.ofNat free).toNat + 64 < 2 ^ 64
    rw [UInt256.toNat_ofNat_of_lt (by omega)]
    exact hfit
  obtain ⟨aw1, k1, C1, h1⟩ := allocateRoundedReturn v
    (by simp only [List.length_cons]; omega) ha
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) rd
  obtain ⟨aw2, k2, C2, h2⟩ := metaMorphoV1_1_block_18452_packed
    (immWords := wordsOf (immStore v)) (by omega) hret h1
  have hnext : nextCursor (UInt256.ofNat free) ⟨64⟩ = UInt256.ofNat (free + 64) :=
    ofNat_add_words _ _
  have haddr : (UInt256.ofNat 32 + UInt256.ofNat free).toNat = free + 32 := by
    rw [ofNat_add_words, UInt256.toNat_ofNat_of_lt (by omega)]
    omega
  refine ⟨aw2, k2, C2, ?_⟩
  simpa only [metaMorphoV1_1_block_18452_stack, metaMorphoV1_1_block_18452_memory,
    hnext, haddr, UInt256.toNat_ofNat_of_lt hsize,
    UInt256.toNat_ofNat_of_lt (show free < UInt256.size by omega)] using h2

end Benchmarks.Morpho.MetaMorphoV1_1
