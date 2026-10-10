import Benchmarks.Morpho.MetaMorphoV1_1.MarketRevocationRole
import Benchmarks.Morpho.MetaMorphoV1_1.Decode
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_009

/-! ABI entry guards for cap and market-removal marketRevocations. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode

def marketRevocationEntryPC (cap : Bool) : UInt256 := if cap then ⟨10660⟩ else ⟨7739⟩

set_option maxRecDepth 2000 in
theorem marketRevocationReachRole {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (cap : Bool) (hstack : R.length + 3 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩) (hsz : 36 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4) (hsize : I.calldata.size < UInt256.size)
    (rd : RD (deployedRuntime v) I g s0 (marketRevocationEntryPC cap) R mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 (marketRevocationRolePC cap) R
      mem aw rdata σ k' C' := by
  cases cap
  · have r1 := metaMorphoV1_1_block_7739_fallthrough
      (immWords := wordsOf (immStore v)) (by omega) hwv rd
    exact ⟨_, _, metaMorphoV1_1_block_7745_fallthrough
      (immWords := wordsOf (immStore v)) hstack (by
        change UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat I.calldata.size) ⟨32⟩ = ⟨0⟩
        rw [calldataNot3_eq_sub (by omega) hsize]
        exact solcDecodeLenCheckOk_4_32 hsz hhi hsize) r1⟩
  · have r1 := metaMorphoV1_1_block_10660_fallthrough
      (immWords := wordsOf (immStore v)) (by omega) hwv rd
    exact ⟨_, _, metaMorphoV1_1_block_10666_fallthrough
      (immWords := wordsOf (immStore v)) hstack (by
        change UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat I.calldata.size) ⟨32⟩ = ⟨0⟩
        rw [calldataNot3_eq_sub (by omega) hsize]
        exact solcDecodeLenCheckOk_4_32 hsz hhi hsize) r1⟩

set_option maxRecDepth 2000 in
theorem marketRevocationRevertNonPayable {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (cap : Bool) (hstack : R.length + 2 ≤ 1024)
    (hwv : I.weiValue ≠ ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 (marketRevocationEntryPC cap) R mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have r1 : ∃ k' C', RD (deployedRuntime v) I g s0 ⟨917⟩ R mem aw rdata σ k' C' := by
    cases cap
    · exact ⟨_, _, metaMorphoV1_1_block_7739_taken
        (immWords := wordsOf (immStore v)) hstack hwv
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd⟩
    · exact ⟨_, _, metaMorphoV1_1_block_10660_taken
        (immWords := wordsOf (immStore v)) hstack hwv
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd⟩
  obtain ⟨_, _, r1⟩ := r1
  exact metaMorphoV1_1_block_917 (immWords := wordsOf (immStore v)) hstack r1

set_option maxRecDepth 2000 in
theorem marketRevocationRevertLength {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (cap : Bool) (hstack : R.length + 3 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩)
    (hc : UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat I.calldata.size) ⟨32⟩ ≠ ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 (marketRevocationEntryPC cap) R mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have r1 : ∃ k' C', RD (deployedRuntime v) I g s0 ⟨917⟩ R mem aw rdata σ k' C' := by
    cases cap
    · have r0 := metaMorphoV1_1_block_7739_fallthrough
        (immWords := wordsOf (immStore v)) (by omega) hwv rd
      exact ⟨_, _, metaMorphoV1_1_block_7745_taken
        (immWords := wordsOf (immStore v)) hstack hc
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r0⟩
    · have r0 := metaMorphoV1_1_block_10660_fallthrough
        (immWords := wordsOf (immStore v)) (by omega) hwv rd
      exact ⟨_, _, metaMorphoV1_1_block_10666_taken
        (immWords := wordsOf (immStore v)) hstack hc
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r0⟩
  obtain ⟨_, _, r1⟩ := r1
  exact metaMorphoV1_1_block_917 (immWords := wordsOf (immStore v)) (by omega) r1

end Benchmarks.Morpho.MetaMorphoV1_1
