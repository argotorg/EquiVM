import Benchmarks.Morpho.MetaMorphoV1_1.CuratorRoleSource
import Benchmarks.Morpho.MetaMorphoV1_1.RevocationRole
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_028
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_029

/-! Curator and owner authorization in the market-removal entry point. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

theorem marketRemovalCuratorChoice {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 4 ≤ 1024)
    (rd : RD (deployedRuntime v) I g s0 ⟨5222⟩ R mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0
      (if storedRoleMismatch I σ ⟨10⟩ = ⟨0⟩ then ⟨5243⟩ else ⟨5518⟩)
      (storedRoleMismatch I σ ⟨10⟩ :: R) mem aw rdata σ k' C' := by
  by_cases hc : storedRoleMismatch I σ ⟨10⟩ = ⟨0⟩
  · rw [if_pos hc]
    have h := metaMorphoV1_1_block_5222_fallthrough
      (immWords := wordsOf (immStore v)) hstack
      (by simpa only [storedRoleMismatch, u256_land_comm] using hc) rd
    simpa only [metaMorphoV1_1_block_5222_fallthrough_stack, storedRoleMismatch,
      u256_land_comm] using h
  · rw [if_neg hc]
    have h := metaMorphoV1_1_block_5222_taken
      (immWords := wordsOf (immStore v)) hstack
      (by simpa only [storedRoleMismatch, u256_land_comm] using hc)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
    simpa only [metaMorphoV1_1_block_5222_taken_stack, storedRoleMismatch,
      u256_land_comm] using h

theorem marketRemovalOwnerLookup {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} {x : UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 4 ≤ 1024)
    (rd : RD (deployedRuntime v) I g s0 ⟨5518⟩ (x :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ⟨5243⟩
      (storedRoleMismatch I σ ⟨8⟩ :: R) mem aw rdata σ k' C' := by
  exact metaMorphoV1_1_block_5518 (immWords := wordsOf (immStore v)) hstack
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd

theorem marketRemovalRolePass {evm : State} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 4 ≤ 1024)
    (hrole : curatorRoleAllowed evm)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 ⟨5222⟩ R
      mem aw rdata evm.accountMap k C) :
    ∃ k' C', RD (deployedRuntime v) evm.executionEnv g s0 ⟨5248⟩ R
      mem aw rdata evm.accountMap k' C' := by
  obtain ⟨_, _, r1⟩ := marketRemovalCuratorChoice v hstack rd
  have hjoin : ∃ k' C', RD (deployedRuntime v) evm.executionEnv g s0 ⟨5243⟩
      (⟨0⟩ :: R) mem aw rdata evm.accountMap k' C' := by
    by_cases hc : curatorAddress evm = evm.executionEnv.source
    · have hz := storedRoleMismatch_match evm.executionEnv evm.accountMap ⟨10⟩ hc
      simp only [hz, ↓reduceIte] at r1
      exact ⟨_, _, r1⟩
    · have hn := storedRoleMismatch_ne evm.executionEnv evm.accountMap ⟨10⟩ hc
      simp only [hn, ↓reduceIte] at r1
      obtain ⟨_, _, r2⟩ := marketRemovalOwnerLookup v hstack r1
      have hz := storedRoleMismatch_match evm.executionEnv evm.accountMap ⟨8⟩
        (hrole.resolve_left hc)
      rw [hz] at r2
      exact ⟨_, _, r2⟩
  obtain ⟨_, _, r2⟩ := hjoin
  exact ⟨_, _, metaMorphoV1_1_block_5243_fallthrough
    (immWords := wordsOf (immStore v)) (by omega) rfl r2⟩

theorem marketRemovalRoleRevert {evm : State} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 4 ≤ 1024)
    (hrole : ¬ curatorRoleAllowed evm)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 ⟨5222⟩ R
      mem aw rdata evm.accountMap k C) : RDrev (deployedRuntime v) g s0 := by
  have hc := storedRoleMismatch_ne evm.executionEnv evm.accountMap ⟨10⟩
    (fun h ↦ hrole (Or.inl h))
  have ho := storedRoleMismatch_ne evm.executionEnv evm.accountMap ⟨8⟩
    (fun h ↦ hrole (Or.inr h))
  obtain ⟨_, _, r1⟩ := marketRemovalCuratorChoice v hstack rd
  simp only [hc, ↓reduceIte] at r1
  obtain ⟨_, _, r2⟩ := marketRemovalOwnerLookup v hstack r1
  have r3 := metaMorphoV1_1_block_5243_taken
    (immWords := wordsOf (immStore v)) (by omega) ho
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r2
  exact metaMorphoV1_1_block_5503 (immWords := wordsOf (immStore v))
    (by simpa only [metaMorphoV1_1_block_5243_taken_stack] using (by omega : R.length + 2 ≤ 1024))
    r3

end Benchmarks.Morpho.MetaMorphoV1_1
