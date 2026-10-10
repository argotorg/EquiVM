import Benchmarks.Morpho.MetaMorphoV1_1.MarketRevocationSource
import Benchmarks.Morpho.MetaMorphoV1_1.RevocationRole
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_039
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_040
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_053

/-! The bytecode's guardian, curator, and owner checks for mapping revocations. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode

def marketRevocationRolePC (cap : Bool) : UInt256 := if cap then ⟨10678⟩ else ⟨7757⟩
def marketRevocationCuratorPC (cap : Bool) : UInt256 := if cap then ⟨10784⟩ else ⟨7891⟩
def marketRevocationOwnerChoicePC (cap : Bool) : UInt256 := if cap then ⟨10700⟩ else ⟨7779⟩
def marketRevocationOwnerPC (cap : Bool) : UInt256 := if cap then ⟨10763⟩ else ⟨7870⟩
def marketRevocationRequirePC (cap : Bool) : UInt256 := if cap then ⟨10706⟩ else ⟨7785⟩
def marketRevocationStorePC (cap : Bool) : UInt256 := if cap then ⟨10711⟩ else ⟨7790⟩

set_option maxRecDepth 2000 in
theorem marketRevocationGuardianChoice {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (cap : Bool) (hstack : R.length + 4 ≤ 1024)
    (rd : RD (deployedRuntime v) I g s0 (marketRevocationRolePC cap) R
      mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0
      (if storedRoleMismatch I σ ⟨12⟩ = ⟨0⟩ then marketRevocationOwnerChoicePC cap
        else marketRevocationCuratorPC cap)
      (storedRoleMismatch I σ ⟨12⟩ :: calldataWord I.calldata 4 :: R)
      mem aw rdata σ k' C' := by
  cases cap <;> by_cases hc : storedRoleMismatch I σ ⟨12⟩ = ⟨0⟩
  · rw [if_pos hc]
    have h := metaMorphoV1_1_block_7757_fallthrough
      (immWords := wordsOf (immStore v)) hstack (by
        simpa only [storedRoleMismatch, u256_land_comm] using hc)
      rd
    simpa only [metaMorphoV1_1_block_7757_fallthrough_stack, storedRoleMismatch,
      u256_land_comm] using h
  · rw [if_neg hc]
    have h := metaMorphoV1_1_block_7757_taken
      (immWords := wordsOf (immStore v)) hstack (by
        simpa only [storedRoleMismatch, u256_land_comm] using hc)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest)
      rd
    simpa only [metaMorphoV1_1_block_7757_taken_stack, storedRoleMismatch,
      u256_land_comm] using h
  · rw [if_pos hc]
    have h := metaMorphoV1_1_block_10678_fallthrough
      (immWords := wordsOf (immStore v)) hstack (by
        simpa only [storedRoleMismatch, u256_land_comm] using hc)
      rd
    simpa only [metaMorphoV1_1_block_10678_fallthrough_stack, storedRoleMismatch,
      u256_land_comm] using h
  · rw [if_neg hc]
    have h := metaMorphoV1_1_block_10678_taken
      (immWords := wordsOf (immStore v)) hstack (by
        simpa only [storedRoleMismatch, u256_land_comm] using hc)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest)
      rd
    simpa only [metaMorphoV1_1_block_10678_taken_stack, storedRoleMismatch,
      u256_land_comm] using h

set_option maxRecDepth 2000 in
theorem marketRevocationCuratorLookup {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} {x : UInt256}
    (v : MetaMorphoV1_1Immutables) (cap : Bool) (hstack : R.length + 4 ≤ 1024)
    (rd : RD (deployedRuntime v) I g s0 (marketRevocationCuratorPC cap) (x :: R)
      mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 (marketRevocationOwnerChoicePC cap)
      (storedRoleMismatch I σ ⟨10⟩ :: R) mem aw rdata σ k' C' := by
  cases cap
  · exact metaMorphoV1_1_block_7891 (immWords := wordsOf (immStore v)) hstack
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  · exact metaMorphoV1_1_block_10784 (immWords := wordsOf (immStore v)) hstack
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd

set_option maxRecDepth 2000 in
theorem marketRevocationOwnerLookup {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} {x : UInt256}
    (v : MetaMorphoV1_1Immutables) (cap : Bool) (hstack : R.length + 4 ≤ 1024)
    (rd : RD (deployedRuntime v) I g s0 (marketRevocationOwnerPC cap) (x :: R)
      mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 (marketRevocationRequirePC cap)
      (storedRoleMismatch I σ ⟨8⟩ :: R) mem aw rdata σ k' C' := by
  cases cap
  · exact metaMorphoV1_1_block_7870 (immWords := wordsOf (immStore v)) hstack
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  · exact metaMorphoV1_1_block_10763 (immWords := wordsOf (immStore v)) hstack
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd

set_option maxRecDepth 2000 in
theorem marketRevocationOwnerChoice {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} {x : UInt256}
    (v : MetaMorphoV1_1Immutables) (cap : Bool) (hstack : R.length + 3 ≤ 1024)
    (rd : RD (deployedRuntime v) I g s0 (marketRevocationOwnerChoicePC cap) (x :: R)
      mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0
      (if x = ⟨0⟩ then marketRevocationRequirePC cap else marketRevocationOwnerPC cap)
      (x :: R) mem aw rdata σ k' C' := by
  cases cap <;> by_cases hc : x = ⟨0⟩
  · rw [if_pos hc]
    exact ⟨_, _, metaMorphoV1_1_block_7779_fallthrough
      (immWords := wordsOf (immStore v)) hstack hc rd⟩
  · rw [if_neg hc]
    exact ⟨_, _, metaMorphoV1_1_block_7779_taken
      (immWords := wordsOf (immStore v)) hstack hc
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd⟩
  · rw [if_pos hc]
    exact ⟨_, _, metaMorphoV1_1_block_10700_fallthrough
      (immWords := wordsOf (immStore v)) hstack hc rd⟩
  · rw [if_neg hc]
    exact ⟨_, _, metaMorphoV1_1_block_10700_taken
      (immWords := wordsOf (immStore v)) hstack hc
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd⟩

set_option maxRecDepth 2000 in
theorem marketRevocationRequirePass {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (cap : Bool) (hstack : R.length + 2 ≤ 1024)
    (rd : RD (deployedRuntime v) I g s0 (marketRevocationRequirePC cap) (⟨0⟩ :: R)
      mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 (marketRevocationStorePC cap) R
      mem aw rdata σ k' C' := by
  cases cap
  · exact ⟨_, _, metaMorphoV1_1_block_7785_fallthrough
      (immWords := wordsOf (immStore v)) hstack rfl rd⟩
  · exact ⟨_, _, metaMorphoV1_1_block_10706_fallthrough
      (immWords := wordsOf (immStore v)) hstack rfl rd⟩

set_option maxRecDepth 2000 in
theorem marketRevocationRequireFail {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} {x : UInt256}
    (v : MetaMorphoV1_1Immutables) (cap : Bool) (hstack : R.length + 2 ≤ 1024)
    (hx : x ≠ ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 (marketRevocationRequirePC cap) (x :: R)
      mem aw rdata σ k C) : RDrev (deployedRuntime v) g s0 := by
  have r1 : ∃ k' C', RD (deployedRuntime v) I g s0 ⟨7855⟩ R mem aw rdata σ k' C' := by
    cases cap
    · exact ⟨_, _, metaMorphoV1_1_block_7785_taken
        (immWords := wordsOf (immStore v)) hstack hx
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd⟩
    · exact ⟨_, _, metaMorphoV1_1_block_10706_taken
        (immWords := wordsOf (immStore v)) hstack hx
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd⟩
  obtain ⟨_, _, r1⟩ := r1
  exact metaMorphoV1_1_block_7855 (immWords := wordsOf (immStore v)) hstack r1

set_option maxRecDepth 2000 in
theorem marketRevocationReachStore {evm : EVM.State} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (cap : Bool) (hstack : R.length + 5 ≤ 1024)
    (hrole : curatorGuardianAllowed evm)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 (marketRevocationRolePC cap) R
      mem aw rdata evm.accountMap k C) :
    ∃ k' C', RD (deployedRuntime v) evm.executionEnv g s0 (marketRevocationStorePC cap)
      (calldataWord evm.executionEnv.calldata 4 :: R) mem aw rdata evm.accountMap k' C' := by
  obtain ⟨_, _, r1⟩ := marketRevocationGuardianChoice v cap (by omega) rd
  have hjoin : ∃ k' C', RD (deployedRuntime v) evm.executionEnv g s0
      (marketRevocationRequirePC cap) (⟨0⟩ :: calldataWord evm.executionEnv.calldata 4 :: R)
      mem aw rdata evm.accountMap k' C' := by
    by_cases hg : guardianAddress evm = evm.executionEnv.source
    · have hz := storedRoleMismatch_match evm.executionEnv evm.accountMap ⟨12⟩ hg
      simp only [hz, ↓reduceIte] at r1
      obtain ⟨_, _, r2⟩ := marketRevocationOwnerChoice v cap
        (by simp only [List.length_cons]; omega) r1
      simpa only [↓reduceIte] using ⟨_, _, r2⟩
    · have hn := storedRoleMismatch_ne evm.executionEnv evm.accountMap ⟨12⟩ hg
      simp only [hn, ↓reduceIte] at r1
      obtain ⟨_, _, r2⟩ := marketRevocationCuratorLookup v cap
        (by simp only [List.length_cons]; omega) r1
      obtain ⟨_, _, r3⟩ := marketRevocationOwnerChoice v cap
        (by simp only [List.length_cons]; omega) r2
      by_cases hc : curatorAddress evm = evm.executionEnv.source
      · have hz := storedRoleMismatch_match evm.executionEnv evm.accountMap ⟨10⟩ hc
        simp only [hz, ↓reduceIte] at r3
        exact ⟨_, _, r3⟩
      · have hn := storedRoleMismatch_ne evm.executionEnv evm.accountMap ⟨10⟩ hc
        simp only [hn, ↓reduceIte] at r3
        obtain ⟨_, _, r4⟩ := marketRevocationOwnerLookup v cap
          (by simp only [List.length_cons]; omega) r3
        have hz := storedRoleMismatch_match evm.executionEnv evm.accountMap ⟨8⟩
          ((hrole.resolve_left hg).resolve_left hc)
        rw [hz] at r4
        exact ⟨_, _, r4⟩
  obtain ⟨_, _, r2⟩ := hjoin
  exact marketRevocationRequirePass v cap (by simp only [List.length_cons]; omega) r2

set_option maxRecDepth 2000 in
theorem marketRevocationRevertRole {evm : EVM.State} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (cap : Bool) (hstack : R.length + 5 ≤ 1024)
    (hrole : ¬ curatorGuardianAllowed evm)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 (marketRevocationRolePC cap) R
      mem aw rdata evm.accountMap k C) : RDrev (deployedRuntime v) g s0 := by
  have hg := storedRoleMismatch_ne evm.executionEnv evm.accountMap ⟨12⟩
    (fun h ↦ hrole (Or.inl h))
  have hc := storedRoleMismatch_ne evm.executionEnv evm.accountMap ⟨10⟩
    (fun h ↦ hrole (Or.inr (Or.inl h)))
  have ho := storedRoleMismatch_ne evm.executionEnv evm.accountMap ⟨8⟩
    (fun h ↦ hrole (Or.inr (Or.inr h)))
  obtain ⟨_, _, r1⟩ := marketRevocationGuardianChoice v cap (by omega) rd
  simp only [hg, ↓reduceIte] at r1
  obtain ⟨_, _, r2⟩ := marketRevocationCuratorLookup v cap
    (by simp only [List.length_cons]; omega) r1
  obtain ⟨_, _, r3⟩ := marketRevocationOwnerChoice v cap
    (by simp only [List.length_cons]; omega) r2
  simp only [hc, ↓reduceIte] at r3
  obtain ⟨_, _, r4⟩ := marketRevocationOwnerLookup v cap
    (by simp only [List.length_cons]; omega) r3
  exact marketRevocationRequireFail v cap (by simp only [List.length_cons]; omega) ho r4

end Benchmarks.Morpho.MetaMorphoV1_1
