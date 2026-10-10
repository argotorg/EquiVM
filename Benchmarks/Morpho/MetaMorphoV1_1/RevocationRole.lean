import Benchmarks.Morpho.MetaMorphoV1_1.RevocationSource
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_014
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_052

/-! Bytecode authorization for pending guardian and timelock revocations. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode

def revocationRolePC (guardian : Bool) : UInt256 := if guardian then ⟨10543⟩ else ⟨2070⟩
def revocationGuardianPC (guardian : Bool) : UInt256 := if guardian then ⟨10610⟩ else ⟨2152⟩
def revocationRequirePC (guardian : Bool) : UInt256 := if guardian then ⟨10563⟩ else ⟨2090⟩
def revocationStorePC (guardian : Bool) : UInt256 := if guardian then ⟨10568⟩ else ⟨2095⟩

def storedRoleMismatch (I : ExecutionEnv) (σ : AccountMap) (slot : UInt256) : UInt256 :=
  UInt256.isZero (UInt256.eq (UInt256.ofNat I.source.val)
    (UInt256.land solcAddrMask (codeOwnerStorageWord I σ slot)))

theorem storedRoleMismatch_match (I : ExecutionEnv) (σ : AccountMap) (slot : UInt256)
    (h : AccountAddress.ofNat (UInt256.land (codeOwnerStorageWord I σ slot)
      solcAddrMask).toNat = I.source) : storedRoleMismatch I σ slot = ⟨0⟩ := by
  have hw := (maskedAddress_eq_iff_word _ _).mp h
  rw [storedRoleMismatch, u256_land_comm, ← hw]
  simp only [UInt256.eq]
  decide

theorem storedRoleMismatch_ne (I : ExecutionEnv) (σ : AccountMap) (slot : UInt256)
    (h : AccountAddress.ofNat (UInt256.land (codeOwnerStorageWord I σ slot)
      solcAddrMask).toNat ≠ I.source) : storedRoleMismatch I σ slot ≠ ⟨0⟩ := by
  have hw := (maskedAddress_eq_iff_word _ _).not.mp h
  rw [storedRoleMismatch, u256_land_comm, u256_eq_of_ne hw]
  decide

set_option maxRecDepth 2000 in
theorem revocationOwnerChoice {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (guardian : Bool) (hstack : R.length + 4 ≤ 1024)
    (rd : RD (deployedRuntime v) I g s0 (revocationRolePC guardian) R mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0
      (if storedRoleMismatch I σ ⟨8⟩ = ⟨0⟩ then revocationRequirePC guardian
        else revocationGuardianPC guardian)
      (storedRoleMismatch I σ ⟨8⟩ :: R) mem aw rdata σ k' C' := by
  cases guardian <;> by_cases hc : storedRoleMismatch I σ ⟨8⟩ = ⟨0⟩
  · rw [if_pos hc]
    exact metaMorphoV1_1_block_2070_fallthrough
      (immWords := wordsOf (immStore v)) hstack hc rd
  · simpa only [hc, ↓reduceIte] using
      (metaMorphoV1_1_block_2070_taken (immWords := wordsOf (immStore v)) hstack hc
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd)
  · rw [if_pos hc]
    exact metaMorphoV1_1_block_10543_fallthrough
      (immWords := wordsOf (immStore v)) hstack hc rd
  · simpa only [hc, ↓reduceIte] using
      (metaMorphoV1_1_block_10543_taken (immWords := wordsOf (immStore v)) hstack hc
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd)

set_option maxRecDepth 2000 in
theorem revocationGuardianComparison {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} {x : UInt256}
    (v : MetaMorphoV1_1Immutables) (guardian : Bool) (hstack : R.length + 4 ≤ 1024)
    (rd : RD (deployedRuntime v) I g s0 (revocationGuardianPC guardian) (x :: R)
      mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 (revocationRequirePC guardian)
      (storedRoleMismatch I σ ⟨12⟩ :: R) mem aw rdata σ k' C' := by
  cases guardian
  · exact metaMorphoV1_1_block_2152 (immWords := wordsOf (immStore v)) hstack
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  · exact metaMorphoV1_1_block_10610 (immWords := wordsOf (immStore v)) hstack
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd

set_option maxRecDepth 2000 in
theorem revocationReachStore {evm : EVM.State} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (guardian : Bool) (hstack : R.length + 4 ≤ 1024)
    (hrole : guardianRoleAllowed evm)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 (revocationRolePC guardian) R
      mem aw rdata evm.accountMap k C) :
    ∃ k' C', RD (deployedRuntime v) evm.executionEnv g s0 (revocationStorePC guardian) R
      mem aw rdata evm.accountMap k' C' := by
  obtain ⟨k1, C1, r1⟩ := revocationOwnerChoice v guardian hstack rd
  have hjoin : ∃ k' C', RD (deployedRuntime v) evm.executionEnv g s0
      (revocationRequirePC guardian) (⟨0⟩ :: R) mem aw rdata evm.accountMap k' C' := by
    by_cases ho : ownerAddress evm = evm.executionEnv.source
    · have hz := storedRoleMismatch_match evm.executionEnv evm.accountMap ⟨8⟩ ho
      simp only [hz, ↓reduceIte] at r1
      exact ⟨_, _, r1⟩
    · have hn := storedRoleMismatch_ne evm.executionEnv evm.accountMap ⟨8⟩ ho
      simp only [hn, ↓reduceIte] at r1
      obtain ⟨_, _, r2⟩ := revocationGuardianComparison v guardian hstack r1
      have hz := storedRoleMismatch_match evm.executionEnv evm.accountMap ⟨12⟩
        (hrole.resolve_left ho)
      rw [hz] at r2
      exact ⟨_, _, r2⟩
  obtain ⟨_, _, r2⟩ := hjoin
  cases guardian
  · exact ⟨_, _, metaMorphoV1_1_block_2090_fallthrough
      (immWords := wordsOf (immStore v)) (by omega) rfl r2⟩
  · exact ⟨_, _, metaMorphoV1_1_block_10563_fallthrough
      (immWords := wordsOf (immStore v)) (by omega) rfl r2⟩

set_option maxRecDepth 2000 in
theorem revocationRevertRole {evm : EVM.State} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (guardian : Bool) (hstack : R.length + 4 ≤ 1024)
    (hrole : ¬ guardianRoleAllowed evm)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 (revocationRolePC guardian) R
      mem aw rdata evm.accountMap k C) : RDrev (deployedRuntime v) g s0 := by
  have ho := storedRoleMismatch_ne evm.executionEnv evm.accountMap ⟨8⟩
    (fun h ↦ hrole (Or.inl h))
  have hg := storedRoleMismatch_ne evm.executionEnv evm.accountMap ⟨12⟩
    (fun h ↦ hrole (Or.inr h))
  obtain ⟨_, _, r1⟩ := revocationOwnerChoice v guardian hstack rd
  simp only [ho, ↓reduceIte] at r1
  obtain ⟨_, _, r2⟩ := revocationGuardianComparison v guardian hstack r1
  have r3 : ∃ k' C', RD (deployedRuntime v) evm.executionEnv g s0 ⟨2137⟩ R
      mem aw rdata evm.accountMap k' C' := by
    cases guardian
    · exact ⟨_, _, metaMorphoV1_1_block_2090_taken
        (immWords := wordsOf (immStore v)) (by omega) hg
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r2⟩
    · exact ⟨_, _, metaMorphoV1_1_block_10563_taken
        (immWords := wordsOf (immStore v)) (by omega) hg
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r2⟩
  obtain ⟨_, _, r3⟩ := r3
  exact metaMorphoV1_1_block_2137 (immWords := wordsOf (immStore v)) (by omega) r3

end Benchmarks.Morpho.MetaMorphoV1_1
