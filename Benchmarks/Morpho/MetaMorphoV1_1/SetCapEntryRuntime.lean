import Benchmarks.Morpho.MetaMorphoV1_1.SetCapTailRuntime

/-! Entry hashing and branch selection for the internal cap setter. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

theorem setCapEntryRuntime {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} {params id cap ret : UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 8 ≤ 1024)
    (hcap : cap.toNat < 2 ^ 184)
    (rd : RD (deployedRuntime v) I g s0 ⟨13448⟩
      ([params, id, cap, ret] ++ R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 (if cap = ⟨0⟩ then ⟨13479⟩ else ⟨13562⟩)
      ([params, cap, id, ret, solcMappingSlot ⟨13⟩ id] ++ R)
      (twoWordHashMem id ⟨13⟩ mem) aw' rdata σ k' C' := by
  have hc : UInt256.land
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 184))
        (UInt256.ofNat 1)) cap = cap := by
    change UInt256.land (UInt256.ofNat (2 ^ 184 - 1)) cap = cap
    rw [u256_land_comm]
    exact wordLowMask_eq_self cap 184 (by decide) hcap
  have hh : keccakWord ⟨0⟩ (UInt256.ofNat 64)
      ((UInt256.ofNat 13).toByteArray.write 0
        (id.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32)
        (UInt256.ofNat 32).toNat 32) = solcMappingSlot ⟨13⟩ id :=
    twoWordHashMem_solcMappingSlot_any _ _ _
  by_cases hz : cap = ⟨0⟩
  · rw [if_pos hz]
    have h := metaMorphoV1_1_block_13448_fallthrough
      (immWords := wordsOf (immStore v)) hstack (by rw [hc, hz]; rfl) rd
    dsimp only [metaMorphoV1_1_block_13448_fallthrough_stack] at h
    rw [hc, hh] at h
    exact ⟨_, _, _, h⟩
  · rw [if_neg hz]
    have h := metaMorphoV1_1_block_13448_taken
      (immWords := wordsOf (immStore v)) hstack (by rw [hc]; exact hz)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
    dsimp only [metaMorphoV1_1_block_13448_taken_stack] at h
    rw [hc, hh] at h
    exact ⟨_, _, _, h⟩

def setCapEnabledWord (I : ExecutionEnv) (σ : AccountMap) (id : UInt256) : UInt256 :=
  UInt256.land
    (UInt256.shiftRight (codeOwnerStorageWord I σ (solcMappingSlot ⟨13⟩ id)) ⟨184⟩) ⟨255⟩

theorem setCapEnabledRuntime {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} {params cap id ret : UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 8 ≤ 1024)
    (rd : RD (deployedRuntime v) I g s0 ⟨13562⟩
      ([params, cap, id, ret, solcMappingSlot ⟨13⟩ id] ++ R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0
      (if setCapEnabledWord I σ id = ⟨0⟩ then ⟨13596⟩ else ⟨13576⟩)
      ([params, cap, id, ret, solcMappingSlot ⟨13⟩ id] ++ R) mem aw rdata σ k' C' := by
  by_cases hz : setCapEnabledWord I σ id = ⟨0⟩
  · rw [if_pos hz]
    exact metaMorphoV1_1_block_13562_taken (immWords := wordsOf (immStore v)) hstack
      (by change UInt256.isZero (setCapEnabledWord I σ id) ≠ UInt256.ofNat 0
          rw [hz]; decide)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  · rw [if_neg hz]
    exact metaMorphoV1_1_block_13562_fallthrough (immWords := wordsOf (immStore v)) hstack
      (isZero_eq_zero_of_ne hz) rd

end Benchmarks.Morpho.MetaMorphoV1_1
