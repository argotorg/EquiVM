import Benchmarks.Morpho.MetaMorphoV1_1.MarketRemovalRole
import Benchmarks.Morpho.MetaMorphoV1_1.MarketRemovalStorage
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_025

/-! The bytecode's four storage guards before scheduling market removal. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

theorem marketRemovalGuardsReach {evm : State} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {k C : Nat} {R : List UInt256} {ptr id : UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 6 ≤ 1024)
    (hid : keccakWord ptr ⟨160⟩ mem = id)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 ⟨5248⟩ (ptr :: R)
      mem aw rdata evm.accountMap k C) :
    (¬ marketRemovalAllowed evm id ∧ RDrev (deployedRuntime v) g s0) ∨
    (marketRemovalAllowed evm id ∧ ∃ mem' aw' k' C',
      RD (deployedRuntime v) evm.executionEnv g s0 ⟨5343⟩ (id :: R)
        mem' aw' rdata evm.accountMap k' C') := by
  have hid' : keccakWord ptr (UInt256.ofNat 160) mem = id := hid
  have hh (m : ByteArray) (base : UInt256) :
      keccakWord ⟨0⟩ (UInt256.ofNat 64)
        (base.toByteArray.write 0 (id.toByteArray.write 0 m (⟨0⟩ : UInt256).toNat 32)
          (UInt256.ofNat 32).toNat 32) =
          solcMappingSlot base id := twoWordHashMem_solcMappingSlot_any _ _ _
  have hmask : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 184))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 184 - 1) := by decide +kernel
  by_cases hc0 : marketRemovalRemovableAt evm id = ⟨0⟩
  case neg =>
    obtain ⟨_, _, _, hbad⟩ := metaMorphoV1_1_block_5248_taken_packed
      (immWords := wordsOf (immStore v)) (by omega)
      (by rw [hid', hh]; exact hc0)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
    exact .inl ⟨fun h ↦ hc0 h.1,
      metaMorphoV1_1_block_4572 (immWords := wordsOf (immStore v))
        (by simp only [metaMorphoV1_1_block_5248_taken_stack, List.length_cons]; omega) hbad⟩
  obtain ⟨aw0, k0, C0, r0⟩ := metaMorphoV1_1_block_5248_fallthrough_packed
    (immWords := wordsOf (immStore v)) (by omega)
    (by rw [hid', hh]; exact hc0) rd
  simp only [metaMorphoV1_1_block_5248_fallthrough_stack, hid'] at r0
  by_cases hc1 : marketRemovalCap evm id = ⟨0⟩
  case neg =>
    obtain ⟨_, _, _, hbad⟩ := metaMorphoV1_1_block_5272_taken_packed
      (immWords := wordsOf (immStore v)) (by omega)
      (by rw [hh, hmask, u256_land_comm]; exact hc1)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r0
    exact .inl ⟨fun h ↦ hc1 h.2.1,
      metaMorphoV1_1_block_5488 (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) hbad⟩
  obtain ⟨aw1, k1, C1, r1⟩ := metaMorphoV1_1_block_5272_fallthrough_packed
    (immWords := wordsOf (immStore v)) (by omega)
    (by rw [hh, hmask, u256_land_comm]; exact hc1) r0
  by_cases hc2 : marketRemovalEnabledWord evm id ≠ ⟨0⟩
  case neg =>
    obtain ⟨_, _, _, hbad⟩ := metaMorphoV1_1_block_5299_taken_packed
      (immWords := wordsOf (immStore v)) (by omega)
      (by
        rw [hh]
        have hz : marketRemovalEnabledWord evm id = ⟨0⟩ := not_ne_iff.mp hc2
        change UInt256.isZero (marketRemovalEnabledWord evm id) ≠ ⟨0⟩
        rw [hz]; decide)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r1
    exact .inl ⟨fun h ↦ hc2 h.2.2.1,
      metaMorphoV1_1_block_5470 (immWords := wordsOf (immStore v))
        (by omega) hbad⟩
  obtain ⟨aw2, k2, C2, r2⟩ := metaMorphoV1_1_block_5299_fallthrough_packed
    (immWords := wordsOf (immStore v)) (by omega)
    (by
      rw [hh]
      exact isZero_eq_zero_of_ne hc2) r1
  by_cases hc3 : marketRemovalPendingAt evm id = ⟨0⟩
  case neg =>
    obtain ⟨_, _, _, hbad⟩ := metaMorphoV1_1_block_5323_taken_packed
      (immWords := wordsOf (immStore v)) (by omega)
      (by rw [hh]; exact hc3)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r2
    exact .inl ⟨fun h ↦ hc3 h.2.2.2,
      metaMorphoV1_1_block_5453 (immWords := wordsOf (immStore v))
        (by omega) hbad⟩
  obtain ⟨aw3, k3, C3, r3⟩ := metaMorphoV1_1_block_5323_fallthrough_packed
    (immWords := wordsOf (immStore v)) (by omega)
    (by rw [hh]; exact hc3) r2
  exact .inr ⟨⟨hc0, hc1, hc2, hc3⟩, _, aw3, k3, C3, r3⟩

end Benchmarks.Morpho.MetaMorphoV1_1
