import Benchmarks.Morpho.MetaMorphoV1_1.LastUpdateSource
import Benchmarks.Morpho.MetaMorphoV1_1.MappingScratchMemory
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_010
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_025
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_045
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_046

/-! Last-update and storage guards before choosing a cap-submission branch. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

open SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

abbrev submitCapGuardsAllowed (evm : State) (id cap last : UInt256) : Prop :=
  last ≠ ⟨0⟩ ∧ marketRemovalPendingAt evm id = ⟨0⟩ ∧
    marketRemovalRemovableAt evm id = ⟨0⟩ ∧ cap ≠ marketRemovalCap evm id

def submitCapGuardMemory (mem : ByteArray) (id : UInt256) : ByteArray :=
  twoWordHashMem id ⟨13⟩ (twoWordHashMem id ⟨13⟩ (twoWordHashMem id ⟨16⟩ mem))

theorem submitCapGuardMemory_prefix (mem : ByteArray) (id : UInt256) (limit : Nat) :
    MemoryPrefix mem (submitCapGuardMemory mem id) limit :=
  ((twoWordHashMem_prefix mem id ⟨16⟩ limit).trans
    (twoWordHashMem_prefix (twoWordHashMem id ⟨16⟩ mem) id ⟨13⟩ limit)).trans
    (twoWordHashMem_prefix (twoWordHashMem id ⟨13⟩ (twoWordHashMem id ⟨16⟩ mem))
      id ⟨13⟩ limit)

theorem submitCapGuardMemory_size {mem : ByteArray} (id : UInt256) (hmem : 64 ≤ mem.size) :
    (submitCapGuardMemory mem id).size = mem.size := by
  have h1 := twoWordHashMem_size_of_ge_64' id ⟨16⟩ hmem
  have h2 := twoWordHashMem_size_of_ge_64' id ⟨13⟩ (by rw [h1]; exact hmem)
  rw [submitCapGuardMemory, twoWordHashMem_size_of_ge_64' _ _ (by
    rw [h2, h1]; exact hmem), h2, h1]

theorem submitCapGuardMemory_free {mem : ByteArray} (id : UInt256) (hmem : 96 ≤ mem.size) :
    memLoad ⟨64⟩ (submitCapGuardMemory mem id) = memLoad ⟨64⟩ mem := by
  have h1 : 96 ≤ (twoWordHashMem id ⟨16⟩ mem).size := by
    rw [twoWordHashMem_size_of_ge_64' _ _ (by omega)]; exact hmem
  have h2 : 96 ≤ (twoWordHashMem id ⟨13⟩ (twoWordHashMem id ⟨16⟩ mem)).size := by
    rw [twoWordHashMem_size_of_ge_64' _ _ (by omega)]; exact h1
  rw [submitCapGuardMemory, twoWordHashMem_free _ _ h2, twoWordHashMem_free _ _ h1,
    twoWordHashMem_free _ _ hmem]

theorem submitCapGuardsReach {evm : State} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw first params id cap last : UInt256}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 7 ≤ 1024)
    (hlast : lastUpdateValue (memLoad first mem) = last)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 ⟨9144⟩
      ([first, UInt256.ofNat (2 ^ 128 - 1), cap, params, id] ++ R)
      mem aw out evm.accountMap k C) :
    (¬ submitCapGuardsAllowed evm id cap last ∧ RDrev (deployedRuntime v) g s0) ∨
    (submitCapGuardsAllowed evm id cap last ∧ ∃ aw' k' C',
      RD (deployedRuntime v) evm.executionEnv g s0 ⟨9222⟩
        (marketRemovalCap evm id :: cap :: params :: id :: R)
        (submitCapGuardMemory mem id) aw' out evm.accountMap k' C') := by
  have hh (m : ByteArray) (base : UInt256) :
      keccakWord ⟨0⟩ (UInt256.ofNat 64)
        (base.toByteArray.write 0 (id.toByteArray.write 0 m (⟨0⟩ : UInt256).toNat 32)
          (UInt256.ofNat 32).toNat 32) =
          solcMappingSlot base id := twoWordHashMem_solcMappingSlot_any _ _ _
  have hmask : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 184))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 184 - 1) := by decide +kernel
  by_cases hn : last ≠ ⟨0⟩
  case neg =>
    have rbad := metaMorphoV1_1_block_9144_taken (immWords := wordsOf (immStore v))
      (by change R.length + 3 + 2 ≤ 1024; omega)
      (by change UInt256.isZero (lastUpdateValue (memLoad first mem)) ≠ ⟨0⟩
          rw [hlast, not_ne_iff.mp hn]; decide)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
    exact .inl ⟨fun h ↦ hn h.1,
      metaMorphoV1_1_block_9404 (immWords := wordsOf (immStore v))
        (by change R.length + 3 + 2 ≤ 1024; omega) rbad⟩
  obtain ⟨aw0, k0, C0, r0⟩ := metaMorphoV1_1_block_9144_fallthrough_packed
    (immWords := wordsOf (immStore v)) (by change R.length + 3 + 2 ≤ 1024; omega)
    (by change UInt256.isZero (lastUpdateValue (memLoad first mem)) = ⟨0⟩
        rw [hlast]; exact isZero_eq_zero_of_ne hn) rd
  change RD (deployedRuntime v) evm.executionEnv g s0 ⟨9152⟩ (cap :: params :: id :: R)
    mem aw0 out evm.accountMap k0 C0 at r0
  by_cases hp : marketRemovalPendingAt evm id = ⟨0⟩
  case neg =>
    obtain ⟨aw1, k1, C1, rbad⟩ := metaMorphoV1_1_block_9152_taken_packed
      (immWords := wordsOf (immStore v)) (by omega) (by rw [hh]; exact hp)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r0
    exact .inl ⟨fun h ↦ hp h.2.1,
      metaMorphoV1_1_block_4572 (immWords := wordsOf (immStore v))
        (by change R.length + 3 + 2 ≤ 1024; omega) rbad⟩
  obtain ⟨aw1, k1, C1, r1⟩ := metaMorphoV1_1_block_9152_fallthrough_packed
    (immWords := wordsOf (immStore v)) (by omega) (by rw [hh]; exact hp) r0
  change RD (deployedRuntime v) evm.executionEnv g s0 ⟨9172⟩ (cap :: params :: id :: R)
    (twoWordHashMem id ⟨16⟩ mem) aw1 out evm.accountMap k1 C1 at r1
  by_cases hr : marketRemovalRemovableAt evm id = ⟨0⟩
  case neg =>
    obtain ⟨aw2, k2, C2, rbad⟩ := metaMorphoV1_1_block_9172_taken_packed
      (immWords := wordsOf (immStore v)) (by omega) (by rw [hh]; exact hr)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r1
    exact .inl ⟨fun h ↦ hr h.2.2.1,
      metaMorphoV1_1_block_9389 (immWords := wordsOf (immStore v))
        (by change R.length + 3 + 2 ≤ 1024; omega) rbad⟩
  obtain ⟨aw2, k2, C2, r2⟩ := metaMorphoV1_1_block_9172_fallthrough_packed
    (immWords := wordsOf (immStore v)) (by omega) (by rw [hh]; exact hr) r1
  change RD (deployedRuntime v) evm.executionEnv g s0 ⟨9192⟩ (cap :: params :: id :: R)
    (twoWordHashMem id ⟨13⟩ (twoWordHashMem id ⟨16⟩ mem)) aw2 out evm.accountMap k2 C2 at r2
  by_cases hc : cap ≠ marketRemovalCap evm id
  case neg =>
    have heq := (not_ne_iff.mp hc).symm
    obtain ⟨aw3, k3, C3, rbad⟩ := metaMorphoV1_1_block_9192_taken_packed
      (immWords := wordsOf (immStore v)) hstack
      (by rw [hh, hmask, u256_land_comm]
          change UInt256.eq (marketRemovalCap evm id) cap ≠ ⟨0⟩
          rw [heq]; simp only [UInt256.eq]; decide)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r2
    exact .inl ⟨fun h ↦ hc h.2.2.2,
      metaMorphoV1_1_block_1143 (immWords := wordsOf (immStore v))
        (by change R.length + 4 + 2 ≤ 1024; omega) rbad⟩
  obtain ⟨aw3, k3, C3, r3⟩ := metaMorphoV1_1_block_9192_fallthrough_packed
    (immWords := wordsOf (immStore v)) hstack
    (by rw [hh, hmask, u256_land_comm]; exact u256_eq_of_ne (Ne.symm hc)) r2
  refine .inr ⟨⟨hn, hp, hr, hc⟩, aw3, k3, C3, ?_⟩
  simp only [metaMorphoV1_1_block_9192_fallthrough_stack, hh, hmask] at r3
  rw [u256_land_comm] at r3
  exact r3

end Benchmarks.Morpho.MetaMorphoV1_1
