import Benchmarks.Morpho.MetaMorphoV1_1.CuratorRoleSource
import Benchmarks.Morpho.MetaMorphoV1_1.RevocationRole
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_029
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_044
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_045
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_046

/-! Curator and owner authorization in cap submission. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

theorem submitCapRoleReach {evm : State} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw params : UInt256} {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 6 ≤ 1024)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 ⟨8890⟩ (params :: R)
      mem aw out evm.accountMap k C) :
    (¬ curatorRoleAllowed evm ∧ RDrev (deployedRuntime v) g s0) ∨
    (curatorRoleAllowed evm ∧ ∃ k' C',
      RD (deployedRuntime v) evm.executionEnv g s0 ⟨8919⟩
        (params :: calldataWord evm.executionEnv.calldata 164 :: R)
        mem aw out evm.accountMap k' C') := by
  have hjoin : ∃ flag k' C',
      (flag = ⟨0⟩ ↔ curatorRoleAllowed evm) ∧
      RD (deployedRuntime v) evm.executionEnv g s0 ⟨8914⟩
        (flag :: params :: calldataWord evm.executionEnv.calldata 164 :: R)
        mem aw out evm.accountMap k' C' := by
    by_cases hc : curatorAddress evm = evm.executionEnv.source
    · have hz := storedRoleMismatch_match evm.executionEnv evm.accountMap ⟨10⟩ hc
      obtain ⟨k1, C1, r1⟩ := metaMorphoV1_1_block_8890_fallthrough
        (immWords := wordsOf (immStore v)) (by omega)
        (by simpa only [storedRoleMismatch, u256_land_comm] using hz) rd
      refine ⟨⟨0⟩, k1, C1, ⟨fun _ ↦ Or.inl hc, fun _ ↦ rfl⟩, ?_⟩
      simp only [metaMorphoV1_1_block_8890_fallthrough_stack, u256_land_comm] at r1
      change RD (deployedRuntime v) evm.executionEnv g s0 ⟨8914⟩
        (storedRoleMismatch evm.executionEnv evm.accountMap ⟨10⟩ :: params ::
          calldataWord evm.executionEnv.calldata 164 :: R) mem aw out evm.accountMap k1 C1
        at r1
      rwa [hz] at r1
    · have hn := storedRoleMismatch_ne evm.executionEnv evm.accountMap ⟨10⟩ hc
      obtain ⟨k1, C1, r1⟩ := metaMorphoV1_1_block_8890_taken
        (immWords := wordsOf (immStore v)) (by omega)
        (by simpa only [storedRoleMismatch, u256_land_comm] using hn)
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
      obtain ⟨k2, C2, r2⟩ := metaMorphoV1_1_block_9492
        (immWords := wordsOf (immStore v))
        (by change R.length + 2 + 4 ≤ 1024; omega)
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r1
      refine ⟨storedRoleMismatch evm.executionEnv evm.accountMap ⟨8⟩, k2, C2, ?_, r2⟩
      constructor
      · intro hz
        by_cases ho : ownerAddress evm = evm.executionEnv.source
        · exact Or.inr ho
        · exact False.elim
            (storedRoleMismatch_ne evm.executionEnv evm.accountMap ⟨8⟩ ho hz)
      · intro ha
        exact storedRoleMismatch_match evm.executionEnv evm.accountMap ⟨8⟩
          (ha.resolve_left hc)
  obtain ⟨flag, k1, C1, hflag, r1⟩ := hjoin
  by_cases hz : flag = ⟨0⟩
  · exact .inr ⟨hflag.mp hz, _, _, metaMorphoV1_1_block_8914_fallthrough
      (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) hz r1⟩
  · have r2 := metaMorphoV1_1_block_8914_taken (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) hz
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r1
    exact .inl ⟨fun ha ↦ hz (hflag.mpr ha),
      metaMorphoV1_1_block_5503 (immWords := wordsOf (immStore v))
        (by change R.length + 2 + 2 ≤ 1024; omega) r2⟩

end Benchmarks.Morpho.MetaMorphoV1_1
