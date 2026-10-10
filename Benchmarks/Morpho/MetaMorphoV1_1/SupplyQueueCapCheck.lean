import Benchmarks.Morpho.MetaMorphoV1_1.SupplyQueueSyntax
import Benchmarks.Morpho.MetaMorphoV1_1.SupplyQueueRole
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_050
import Benchmarks.Morpho.MetaMorphoV1_1.CalldataArrayIndexRuntime

/-! Calldata indexing and the runtime capacity guard for a replacement supply queue. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

open SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

theorem supplyQueueCapCheck {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {start len i : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 8 ≤ 1024)
    (hi : i.toNat < len.toNat)
    (rd : RD (deployedRuntime v) I g s0 ⟨10307⟩
      ([i, len, start] ++ R) mem aw out σ k C) :
    let id := calldataWord I.calldata (UInt256.shiftLeft i ⟨5⟩ + start).toNat
    (maxDepositCapWord I σ id = ⟨0⟩ ∧ RDrev (deployedRuntime v) g s0) ∨
    (maxDepositCapWord I σ id ≠ ⟨0⟩ ∧ ∃ aw' k' C',
      RD (deployedRuntime v) I g s0 ⟨10348⟩ ([i, len, start] ++ R)
        (twoWordHashMem id ⟨13⟩ mem) aw' out σ k' C') := by
  dsimp only
  let id := calldataWord I.calldata (UInt256.shiftLeft i ⟨5⟩ + start).toNat
  have h1 := metaMorphoV1_1_block_10307 (immWords := wordsOf (immStore v)) hstack
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  obtain ⟨k2, C2, h2⟩ := calldataArrayIndex v
    (by simp only [List.length_cons]; omega) hi
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h1
  have hh : keccakWord ⟨0⟩ (UInt256.ofNat 64) (twoWordHashMem id ⟨13⟩ mem) =
      solcMappingSlot ⟨13⟩ id := twoWordHashMem_solcMappingSlot_any _ _ _
  have hm : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 184))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 184 - 1) := rfl
  by_cases hz : maxDepositCapWord I σ id = ⟨0⟩
  · obtain ⟨aw3, k3, C3, h3⟩ := metaMorphoV1_1_block_10318_taken_packed
      (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega)
      (by
        change UInt256.isZero (UInt256.land _
          (codeOwnerStorageWord I σ (keccakWord ⟨0⟩ (UInt256.ofNat 64)
            (twoWordHashMem id ⟨13⟩ mem)))) ≠ UInt256.ofNat 0
        rw [hh, hm, u256_land_comm]
        change UInt256.isZero (maxDepositCapWord I σ id) ≠ UInt256.ofNat 0
        rw [hz]; decide)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2
    have h4 := metaMorphoV1_1_block_10355 (immWords := wordsOf (immStore v))
      (by omega) (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h3
    obtain ⟨k5, C5, h5⟩ := calldataArrayIndex v (by omega) hi
      (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h4
    exact .inl ⟨hz, metaMorphoV1_1_block_10365 (immWords := wordsOf (immStore v))
      (by omega) h5⟩
  · obtain ⟨aw3, k3, C3, h3⟩ := metaMorphoV1_1_block_10318_fallthrough_packed
      (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega)
      (by
        change UInt256.isZero (UInt256.land _
          (codeOwnerStorageWord I σ (keccakWord ⟨0⟩ (UInt256.ofNat 64)
            (twoWordHashMem id ⟨13⟩ mem)))) = UInt256.ofNat 0
        rw [hh, hm, u256_land_comm]
        exact isZero_eq_zero_of_ne hz) h2
    exact .inr ⟨hz, aw3, k3, C3, h3⟩

end Benchmarks.Morpho.MetaMorphoV1_1
