import Benchmarks.Morpho.MetaMorphoV1_1.BalanceInternalSource
import Benchmarks.EAS.Attester.Memory
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_072

/-! The owner's balance lookup between fee accrual and asset conversion. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

theorem maxWithdrawBalanceMemory_free (owner : AccountAddress) {mem : ByteArray}
    (hm : 96 ≤ mem.size) :
    memLoad ⟨64⟩ (twoWordHashMem (UInt256.ofNat owner.toNat) ⟨0⟩ mem) = memLoad ⟨64⟩ mem := by
  change memLoad ⟨64⟩ (writeWord (writeWord mem 0 (UInt256.ofNat owner.toNat)) 32 ⟨0⟩) = _
  rw [Reasoning.Theory.writeWord, memLoad_write_disjoint _ 32 ⟨64⟩ ⟨0⟩
    (by change 96 ≤ _; rw [writeWord_sparse_size]; omega) (.inr (by decide))]
  rw [Reasoning.Theory.writeWord, memLoad_write_disjoint mem 0 ⟨64⟩ _ hm (.inr (by decide))]

theorem maxWithdrawBalanceMemory_size (owner : AccountAddress) {mem : ByteArray}
    (hm : 96 ≤ mem.size) :
    (twoWordHashMem (UInt256.ofNat owner.toNat) ⟨0⟩ mem).size = mem.size :=
  twoWordHashMem_size_of_ge_64' _ _ (by omega)

set_option maxRecDepth 2000 in
theorem maxWithdrawReadBalance {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {supply total ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (owner : AccountAddress) (hstack : R.length + 7 ≤ 1024)
    (rd : RD (deployedRuntime v) I g s0 ⟨15909⟩
      (supply :: total :: ret :: UInt256.ofNat owner.toNat :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨15343⟩
      (codeOwnerStorageWord I σ (solcMappingSlot ⟨0⟩ (UInt256.ofNat owner.toNat)) ::
        supply :: total :: ret :: supply :: R)
      (twoWordHashMem (UInt256.ofNat owner.toNat) ⟨0⟩ mem) aw' rdata σ k' C' := by
  have hm : UInt256.land
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1)) (UInt256.ofNat owner.toNat) = UInt256.ofNat owner.toNat :=
    solcAddrMask_clean_left (addressWord_val_canonical owner)
  have hh : keccakWord ⟨0⟩ ⟨64⟩ (twoWordHashMem (UInt256.ofNat owner.toNat) ⟨0⟩ mem) =
      solcMappingSlot ⟨0⟩ (UInt256.ofNat owner.toNat) :=
    twoWordHashMem_solcMappingSlot_any _ _ _
  obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_15909_packed
    (immWords := wordsOf (immStore v)) hstack
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  simp only [metaMorphoV1_1_block_15909_stack, metaMorphoV1_1_block_15909_memory, hm] at h1
  change RD (deployedRuntime v) I g s0 ⟨15343⟩
    (codeOwnerStorageWord I σ
      (keccakWord ⟨0⟩ ⟨64⟩ (twoWordHashMem (UInt256.ofNat owner.toNat) ⟨0⟩ mem)) ::
        supply :: total :: ret :: supply :: R)
    (twoWordHashMem (UInt256.ofNat owner.toNat) ⟨0⟩ mem) aw1 rdata σ k1 C1 at h1
  rw [hh] at h1
  exact ⟨aw1, k1, C1, h1⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
