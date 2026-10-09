import Benchmarks.Morpho.MetaMorphoV1_1.MappingStorage
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_009
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_057

/-! Shared storage-array addressing routines and the full-word getter return. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode

-- LIBRARY CANDIDATE: normalize the hash used as a dynamic storage array's data base.
theorem arrayScratchHash (slot : UInt256) (mem : ByteArray) :
    keccakWord ⟨0⟩ ⟨32⟩ (wordAt0Mem slot mem) =
      uInt256OfByteArray (KEC slot.toByteArray) := by
  exact (wordAt0Mem_keccak_word slot mem).trans (uInt256OfByteArray_eq _).symm

-- LIBRARY CANDIDATE: shifting a word right by zero preserves it.
theorem wordShiftRight_zero (w : UInt256) : UInt256.shiftRight w ⟨0⟩ = w := by
  apply u256_inj
  simpa only [Nat.pow_zero, Nat.div_one] using wordShiftRight_toNat w 0 (by decide)

set_option maxRecDepth 2000 in
theorem supplyQueueIndex {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {i ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 4 ≤ 1024)
    (hbound : i.toNat < (codeOwnerStorageWord I σ ⟨20⟩).toNat)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨11535⟩ (i :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ret
      (⟨0⟩ :: (uInt256OfByteArray (KEC (UInt256.toByteArray ⟨20⟩)) + i) :: R)
      (wordAt0Mem ⟨20⟩ mem) (M (M aw ⟨0⟩ ⟨32⟩) ⟨0⟩ ⟨32⟩) rdata σ k' C' := by
  obtain ⟨_, _, rd11546⟩ := metaMorphoV1_1Blocks.metaMorphoV1_1_block_11535_fallthrough
    (immWords := wordsOf (immStore v)) (by simpa using hstack)
    (by
      change UInt256.isZero (UInt256.lt i (codeOwnerStorageWord I σ ⟨20⟩)) = ⟨0⟩
      rw [ult_one hbound]
      decide) rd
  have hret := metaMorphoV1_1Blocks.metaMorphoV1_1_block_11546
    (immWords := wordsOf (immStore v)) hstack hvalid rd11546
  change RD (deployedRuntime v) I g s0 ret
    (⟨0⟩ :: (keccakWord ⟨0⟩ ⟨32⟩ (wordAt0Mem ⟨20⟩ mem) + i) :: R)
    (wordAt0Mem ⟨20⟩ mem) (M (M aw ⟨0⟩ ⟨32⟩) ⟨0⟩ ⟨32⟩) rdata σ _ _ at hret
  rw [arrayScratchHash] at hret
  exact ⟨_, _, hret⟩

set_option maxRecDepth 2000 in
theorem withdrawQueueIndex {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {i ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 4 ≤ 1024)
    (hbound : i.toNat < (codeOwnerStorageWord I σ ⟨21⟩).toNat)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨11491⟩ (i :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ret
      (⟨0⟩ :: (uInt256OfByteArray (KEC (UInt256.toByteArray ⟨21⟩)) + i) :: R)
      (wordAt0Mem ⟨21⟩ mem) (M (M aw ⟨0⟩ ⟨32⟩) ⟨0⟩ ⟨32⟩) rdata σ k' C' := by
  obtain ⟨_, _, rd11502⟩ := metaMorphoV1_1Blocks.metaMorphoV1_1_block_11491_fallthrough
    (immWords := wordsOf (immStore v)) (by simpa using hstack)
    (by
      change UInt256.isZero (UInt256.lt i (codeOwnerStorageWord I σ ⟨21⟩)) = ⟨0⟩
      rw [ult_one hbound]
      decide) rd
  have hret := metaMorphoV1_1Blocks.metaMorphoV1_1_block_11502
    (immWords := wordsOf (immStore v)) hstack hvalid rd11502
  change RD (deployedRuntime v) I g s0 ret
    (⟨0⟩ :: (keccakWord ⟨0⟩ ⟨32⟩ (wordAt0Mem ⟨21⟩ mem) + i) :: R)
    (wordAt0Mem ⟨21⟩ mem) (M (M aw ⟨0⟩ ⟨32⟩) ⟨0⟩ ⟨32⟩) rdata σ _ _ at hret
  rw [arrayScratchHash] at hret
  exact ⟨_, _, hret⟩

set_option maxRecDepth 2000 in
theorem arrayGetterReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {slot : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 4 ≤ 1024)
    (hsize : mem.size = 96)
    (hread : mem.readWithPadding 64 32 = (⟨128⟩ : UInt256).toByteArray)
    (rd : RD (deployedRuntime v) I g s0 ⟨902⟩ (⟨0⟩ :: slot :: ⟨32⟩ :: R)
      mem aw rdata σ k C) :
    RDret (deployedRuntime v) g s0 σ (codeOwnerStorageWord I σ slot).toByteArray := by
  have hret := metaMorphoV1_1Blocks.metaMorphoV1_1_block_902
    (immWords := wordsOf (immStore v)) hstack rd
  have hbytes := returnScratchWordMemory mem (codeOwnerStorageWord I σ slot) hsize hread
  have hshift := wordShiftRight_zero (codeOwnerStorageWord I σ slot)
  exact hbytes ▸ (hshift ▸ hret)

end Benchmarks.Morpho.MetaMorphoV1_1
